import EggTactic.Sexp
import EggTactic.Tracing
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
import Lean.Data.Json
import Lean.Elab.Deriving.FromToJson

open Lean Elab Meta Tactic Term
open IO
open System

--initialize registerTraceClass `EggTactic.egg

-- Path to the egg server.
def egg_server_path : String :=
  "utils/egg-herbie"

inductive EggRewriteDirection where
  | Forward
  | Backward
  deriving Inhabited, DecidableEq

def EggRewriteDirection.toString : EggRewriteDirection → String
  | Forward => "fwd"
  | Backward => "bwd"

instance : ToString EggRewriteDirection where toString := EggRewriteDirection.toString

open EggRewriteDirection

structure EggRewrite where
  name: String
  lhs: Sexp
  rhs: Sexp
  -- TODO: see if converting to FVars makes it better
  pretendMVars: Array MVarId -- list of pretend mvars needed by this rewrite
                      --  Why do we need this again?
  rw: Expr -- the rewrite with fvars applied
  unappliedRw: Expr -- the rewrite without fvars applied
  rwType: Expr
  unappliedRwType: Expr
  direction : EggRewriteDirection

instance : Inhabited EggRewrite where
  default := EggRewrite.mk
         "default" "default" "default" #[] default default default default default

structure Eggxplanation where
  direction: EggRewriteDirection -- direction of the rewrite
  rule: String -- name of the rewrite rule
  result: Expr -- result of the rewrite
  source: Expr -- source of the rewrite
  position : Nat
  mvars: List (Sexp × Expr) -- metavariables in the rewrite rule and its assignment

instance : ToString Eggxplanation where
  toString expl :=
    let mvars := expl.mvars.map (fun (mvar, expr) => s!"{mvar} := {expr}")
    let mvars := "{" ++ (", ".intercalate mvars) ++ "}"
    toString f!"(Eggxplanation dir:{expl.direction} rule:{expl.rule} mvars:{mvars} result:{expl.result})"



def nameToSexp: Name -> Sexp
| Name.anonymous => "anonymous"
| Name.str n s => Sexp.fromList ["str", nameToSexp n, s]
| Name.num n i => Sexp.fromList ["num", nameToSexp n, (toString i)]

-- | TODO: cleanup error handling
def parseNameSexpr (sexpr: Sexp) : MetaM Name := do
  match sexpr with
  | Sexp.atom "anonymous" => return Name.anonymous
  | Sexp.list [Sexp.atom "str", n, Sexp.atom s] =>
    return Name.mkStr (← parseNameSexpr n) s
  | Sexp.list [Sexp.atom "num", n, Sexp.atom s] =>
    return Name.mkNum (← parseNameSexpr n) (s.toNat!)
  | _ => throwError s!"unexpected sexpr {sexpr}"



def levelToSexp: Level → Sexp
| Level.zero => "zero"
| Level.succ l => Sexp.fromList ["succ", levelToSexp l]
| Level.max l₁ l₂ => Sexp.fromList ["max", levelToSexp l₁, levelToSexp l₂]
| Level.imax l₁ l₂ => Sexp.fromList ["imax", levelToSexp l₁, levelToSexp l₂]
| Level.param n => Sexp.fromList ["param", nameToSexp n]
| Level.mvar n => Sexp.fromList ["mvar", nameToSexp n.name]

def parseLevelSexpr (s: Sexp): MetaM Level := do
  match s with
  | Sexp.atom "zero" => return Level.zero
  | Sexp.list [Sexp.atom "succ", l] =>  return Level.succ (← parseLevelSexpr l)
  | Sexp.list [Sexp.atom "max", l₁, l₂] => return Level.max (← parseLevelSexpr l₁) (← parseLevelSexpr l₂)
  | Sexp.list [Sexp.atom "imax", l₁, l₂] => return Level.imax (← parseLevelSexpr l₁) (← parseLevelSexpr l₂)
  | Sexp.list [Sexp.atom "param", n] => return Level.param (← parseNameSexpr n)
  | Sexp.list [Sexp.atom "mvar", n] => return Level.mvar (LevelMVarId.mk (← parseNameSexpr n))
  | _ => throwError s!"unexpected level sexpr: {s}"



mutual
-- TODO: see if there is some other way to give mvars in a structured way instead of string
-- I really want to be able to give the full Name.
partial def mvarIdToSexp (m:MVarId): Sexp :=  Sexp.atom ("?" ++ toString m.name)

/-
convert this expression into a string, along with the names of the
bound variables.
-/
partial def exprToUntypedSexp (e: Expr): MetaM Sexp :=
match e with
  | Expr.const name [] => return .fromList ["const", nameToSexp name, "nolevels"]
  | Expr.const name levels => return .fromList ["const", nameToSexp name, .fromList ["levels", (levels.map levelToSexp)]]
  | Expr.bvar ix => return .fromList ["bbar", toString ix]
  | Expr.fvar id => return .fromList ["fvar", nameToSexp id.name]
  -- TODO: see if there is some other way to give mvars in a structured way instead of string
  | Expr.mvar id => do
     return (mvarIdToSexp id)
  | Expr.lit (.natVal n)=> return .fromList ["litNat", toString n]
  | Expr.forallE _binderName _binderType body _binderInfo => return .fromList ["forall", <- exprToUntypedSexp body]
  | Expr.app  l r => do
     return (.fromList ["ap", (← exprToUntypedSexp l), (← exprToUntypedSexp r)])
  | Expr.sort lvl => return (.fromList ["sort", levelToSexp lvl])
  | _ => throwError s!"unimplemented exprToUntypedSexp ({e.ctorName}): {e}"
end

partial def exprToTypedSexp (e: Expr): MetaM Sexp := do
 let sexp <- match e with
  | Expr.const name [] => pure $  .fromList ["const", nameToSexp name, "nolevels"]
  | Expr.const name levels => pure $  .fromList ["const", nameToSexp name, .fromList ["levels", (levels.map levelToSexp)]]
  | Expr.bvar ix => throwError s!"expected no bound variables, we use locally nameless!, but found bvar '{ix}'"
  | Expr.fvar id => pure $  .fromList ["fvar", nameToSexp id.name]
  -- TODO: see if there is some other way to give mvars in a structured way instead of string
  | Expr.mvar id => do
     -- let ty ← inferType e
     -- pure $   .fromList ["mvar", mvarIdToSexp id, (<- exprToSexp ty)]
     pure $  (mvarIdToSexp id)
  | Expr.lit (.natVal n)=> pure $  .fromList ["litNat", toString n]
  | Expr.app  l r => do
     pure $  (.fromList ["ap", (← exprToTypedSexp l), (← exprToTypedSexp r)])
  | _ => throwError s!"unimplemented expr_to_string ({e.ctorName}): {e}"
 let t ← inferType e
 return .fromList ["typed-expr", sexp, <- exprToUntypedSexp t]



partial def parseExprSexpr (s: Sexp): MetaM Expr := do
  match s with
  | Sexp.list [Sexp.atom "typed-expr", expr, _ty] => parseExprSexpr expr
  -- TODO: teach `egg` that empty sexp is okay
  | Sexp.list [Sexp.atom "const", name, Sexp.atom "nolevels"] => do
    return (Expr.const (← parseNameSexpr name) [])
    -- TODO: teach `egg` to not convert `(list (atom level))` to `(atom level)`
  | Sexp.list [Sexp.atom "const", name, Sexp.list [Sexp.atom "levels", Sexp.atom "zero"] ] => do
    return Expr.const (← parseNameSexpr name) [Level.zero]
  | Sexp.list [Sexp.atom "const", name, Sexp.list [Sexp.atom "levels", Sexp.list levels] ] => do
    let levels ← levels.mapM parseLevelSexpr
    return Expr.const (← parseNameSexpr name) levels
  | Sexp.list [Sexp.atom "fvar", n] => return mkFVar (FVarId.mk (← parseNameSexpr n))
  | Sexp.list [Sexp.atom "litNat", n] => return mkNatLit n.toAtom!.toNat!
  | Sexp.list [Sexp.atom "ap", l, r] => return mkApp (← parseExprSexpr l) (← parseExprSexpr r)
  | _ => throwError s!"unimplemented parseExprSexpr '{s}': {s}"


def exceptToMetaM [ToString ε]: Except ε α -> MetaM α :=
  fun e =>
    match e with
    | Except.error msg => throwError (toString msg)
    | Except.ok x => return x


-- | parse a fragment of an explanation into an EggRewrite
def parseExplanation (mapping : VariableMapping) (j: Json) : MetaM Eggxplanation := do
  let direction ← exceptToMetaM (← exceptToMetaM <| j.getObjVal? "direction").getStr?
  let direction <- match direction with
    | "fwd" => pure Forward
    | "bwd" => pure Backward
    | other => throwError (s!"unknown direction {other} in |{j}|")
  let rewrite ← exceptToMetaM (← exceptToMetaM <| j.getObjVal? "rewrite").getStr?
  let mvarsJson ← exceptToMetaM (← exceptToMetaM <| j.getObjVal? "mvars").getObj?
  let mvarid2expr ← mvarsJson.foldM (init := []) (fun out mvaridStr expr => do {
    let expr ← exceptToMetaM <| expr.getStr?
    let expr ← exceptToMetaM <| parseSingleSexp expr
    trace[EggTactic.egg] ("12.5.1) expr.currying....")
    let expr := expr.curry
    trace[EggTactic.egg] ("\t12.5.1) done!...")
    trace[EggTactic.egg] ("12.5.1) expr.unsimplifying....")
    let expr := expr.unsimplify mapping
    trace[EggTactic.egg] ("\t12.5.1) done!...")
    let expr ← parseExprSexpr $ expr
    let mvaridSexp ← exceptToMetaM <| parseSingleSexp mvaridStr
    return (mvaridSexp, expr) :: out
  })
  let result ← exceptToMetaM (← exceptToMetaM <| j.getObjVal? "result").getStr?
  let result ← exceptToMetaM <| (parseSingleSexp result)
  trace[EggTactic.egg] ("12.5.2) result.currying....")
  let result := result.curry
  trace[EggTactic.egg] ("\t12.5.2) done!...")
  trace[EggTactic.egg] ("\t12.5.2) result.unsimplifying....")
  let result := result.unsimplify mapping
  trace[EggTactic.egg] ("12.5.2) done!...")

  let result ← parseExprSexpr $ result

  let source ← exceptToMetaM (← exceptToMetaM <| j.getObjVal? "source").getStr?
  let source ← exceptToMetaM <| parseSingleSexp source
  trace[EggTactic.egg] ("12.5.3) source.currying....")
  let source := source.curry
  trace[EggTactic.egg] ("12.5.3) source.done....")
  trace[EggTactic.egg] ("12.5.3) source.unsimplify....")
  let source := source.unsimplify mapping
  trace[EggTactic.egg] ("12.5.3) source.done....")
  let source ← parseExprSexpr $ source

  let position ← exceptToMetaM (← exceptToMetaM <| j.getObjVal? "position").getNat?

  return { direction := direction
          , rule := rewrite -- TODO: make consistent in terminology
          , mvars := mvarid2expr
          , result := result
          , source := source
          , position := position
          : Eggxplanation }

-- | Actually do the IO. This incurs an `unsafe`.
unsafe def unsafePerformIO [Inhabited α] (io: IO α): α :=
  match unsafeIO io with
  | Except.ok a    =>  a
  | Except.error _ => panic! "expected io computation to never fail"

-- | Circumvent the `unsafe` by citing an `implementedBy` instance.
@[implemented_by unsafePerformIO]
def performIO [Inhabited α] (io: IO α): α := Inhabited.default


def surroundQuotes (s: String): String :=
 "\"" ++ s ++ "\""
def surround_escaped_quotes (s: String): String :=
 "\\\"" ++ s ++ "\\\""


def EggRewrite.toJson (rewr: EggRewrite) :=
  let eggLhs := if rewr.direction == Forward then rewr.lhs else rewr.rhs
  let eggRhs := if rewr.direction == Forward then rewr.rhs else rewr.lhs
  -- trace[EggTactic.egg] "sending rewrite {rewr.name} to egg with direction {rewr.direction}"
  "{"
    ++ surroundQuotes "name" ++ ":" ++ surroundQuotes rewr.name ++ ","
    ++ surroundQuotes "lhs" ++ ":" ++ surroundQuotes eggLhs.toString ++ ","
    ++ surroundQuotes "rhs" ++ ":" ++ surroundQuotes eggRhs.toString ++
  "}"
instance : ToString EggRewrite where
  toString rewr := rewr.toJson


structure EggRequest where
  targetLhs: String
  targetRhs: String
  varMapping : VariableMapping
  rewrites: List EggRewrite
  time : Nat
  dumpGraph : Bool

def EggRequest.toJson (e: EggRequest): String :=
  "{"
  ++ surroundQuotes "request"  ++  ":" ++ surroundQuotes "perform-rewrite" ++ ","
  ++ surroundQuotes "target-lhs"  ++  ":" ++ surroundQuotes (e.targetLhs) ++ ","
  ++ surroundQuotes "target-rhs"  ++  ":" ++ surroundQuotes (e.targetRhs) ++ ","
  ++ surroundQuotes "rewrites" ++ ":" ++ "[" ++ String.intercalate "," (e.rewrites.map EggRewrite.toJson) ++ "]" ++ ","
  ++ surroundQuotes "timeout" ++ ":" ++ toString e.time ++ ","
  ++ surroundQuotes "dump-graph" ++ ":" ++ toString e.dumpGraph
  ++ "}"

def Lean.Json.getStr! (j: Json): String :=
  match j with
  | Json.str a => a
  | _ => toString (f!"[ERROR: expected |{j}| to be a JSON string.]")

def Lean.Json.getArr! (j: Json): Array Json :=
  match j with
  | Json.arr a => a
  | _ => #[]

def Lean.List.contains [DecidableEq α] (as: List α) (needle: α): Bool :=
  as.any (. == needle)

def lean_list_get? (as: List α) (n: Nat): Option α :=
match n with
| 0 => match as with | .nil => none | .cons a _ => some a
| n + 1 => match as with | .nil => none |.cons _ as => lean_list_get? as n

def Lean.List.get? (as: List α) (n: Nat): Option α := lean_list_get? as n

structure EggConfig where
  explodeMVars : Bool := true
  twoSided : Bool := true
  dumpGraph : Bool := false
  simplifyExprs : Bool := false
  time : Nat := 25
  deriving Repr

instance : Inhabited EggConfig where default := { }

structure EggState where
  ix: Nat := 0
  name2expr: List (Int × Expr) := []
  rewrites: List EggRewrite := []
  config : EggConfig
  deriving Inhabited

abbrev EggM (α: Type) := StateT EggState TermElabM α

def EggM.getRewrites (egg: EggM Unit) (cfg := instInhabitedEggConfig.default) : TermElabM (List EggRewrite) := do
  let start : EggState := default
  pure (← egg.run {start with config := cfg}).snd.rewrites

-- Find expressions of a given type in the local context
def withExprsOfType (g: MVarId) (t : Expr) (f: Expr → EggM Unit): EggM Unit := do
   g.withContext do
    let lctx <- getLCtx
    for ldecl in lctx do
      let ldecl_type <- inferType ldecl.toExpr
      if (← isExprDefEq ldecl_type t) then f ldecl.toExpr

instance : ToString EggState where
  toString expl :=
    toString f!"[ix:{expl.ix}]"

-- | find an expression with the given index as needle.
def EggState.findExpr (state: EggState) (needle: Int): Option Expr :=
    let rec go (l: List (Int × Expr)): Option Expr :=
      match l with
      | [] => Option.none
      | ((ix, e)::xs) => if ix == needle then some e else go xs
    go state.name2expr


partial def addEggRewrite
  (rw: Expr)
  (unappliedRw: Expr)
  (ty: Expr)
  (unappliedRwType: Expr)
  (lhs: Sexp)
  (rhs: Sexp)
  (pretendMVars: Array MVarId)
  (direction : EggRewriteDirection)
  : EggM Unit := do
  let i := (← get).ix
  trace[EggTactic.egg] s!"addEggRewrite rw:{rw} ty:{ty} lhs:{lhs} rhs:{rhs} name:{i}"

  let egg_rewrite :=
    { name := toString i
    , lhs := lhs
    , rhs := rhs
    , rw := rw
    , unappliedRw := unappliedRw
    , rwType := ty
    , unappliedRwType := unappliedRwType
    , pretendMVars := pretendMVars
    , direction := direction
    : EggRewrite }
  modify (fun state => { state with ix := i + 1, name2expr := (i, rw) :: state.name2expr, rewrites := egg_rewrite :: state.rewrites })

def expr_get_forall_bound_vars: Expr -> List Name
| Expr.forallE name _ty body _ => name :: expr_get_forall_bound_vars body
| _ => []


def tacticGuard (shouldSucceed?: Bool) (err: MessageData): MetaM Unit :=
  if !shouldSucceed? then throwError err else pure ()

def Array.isSubsetOf [BEq α] (self: Array α) (other: Array α): Bool :=
  self.all (fun x => other.contains x)


-- verify that the expressoin is of the form
-- ∀ x₁, ∀ x₂, ∀ x₃, ... , f(x₁, x₂, ...) = g(x₁, x₂, ...)
-- This is well founded since we reduce on the body of the forall,
-- but lean cannot see this, and hence neds a `partial`.
partial def Lean.Expr.universallyQuantifiedEq? (e: Expr): Bool :=
  -- match e with
  -- | .forallE (body := body) .. =>
  if e.isEq then true
  else if e.isForall
  then e.getForallBody.universallyQuantifiedEq?
  else false



-- get all mvars in an expr
def Lean.Expr.getAppMVars (e: Expr) (arr: Array MVarId := #[]): Array MVarId :=
match e with
  | Expr.mvar id => arr.push id
  | Expr.app l r =>
     r.getAppMVars (l.getAppMVars arr)
  | _ => arr


def instantiateRewriteMVars
  (unappliedRw : Expr)
  (unappliedRwType : Expr)
  (direction : EggRewriteDirection)
  (opargs : Array (Option Expr))
  : MetaM (Expr × Expr) := do
    -- TODO: Is there a better way to instantiating universal quantifiers?
    let (ms, _binders, rwTypeAppliedToMVar) ← forallMetaTelescope unappliedRwType
    let mut args : Array Expr := #[]
    for (m, oparg) in ms.zip opargs do
      match oparg with
        | some arg =>
          trace[EggTactic.egg] "*** mvar {m} := {arg}"
          -- TODO: how about this one, is there a less cursed way here?
          let _ ← isDefEq m arg -- force unification
          args:= args.push arg
        | none => args:= args.push m

    -- resolve `MVar`s that were unified above in `rwTypeAppliedToMVar`
    let rwTy ← instantiateMVars rwTypeAppliedToMVar
    trace[EggTactic.egg] "***rwTy: {rwTy}"
    let rwTy ← match (← matchEq? rwTy) with
                | .some (_, source, target) =>
                    if direction == .Forward then
                      mkEq source target
                    else
                      mkEq target source
                | .none => throwError "unable to matchEq? {rwTy}"
    trace[EggTactic.egg] "***rwTy: {rwTy}"
    -- let (ms, binders, rwAppliedToMVar) ← forallMetaTelescope eggrw.unappliedRw
    -- for (m, arg) in ms.zip args do
    --   trace[EggTactic.egg] "*** mvar {m} := {arg}"
    --   let _ ← isDefEq m arg -- force unification
    -- let rw ← instantiateMVars rwAppliedToMVar
    let rw := unappliedRw
    trace[EggTactic.egg] "***rw: {rw}"
    trace[EggTactic.egg] "***applying args: {args}"
    let rw := mkAppN rw args
    trace[EggTactic.egg] "***rw: {rw}"
    -- TODO: just in case (quote bollu "it's spiritual; I ask god")
    let rw ← instantiateMVars rw
    trace[EggTactic.egg] "***rw: {rw}"
    let rw ← (if direction == EggRewriteDirection.Forward
             then pure rw
             else mkEqSymm rw)
    trace[EggTactic.egg] "***rw: {rw}"
    return (rw, rwTy)


/-
Create a regular equality of the form lhs = rhs
-/
def addBareEquality
  (rw: Expr)
  (rwUnapplied: Expr)
  (ty: Expr)
  (unappliedRwType: Expr)
  (mvars: Array MVarId)
  (direction : EggRewriteDirection)
  : EggM Unit := do
  trace[EggTactic.egg] "**adding bareEquality {rw} : {ty}"
  -- Check if the lhs has all the mvars of the rhs
  let (lhs, rhs)  ←
      match (← matchEq? ty) with
      | some (_, lhs, rhs) =>
          pure (lhs, rhs)
      | none => throwError f!"**expected type to be equality: {ty}"
  -- NOTE: egg can only handle rewrites where the value of metavars
  -- on the RHS is deduced from the LHS. Thus, we check that
  -- the metavars that occur on the RHS is a subset of the LHS, and
  -- we flip the equality in the symmetric case.
  let lhsVars := lhs.getAppMVars.filter mvars.contains
  let rhsVars := rhs.getAppMVars.filter mvars.contains
  if (rhsVars.isSubsetOf lhsVars
      && direction == Forward) ||
     (lhsVars.isSubsetOf rhsVars
      && direction == Backward) then
    addEggRewrite rw rwUnapplied
        ty unappliedRwType
        (← exprToUntypedSexp lhs)
        (← exprToUntypedSexp rhs) mvars direction
  else
    trace[EggTactic.egg] "ERROR: Trying to add equality where the mvars of the LHS ({lhs}) is not a subset of the mvars of the RHS ({rhs})"

/-
Create an equality with MVars
-/
def addForallMVarEquality (rw: Expr) (ty: Expr): EggM Unit := do

  tacticGuard ty.universallyQuantifiedEq? "**expected ∀ ... a = b**"
  trace[EggTactic.egg] "**adding forallMVarEquality {rw} : {ty}"
  let (ms, _binders, tyNoForall) ← forallMetaTelescope ty
  -- | code taken from Lean/Meta/Rewrite.lean by looking at `heq`.
  let (lhs, rhs)  ←
      match (← matchEq? tyNoForall) with
      | some (_, lhs, rhs) =>
          pure (lhs, rhs)
      | none => throwError f!"**expected type to be equality: {ty}"

  let rwApplied := mkAppN rw ms -- is this correct?
  let mvIds := ms.map Expr.mvarId!
  let lhsVars := lhs.getAppMVars.filter mvIds.contains
  let rhsVars := rhs.getAppMVars.filter mvIds.contains
  if rhsVars.isSubsetOf lhsVars then
    addBareEquality rwApplied rw  tyNoForall ty mvIds Forward
    unless (← get).config.twoSided do
      return ()
  if lhsVars.isSubsetOf rhsVars then
    addBareEquality rwApplied rw  tyNoForall ty mvIds Backward
  else if !(rhsVars.isSubsetOf lhsVars) then
    throwError "error adding {rw}, neither side's variables are a subset of the other: LHS : {lhs} ({lhsVars}), RHS: {rhs} ({rhsVars})"

--  explode an equality with ∀ by creating many variations, from the local context.
-- It is well founded because we destructure the inductive type, but lean is unable to
-- infer this
partial def addForallExplodedEquality_ (goal: MVarId)
  (rw: Expr) (rwUnapplied: Expr)
  (ty: Expr)
  (unappliedRwType: Expr)
  (toExplode : Array Bool)
  (mvars: Array MVarId)
  : EggM Unit := do
  tacticGuard ty.universallyQuantifiedEq? "**expected ∀ ... a = b**"
  if let Expr.forallE x xty body _ := ty then do {
  --trace[EggTactic.egg] "**forall is : (FA [{x} : {xty}] {body})"
   if toExplode.back then{
       withExprsOfType goal xty $ λ xval => do
          -- trace[EggTactic.egg] "**exploding {ty} @ {xval} : {← inferType xval }"
          -- addForallExplodedEquality_ goal rw (←  mkAppM' ty #[xval])
          -- We apply the value and pass it on recursively. This becomes the
          -- new "unapplied" type, as the applied argument is not going to
          -- be passed as an mvar anymore
            addForallExplodedEquality_ goal
                (Expr.beta rw #[xval])
                (Expr.beta rw #[xval])
                (← instantiateForall ty #[xval])
                (← instantiateForall ty #[xval])
                toExplode.pop mvars
   }
  -- TODO: if we're skipping, don't beta-reduce,
  -- convert to mvar instead and continue
  -- This doesn't seem to work as-is.
   else do {
      let m ← mkFreshExprMVar (type? := .some xty) (userName := x)
      addForallExplodedEquality_
        goal
        (Expr.beta rw #[m])
        (Expr.beta rw #[m])
        (← instantiateForall ty #[m])
        (← instantiateForall ty #[m])
        toExplode.pop (mvars.push m.mvarId!)
   }
 } else do {
   addBareEquality rw rwUnapplied ty unappliedRwType mvars Forward;
   addBareEquality rw rwUnapplied ty unappliedRwType mvars Backward;
 }


-- See `addForallExplodedEquality_`
def addForallExplodedEquality (goal: MVarId) (rw: Expr) (ty: Expr): EggM Unit := do
  tacticGuard ty.universallyQuantifiedEq? "**expected ∀ ... a = b**"
  trace[EggTactic.egg] "**adding forallExplodedEquality {rw} : {ty}"
  let (ms, _, tyeq) ← forallMetaTelescope ty
  let (lhs, rhs)  ←
      match (← matchEq? tyeq) with
      | some (_, lhs, rhs) =>
          pure (lhs, rhs)
      | none => throwError f!"**expected type to be equality: {ty}"
  let ms := ms.map Expr.mvarId!
  if lhs.getAppMVars.isSubsetOf rhs.getAppMVars then
    let toExplode := ms.map $ λ mv => !lhs.getAppMVars.contains mv && ms.contains mv
    -- we reverse toExplode so we can pop later
    addForallExplodedEquality_ goal rw rw ty ty toExplode.reverse (mvars := #[])
    unless (← get).config.twoSided do
      return ()
  if rhs.getAppMVars.isSubsetOf lhs.getAppMVars then
    let toExplode := ms.map $ λ mv => !rhs.getAppMVars.contains mv && ms.contains mv
    -- we reverse toExplode so we can pop later
    addForallExplodedEquality_ goal rw rw ty ty toExplode.reverse (mvars := #[])

-- Add an expression into the EggM context, if it is indeed a rewrite
def eggAddExprAsRewrite (goal: MVarId) (rw: Expr) (ty: Expr): EggM Unit := do
  if ty.universallyQuantifiedEq? then
    if ty.isForall then do
        -- TODO: add this only when metavars disallow to pass without
        if (← get).config.explodeMVars
          then addForallExplodedEquality goal rw ty
        addForallMVarEquality rw ty
    else if ty.isEq then do
        addBareEquality rw rw ty ty #[] Forward
  else if ty.isMVar then
    throwError "rw {rw} isMVar"
  else
    throwError "Unknown kind of rewrite {rw} : {ty}"


-- Add all equalities from the local context
def addAllLocalContextEqualities (goal: MVarId) (goals: List MVarId): EggM Unit :=
  goal.withContext do
    trace[EggTactic.egg] "goals: {goals.map fun g => g.name}"
    for decl in (← getLCtx) do
      if decl.toExpr.isMVar && goals.contains (decl.toExpr.mvarId!)
        then continue
      trace[EggTactic.egg] (s!"**processing local declaration {decl.userName}" ++
      s!":= {decl.toExpr} : {← inferType decl.toExpr}")
      -- TODO: call the correct API to resolve metavariables
      -- to enable local declarations such as 'have gh := group_inv h'
      -- eggAddExprAsRewrite goal (<- reduce decl.toExpr) (<- reduce (← inferType decl.toExpr))
      eggAddExprAsRewrite goal decl.toExpr (← inferType decl.toExpr)


-- Do the dirty work of sending a string, and reading the string out from stdout
def runEggRequestRaw (requestJson: String): MetaM String := do
    trace[EggTactic.egg] "sending request:\n{requestJson}"
    let eggProcess <- IO.Process.spawn
      { cmd := egg_server_path,
        -- stdin := IO.Process.Stdio.piped,
        stdout := IO.Process.Stdio.piped,
        stdin := IO.Process.Stdio.piped,
        -- stdout := IO.Process.Stdio.null,
        stderr := IO.Process.Stdio.null
      }
    FS.writeFile s!"/tmp/egg.json" requestJson
    trace[EggTactic.egg] "3) Spanwed egg server process. Writing stdin..."
    let (stdin, eggProcess) ← eggProcess.takeStdin
    stdin.putStr requestJson
    trace[EggTactic.egg] "5) Wrote stdin. Setting up stdout..."
    let stdout ← IO.asTask eggProcess.stdout.readToEnd Task.Priority.dedicated
    trace[EggTactic.egg] "6) Setup stdout. Waiting for exitCode..."
    let exitCode : UInt32 <- eggProcess.wait
    trace[EggTactic.egg] "7) got exitCode ({exitCode}). Waiting for stdout..."
    let stdout : String <- IO.ofExcept stdout.get
    -- trace[EggTactic.egg] "8) read stdout."
    -- let stdout : String := "STDOUT"
    trace[EggTactic.egg] ("9)stdout:\n" ++ stdout)
    return stdout


def Eggxplanation.instantiateEqType
  (expl: Eggxplanation)
  (eggrw: EggRewrite): MetaM (Expr × Expr) := do
    let eq ← match expl.direction with
        | .Forward =>  mkEq expl.source expl.result
        | .Backward =>  mkEq expl.result expl.source
    trace[EggTactic.egg] "*** eq                       : {eq}"
    let mut args : Array (Option Expr) := #[]
    -- We assume all mvars are used and they are in the right order here
    for mvar in eggrw.pretendMVars do
      match expl.mvars.lookup (mvarIdToSexp mvar) with
      | .some val =>
          args := args.push (some val)
      | .none => throwError "unable to find value for mvar: {mvar}"
    instantiateRewriteMVars eggrw.unappliedRw eggrw.unappliedRwType expl.direction args

def simplifyRequest (lhs rhs : Sexp) (rewrites : List EggRewrite)
  : Sexp × Sexp × List EggRewrite × VariableMapping :=
  let rewriteSexps := List.join $  rewrites.map  λ rw => [rw.lhs,rw.rhs]
  let (substituted, mapping) := simplifySexps $
    lhs :: rhs :: rewriteSexps
  let uncurried := substituted.map Sexp.uncurry
  Id.run do
    let mut resRewrites := []
    let mut remaining := uncurried.tail!.tail!
    for rw in rewrites do
      if let lhs::rhs::remaining' := remaining then
        resRewrites := resRewrites ++
          [{ name := rw.name, lhs := lhs, rhs := rhs,
             pretendMVars := rw.pretendMVars, rw := rw.rw,
             unappliedRw := rw.unappliedRw, rwType := rw.rwType,
             unappliedRwType := rw.unappliedRwType, direction := rw.direction
             : EggRewrite}]
        remaining := remaining'
      else
        panic! "error unpacking rewrites"
    return (uncurried.head!, uncurried.tail!.head!,resRewrites,mapping)

-- parse the response, given the response as a string
def parseEggResponse (goal: MVarId) (varMapping : VariableMapping) (responseString: String) :
  MetaM (List Eggxplanation) := do
    let outJson : Json <- match Json.parse responseString with
      | Except.error e => throwTacticEx `egg goal e
      | Except.ok j => pure j
    trace[EggTactic.egg] ("10)stdout as json:\n" ++ (toString outJson))
    let responseType := (outJson.getObjValD "response").getStr!
    trace[EggTactic.egg] ("11)stdout response: |" ++ responseType ++ "|")
    if responseType == "error"
    then throwTacticEx `egg goal (toString outJson)
    else
      trace[EggTactic.egg] "12) Creating explanation..."
      -- This whole thing is in an Except beacause everything in Json
      -- is written relative to Except, and not a general MonadError :(
      -- extract explanation field from response
      let explanation <- exceptToMetaM (outJson.getObjVal? "explanation")
      -- cast field to array
      let explanation <- exceptToMetaM <| Json.getArr? explanation
      -- map over each element into an explanation
      let explanation <- explanation.mapM (parseExplanation varMapping)
      let explanation := explanation.toList
      trace[EggTactic.egg] ("13) explanation: |" ++ String.intercalate " ;;; " (explanation.map ToString.toString) ++ "|")
      return explanation

-- High level wrapped aroung runEggRequestRaw that is well-typed, and returns the
-- list of explanations
def runEggRequest (goal: MVarId) (request: EggRequest): MetaM (List Eggxplanation) :=
  runEggRequestRaw request.toJson >>= (parseEggResponse goal request.varMapping)

-- Add rewrites with known names 'rewriteNames' from the local context of 'goalMVar'
def addNamedRewrites (goalMVar: MVarId)  (rewriteNames: List Ident): EggM Unit :=
  goalMVar.withContext do
    trace[EggTactic.egg] " addNamedRewrites {goalMVar.name} {rewriteNames.map ToString.toString}"
    let mut rewrites := rewriteNames.map (·.getId)
    for decl in (← getLCtx) do
    -- TODO: find a way to not have to use strings, see how 'simp' does this.
      if !((rewrites.map fun ident => ident).contains decl.userName)
        then continue
      trace[EggTactic.egg] (s!"**processing local declaration {decl.userName}" ++
      s!":= {decl.toExpr} : {← inferType decl.toExpr}")
      eggAddExprAsRewrite  goalMVar decl.toExpr (← inferType decl.toExpr)
      rewrites := List.removeAll rewrites [decl.userName]
    for rwName in rewrites do
      if let some rw := (← getEnv).find? rwName then
        trace[EggTactic.egg] (s!"**processing global declaration {rw.name}" ++
        s!":= {rw.name} : {← inferType rw.type}")
        -- TODO: get universe levels right here...
        eggAddExprAsRewrite  goalMVar (Expr.const rw.name []) (← inferType rw.value!)
        continue
      throwError "rewrite '{rwName}' not found in local context"

declare_syntax_cat eggconfigval
declare_syntax_cat eggconfig

syntax "(" "timeLimit" ":=" num ")" : eggconfigval
syntax "noInstantiation" : eggconfigval
syntax "dump" : eggconfigval
syntax "oneSided" : eggconfigval
syntax "simplify" : eggconfigval
syntax eggconfigval eggconfig : eggconfig
syntax eggconfigval : eggconfig

def Lean.TSyntax.updateEggConfig : TSyntax `eggconfigval → EggConfig → EggConfig
  | `(eggconfigval| noInstantiation ) => λ cfg => { cfg with explodeMVars := false }
  | `(eggconfigval| oneSided ) =>  λ cfg => { cfg with twoSided := false }
  | `(eggconfigval| dump ) =>  λ cfg => { cfg with dumpGraph := true }
  | `(eggconfigval| simplify ) =>  λ cfg => { cfg with simplifyExprs := true }
  | `(eggconfigval| (timeLimit := $n:num) ) => λ cfg => { cfg with time := n.getNat }
  | stx => panic! s!"unknown egg configuration syntax {stx}"

partial def Lean.TSyntax.getEggConfig : TSyntax `eggconfig → EggConfig
  | `(eggconfig| $v:eggconfigval $r:eggconfig) => v.updateEggConfig r.getEggConfig
  | `(eggconfig| $v:eggconfigval ) => v.updateEggConfig default
  | _ => panic! "unknown egg config syntax"

elab "egg" "[" rewriteNames:ident,* "]" c:(eggconfig)? : tactic => withMainContext do
  trace[EggTactic.egg] (s!"0) Running Egg on '{← getMainTarget}'")
  let decls : List LocalDecl := (← getLCtx).decls.toList.filter Option.isSome |>.map Option.get!
  let idsnames := decls.map λ decl => (repr decl.fvarId, decl.userName)
  trace[EggTactic.egg] "\nfvar local decls: {idsnames}\n"

  let (_, goalLhs, goalRhs) ← match (← matchEq? (<- getMainTarget)) with
    | .none => throwError "Egg: target not equality: {<- getMainTarget}"
    | .some eq => pure eq

  let cfg : EggConfig := match c with
    | none =>
      --trace[EggTactic.egg] "did not find config, using default"
      default
    | some cfgSyn => cfgSyn.getEggConfig
  trace[EggTactic.egg] "using config: {repr cfg}"

  let rewrites ←  (addNamedRewrites (<- getMainGoal) (rewriteNames.getElems.toList)).getRewrites cfg
  trace[EggTactic.egg] "simplifying {(← exprToUntypedSexp goalLhs)} {(← exprToUntypedSexp goalRhs)} {rewrites}"

  let (simplifiedLhs,simplifiedRhs,simplifiedRewrites,mapping) :=
    if cfg.simplifyExprs then
       simplifyRequest (← exprToUntypedSexp goalLhs) (← exprToUntypedSexp goalRhs) rewrites
    else
       (← exprToUntypedSexp goalLhs,← exprToUntypedSexp goalRhs,rewrites,[])
  trace[EggTactic.egg] "simplification result {simplifiedLhs} {simplifiedRhs} {simplifiedRewrites}"
  trace[EggTactic.egg] "simplification mapping {mapping}"
  let eggRequest := {
    targetLhs := simplifiedLhs.toString,
    targetRhs := simplifiedRhs.toString,
    rewrites := simplifiedRewrites,
    time := cfg.time,
    dumpGraph := cfg.dumpGraph,
    varMapping := mapping
    : EggRequest
  }
  let explanations := (← runEggRequest (← getMainGoal) eggRequest)
  for e in explanations do
    trace[EggTactic.egg] (s!"14) applying rewrite explanation {e}")
    trace[EggTactic.egg] (s!"14.5) current goal: {(<- getMainGoal).name} : {(<- inferType (Expr.mvar (<- getMainGoal)))}")
    let eggRewrite <-
      match rewrites.find? (fun rw => rw.name == e.rule) with
      | .some rw => pure rw
      |  .none => throwTacticEx `egg (<- getMainGoal) (f!"unknown local declaration {e.rule} in rewrite {e}")
    trace[EggTactic.egg] (s!"14.6) found eggRewrite {eggRewrite}\n\twith rw {eggRewrite.rw} : {<- inferType eggRewrite.rw}")
    trace[EggTactic.egg] (s!"15) applying rewrite expression eggRewrite: {eggRewrite} to target: {<- getMainTarget}")
    -- let rwType <- e.instantiateTarget eggRewrite.rwType
    -- let rewriteResult <- rewrite
    --   (← getMainGoal)
    --   (← getMainTarget)
    --   (← instantiateMVars eggRewrite.rw)
    --   (symm := e.direction == Backward)
    -- trace[EggTactic.egg] (s!"16) rewritten to: {rewriteResult.eNew} with proof: {rewriteResult.eqProof}")
    -- trace[EggTactic.egg] (s!"16) rewritten to: {e.result} with proof: {rewriteResult.eqProof}")
    -- let goal' ← replaceTargetEq (<- getMainGoal) rewriteResult.eNew rewriteResult.eqProof
    let (eggxplanationRw, eggxplanationRwTy) ← e.instantiateEqType eggRewrite
    -- let (eggLhs, eggRhs) := if e.direction == EggRewriteDirection.Forward
    --      then (e.source, e.result)
    --      else (e.result, e.source)

    let (mainLhs, mainRhs) ← match (← matchEq? (<- getMainTarget)) with
      | .none => throwError "Egg: target not equality: {<- getMainTarget}"
      | .some (_, lhs, rhs) => pure (lhs, rhs)
    -- trace[EggTactic.egg] (s!"16) eggLhs:       {eggLhs}")
    trace[EggTactic.egg] (s!"16) mainLhs     : {mainLhs}")
    trace[EggTactic.egg] s!"16) --"
    trace[EggTactic.egg] (s!"16) mainRhs     : {mainRhs}")
    -- trace[EggTactic.egg] (s!"16) eggRhs     : {eggRhs}")
    trace[EggTactic.egg] s!"16) --"
    -- let isEq ← isDefEq eggLhs mainLhs
    -- trace[EggTactic.egg] (s!"16) isEq:          : {isEq}")
    trace[EggTactic.egg] (s!"16) rewrite        : {eggxplanationRw}")
    let rewriteType ← inferType eggxplanationRw
    trace[EggTactic.egg] (s!"16) rewrite type   : {rewriteType}")
    --trace[EggTactic.egg] (s!"16) rewrite type   : {← inferType eggxplanationRw}")
    -- TODO: maybe revive the code that passes the direction (and the burden)
    -- to `rewriteResult` (or stop using rewrite altogether)
    let rewriteResult <- (<- getMainGoal).rewrite
        (<- getMainTarget)
        eggxplanationRw
        (occs := Occurrences.pos [e.position])
        -- The rewrite direction here is different from the direction of the
        -- explanation! The former is given by egg, the latter is what *we* gave
        -- to egg.
        (symm := eggRewrite.direction == Backward)

    trace[EggTactic.egg] (f!"rewritten to: {rewriteResult.eNew}")
    let mvarId' ← (← getMainGoal).replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
    replaceMainGoal (mvarId' :: rewriteResult.mvarIds)

    -- let goal'ty <- inferType (Expr.mvar goal')
    -- trace[EggTactic.egg] (s!"18) new goal: {goal'.name} : {goal'ty}")
    -- replaceMainGoal [goal'] -- replace main goal with new goal + subgoals
  -- TODO: replace 'simp' with something that dispatches 'a=a' sanely.
  let _ <- simpGoal (<- getMainGoal) (<- Simp.Context.mkDefault)
  return ()
