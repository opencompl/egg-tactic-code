import EggTactic.Sexp
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

builtin_initialize registerTraceClass `EggTactic.egg

-- Path to the egg server.
def egg_server_path : String :=
  "json-egg/target/debug/egg-herbie"

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

instance : Inhabited EggRewrite where
  default := EggRewrite.mk
         "default" "default" "default" #[] default default default default

inductive EggRewriteDirection where
  | Forward
  | Backward
  deriving Inhabited, DecidableEq

open EggRewriteDirection

structure Eggxplanation where
  direction: EggRewriteDirection -- direction of the rewrite
  rule: String -- name of the rewrite rule
  result: Expr -- result of the rewrite
  source: Expr -- source of the rewrite
  mvars: List (Sexp × Expr) -- metavariables in the rewrite rule and its assignment

instance : ToString Eggxplanation where
  toString expl :=
    let dir := if expl.direction == Forward then "fwd" else "bwd"
    let mvars := expl.mvars.map (fun (mvar, expr) => s!"{mvar} := {expr}")
    let mvars := "{" ++ (", ".intercalate mvars) ++ "}"
    toString f!"(Eggxplanation dir:{dir} rule:{expl.rule} mvars:{mvars} result:{expl.result})"



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

-- TODO: see if there is some other way to give mvars in a structured way instead of string
-- I really want to be able to give the full Name.
def mvarIdToSexp (m:MVarId): Sexp :=
 "?" ++ toString m.name


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

/-
convert this expression into a string, along with the names of the
bound variables.
-/
def exprToSexp (e: Expr): MetaM Sexp :=
match e with
  | Expr.const name [] => return .fromList ["const", nameToSexp name, "nolevels"]
  | Expr.const name levels => return .fromList ["const", nameToSexp name, .fromList ["levels", (levels.map levelToSexp)]]
  | Expr.bvar ix => throwError s!"expected no bound variables, we use locally nameless!, but found bvar '{ix}'"
  | Expr.fvar id => return .fromList ["fvar", nameToSexp id.name]
  -- TODO: see if there is some other way to give mvars in a structured way instead of string
  | Expr.mvar id => return  mvarIdToSexp id
  | Expr.lit (.natVal n)=> return .fromList ["litNat", toString n]
  | Expr.app  l r => do
     return (.fromList ["ap", (← exprToSexp l), (← exprToSexp r)])
  | _ => throwError s!"unimplemented expr_to_string ({e.ctorName}): {e}"


partial def parseExprSexpr (s: Sexp): MetaM Expr := do
  match s with
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
    let expr ← parseExprSexpr $ expr.unsimplify mapping
    let mvaridSexp ← exceptToMetaM <| parseSingleSexp mvaridStr
    return (mvaridSexp, expr) :: out
  })
  let result ← exceptToMetaM (← exceptToMetaM <| j.getObjVal? "result").getStr?
  let result ← exceptToMetaM <| (parseSingleSexp result)
  let result ← parseExprSexpr $ result.unsimplify mapping

  let source ← exceptToMetaM (← exceptToMetaM <| j.getObjVal? "source").getStr?
  let source ← exceptToMetaM <| parseSingleSexp source
  let source ← parseExprSexpr $ source.unsimplify mapping

  return { direction := direction
          , rule := rewrite -- TODO: make consistent in terminology
          , mvars := mvarid2expr
          , result := result
          , source := source
          : Eggxplanation }

-- | Actually do the IO. This incurs an `unsafe`.
unsafe def unsafePerformIO [Inhabited α] (io: IO α): α :=
  match unsafeIO io with
  | Except.ok a    =>  a
  | Except.error _ => panic! "expected io computation to never fail"

-- | Circumvent the `unsafe` by citing an `implementedBy` instance.
@[implementedBy unsafePerformIO]
def performIO [Inhabited α] (io: IO α): α := Inhabited.default


def surroundQuotes (s: String): String :=
 "\"" ++ s ++ "\""
def surround_escaped_quotes (s: String): String :=
 "\\\"" ++ s ++ "\\\""


def EggRewrite.toJson (rewr: EggRewrite) :=
  "{"
    ++ surroundQuotes "name" ++ ":" ++ surroundQuotes rewr.name ++ ","
    ++ surroundQuotes "lhs" ++ ":" ++ surroundQuotes rewr.lhs.toString ++ ","
    ++ surroundQuotes "rhs" ++ ":" ++ surroundQuotes rewr.rhs.toString ++
  "}"

instance : ToString EggRewrite where
  toString rewr := rewr.toJson


structure EggRequest where
  targetLhs: String
  targetRhs: String
  varMapping : VariableMapping
  rewrites: List EggRewrite

def EggRequest.toJson (e: EggRequest): String :=
  "{"
  ++ surroundQuotes "request"  ++  ":" ++ surroundQuotes "perform-rewrite" ++ ","
  ++ surroundQuotes "target-lhs"  ++  ":" ++ surroundQuotes (e.targetLhs) ++ ","
  ++ surroundQuotes "target-rhs"  ++  ":" ++ surroundQuotes (e.targetRhs) ++ ","
  ++ surroundQuotes "rewrites" ++ ":" ++ "[" ++ String.intercalate "," (e.rewrites.map EggRewrite.toJson) ++ "]"
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


structure EggState where
  ix: Nat := 0
  name2expr: List (Int × Expr) := []
  rewrites: List EggRewrite := []
  deriving Inhabited

abbrev EggM (α: Type) := StateT EggState TermElabM α

def EggM.getRewrites (egg: EggM Unit): TermElabM (List EggRewrite) := do
  pure (← egg.run default).snd.rewrites

-- Find expressions of a given type in the local context
def withExprsOfType (g: MVarId) (t : Expr) (f: Expr → EggM Unit): EggM Unit := do
   withMVarContext g do -- TODO: deprecated
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
  (pretendMVars: Array MVarId): EggM Unit := do
  let i := (← get).ix
  dbg_trace s!"addEggRewrite rw:{rw} ty:{ty} lhs:{lhs} rhs:{rhs} name:{i}"

  let egg_rewrite :=
    { name := toString i
    , lhs := lhs
    , rhs := rhs
    , rw := rw
    , unappliedRw := unappliedRw
    , rwType := ty
    , unappliedRwType := unappliedRwType
    , pretendMVars := pretendMVars : EggRewrite }
  modify (fun state => { state with ix := i + 1, name2expr := (i, rw) :: state.name2expr, rewrites := egg_rewrite :: state.rewrites })

def expr_get_forall_bound_vars: Expr -> List Name
| Expr.forallE name ty body _ => name :: expr_get_forall_bound_vars body
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


/-
Create a regular equality of the form lhs = rhs
-/
def addBareEquality
  (rw: Expr)
  (rwUnapplied: Expr)
  (ty: Expr)
  (unappliedRwType: Expr)
  (mvars: Array MVarId): EggM Unit := do
  dbg_trace "**adding bareEquality {rw} : {ty}"
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
  if rhs.getAppMVars.isSubsetOf lhs.getAppMVars then
    addEggRewrite rw rwUnapplied
        ty unappliedRwType
        (← exprToSexp lhs)
        (← exprToSexp rhs) mvars
  else if lhs.getAppMVars.isSubsetOf rhs.getAppMVars then
    dbg_trace "TODO: make symmetric rewrite when we have foralls: (LHS: {lhs}) (RHS: {rhs})"
    -- addEggRewrite (← mkEqSymm rw) (← exprToString rhs) (← exprToString lhs)
  else
    dbg_trace "ERROR: have equality where RHS has more vars than LHS: (LHS: {lhs}) (RHS: {rhs})"

/-
Create an equality with MVars
-/
def addForallMVarEquality (rw: Expr) (ty: Expr): EggM Unit := do
  tacticGuard ty.universallyQuantifiedEq? "**expected ∀ ... a = b**"
  dbg_trace "**adding forallMVarEquality {rw} : {ty}"
  let (ms, _binders, tyNoForall) ← forallMetaTelescope ty
  -- | code taken from Lean/Meta/Rewrite.lean by looking at `heq`.
  let rwApplied := mkAppN rw ms -- is this correct?
  addBareEquality rwApplied rw  tyNoForall ty (ms.map fun e => e.mvarId!)


--  explode an equality with ∀ by creating many variations, from the local context.
-- It is well founded because we destructure the inductive type, but lean is unable to
-- infer this
partial def addForallExplodedEquality_ (goal: MVarId)
  (rw: Expr) (rwUnapplied: Expr)
  (ty: Expr)
  (unappliedRwType: Expr): EggM Unit := do
  if let Expr.forallE x xty body _ := ty then do {
  --dbg_trace "**forall is : (FA [{x} : {xty}] {body})"
   withExprsOfType goal xty $ λ xval => do
      -- dbg_trace "**exploding {ty} @ {xval} : {← inferType xval }"
      -- addForallExplodedEquality_ goal rw (←  mkAppM' ty #[xval])
      addForallExplodedEquality_ goal
          (Expr.beta rw #[xval])
          rwUnapplied
          (← instantiateForall ty #[xval])
          unappliedRwType
  } else {
    addBareEquality rw rwUnapplied ty unappliedRwType #[]
  }


-- See `addForallExplodedEquality_`
def addForallExplodedEquality (goal: MVarId) (rw: Expr) (ty: Expr): EggM Unit := do
  tacticGuard ty.universallyQuantifiedEq? "**expected ∀ ... a = b**"
  dbg_trace "**adding forallExplodedEquality {rw} : {ty}"
  addForallExplodedEquality_ goal rw rw ty ty

-- Add an expression into the EggM context, if it is indeed a rewrite
def eggAddExprAsRewrite (goal: MVarId) (rw: Expr) (ty: Expr): EggM Unit := do
  if ty.universallyQuantifiedEq? then
    if ty.isForall then do
        -- addForallExplodedEquality goal rw ty
        addForallMVarEquality rw ty
    else if ty.isEq then do
        addBareEquality rw rw ty ty #[]


-- Add all equalities from the local context
def addAllLocalContextEqualities (goal: MVarId) (goals: List MVarId): EggM Unit :=
  withMVarContext goal do
    dbg_trace "goals: {goals.map fun g => g.name}"
    for decl in (← getLCtx) do
      if decl.toExpr.isMVar && goals.contains (decl.toExpr.mvarId!)
        then continue
      dbg_trace (s!"**processing local declaration {decl.userName}" ++
      s!":= {decl.toExpr} : {← inferType decl.toExpr}")
      -- TODO: call the correct API to resolve metavariables
      -- to enable local declarations such as 'have gh := group_inv h'
      -- eggAddExprAsRewrite goal (<- reduce decl.toExpr) (<- reduce (← inferType decl.toExpr))
      eggAddExprAsRewrite goal decl.toExpr (← inferType decl.toExpr)


-- Do the dirty work of sending a string, and reading the string out from stdout
def runEggRequestRaw (requestJson: String): MetaM String := do
    dbg_trace "sending request:\n{requestJson}"
    let eggProcess <- IO.Process.spawn
      { cmd := egg_server_path,
        -- stdin := IO.Process.Stdio.piped,
        stdout := IO.Process.Stdio.piped,
        stdin := IO.Process.Stdio.piped,
        -- stdout := IO.Process.Stdio.null,
        stderr := IO.Process.Stdio.null
      }
    FS.writeFile s!"/tmp/egg.json" requestJson
    dbg_trace "3) Spanwed egg server process. Writing stdin..."
    let (stdin, eggProcess) ← eggProcess.takeStdin
    stdin.putStr requestJson
    dbg_trace "5) Wrote stdin. Setting up stdout..."
    let stdout ← IO.asTask eggProcess.stdout.readToEnd Task.Priority.dedicated
    dbg_trace "6) Setup stdout. Waiting for exitCode..."
    let exitCode : UInt32 <- eggProcess.wait
    dbg_trace "7) got exitCode ({exitCode}). Waiting for stdout..."
    let stdout : String <- IO.ofExcept stdout.get
    -- dbg_trace "8) read stdout."
    -- let stdout : String := "STDOUT"
    dbg_trace ("9)stdout:\n" ++ stdout)
    return stdout


def Eggxplanation.instantiateEqType
  (expl: Eggxplanation)
  (eggrw: EggRewrite): MetaM (Expr × Expr) := do
    let eq ← match expl.direction with
        | .Forward =>  mkEq expl.source expl.result
        | .Backward =>  mkEq expl.result expl.source
    dbg_trace "*** eq                       : {eq}"
    let mut args : Array Expr := #[]
    for mvar in eggrw.pretendMVars do
      let needle := mvarIdToSexp mvar
      match expl.mvars.find? (fun mvarExpr => mvarExpr.1 == needle) with
      | .some (_, val) =>
          args := args.push (val)
      | .none => throwError "unable to find value for mvar: {mvar}"

    -- TODO: Is there a better way to instantiating universal quantifiers?
    let (ms, _binders, rwTypeAppliedToMVar) ← forallMetaTelescope eggrw.unappliedRwType
    for (m, arg) in ms.zip args do
      dbg_trace "*** mvar {m} := {arg}"
      -- TODO: how about this one, is there a less cursed way here?
      let _ ← isDefEq m arg -- force unification

    -- resolve `MVar`s that were unified above in `rwTypeAppliedToMVar`
    let rwTy ← instantiateMVars rwTypeAppliedToMVar
    dbg_trace "***rwTy: {rwTy}"
    let rwTy ← match (← matchEq? rwTy) with
                | .some (_, source, target) =>
                    if expl.direction == .Forward then
                      mkEq source target
                    else
                      mkEq target source
                | .none => throwError "unable to matchEq? {rwTy}"
    dbg_trace "***rwTy: {rwTy}"

    -- let (ms, binders, rwAppliedToMVar) ← forallMetaTelescope eggrw.unappliedRw
    -- for (m, arg) in ms.zip args do
    --   dbg_trace "*** mvar {m} := {arg}"
    --   let _ ← isDefEq m arg -- force unification
    -- let rw ← instantiateMVars rwAppliedToMVar
    let rw := eggrw.unappliedRw
    dbg_trace "***rw: {rw}"
    let rw := mkAppN rw args
    dbg_trace "***rw: {rw}"
    -- TODO: just in case (quote bollu "it's spiritual; I ask god")
    let rw ← instantiateMVars rw
    dbg_trace "***rw: {rw}"
    let rw ← (if expl.direction == EggRewriteDirection.Forward
             then pure rw
             else mkEqSymm rw)
    dbg_trace "***rw: {rw}"
    return (rw, rwTy)

def simplifyRequest (lhs rhs : Sexp) (rewrites : List EggRewrite)
  : Sexp × Sexp × List EggRewrite × VariableMapping :=
  let rewriteSexps := List.join $  rewrites.map  λ rw => [rw.lhs,rw.rhs]
  let (substituted, mapping) := simplifySexps $
    lhs :: rhs :: rewriteSexps
  Id.run do
    let mut resRewrites := []
    let mut remaining := substituted.tail!.tail!
    for rw in rewrites do
      if let lhs::rhs::remaining' := remaining then
        resRewrites := resRewrites ++
          [{ name := rw.name, lhs := lhs, rhs := rhs,
             pretendMVars := rw.pretendMVars, rw := rw.rw,
             unappliedRw := rw.unappliedRw, rwType := rw.rwType,
             unappliedRwType := rw.unappliedRwType : EggRewrite}]
        remaining := remaining'
      else
        panic! "error unpacking rewrites"
    return (substituted.head!, substituted.tail!.head!,resRewrites,mapping)

-- parse the response, given the response as a string
def parseEggResponse (goal: MVarId) (varMapping : VariableMapping) (responseString: String) :
  MetaM (List Eggxplanation) := do
    let outJson : Json <- match Json.parse responseString with
      | Except.error e => throwTacticEx `rawEgg goal e
      | Except.ok j => pure j
    dbg_trace ("10)stdout as json:\n" ++ (toString outJson))
    let responseType := (outJson.getObjValD "response").getStr!
    dbg_trace ("11)stdout response: |" ++ responseType ++ "|")
    if responseType == "error"
    then throwTacticEx `rawEgg goal (toString outJson)
    else
      dbg_trace "12) Creating explanation..."
      -- This whole thing is in an Except beacause everything in Json
      -- is written relative to Except, and not a general MonadError :(
      -- extract explanation field from response
      let explanation <- exceptToMetaM (outJson.getObjVal? "explanation")
      -- cast field to array
      let explanation <- exceptToMetaM <| Json.getArr? explanation
      -- map over each element into an explanation
      let explanation <- explanation.mapM (parseExplanation varMapping)
      let explanation := explanation.toList
      dbg_trace ("13) explanation: |" ++ String.intercalate " ;;; " (explanation.map toString) ++ "|")
      return explanation

-- High level wrapped aroung runEggRequestRaw that is well-typed, and returns the
-- list of explanations
def runEggRequest (goal: MVarId) (request: EggRequest): MetaM (List Eggxplanation) :=
  runEggRequestRaw request.toJson >>= (parseEggResponse goal request.varMapping)

-- Add rewrites with known names 'rewriteNames' from the local context of 'goalMVar'
def addNamedRewrites (goalMVar: MVarId)  (rewriteNames: List Ident): EggM Unit :=
  withMVarContext goalMVar do
    dbg_trace " addNamedRewrites {goalMVar.name} {rewriteNames.map toString}"
    for decl in (← getLCtx) do
    -- TODO: find a way to not have to use strings, see how 'simp' does this.
    if !((rewriteNames.map fun ident => ident.getId ).contains decl.userName)
    then continue
    dbg_trace (s!"**processing local declaration {decl.userName}" ++
    s!":= {decl.toExpr} : {← inferType decl.toExpr}")
    eggAddExprAsRewrite  goalMVar decl.toExpr (← inferType decl.toExpr)



elab "rawEgg" "[" rewriteNames:ident,* "]" : tactic => withMainContext do
  dbg_trace (s!"0) Running Egg on '{← getMainTarget}'")

  let (_, goalLhs, goalRhs) ← match (← matchEq? (<- getMainTarget)) with
    | .none => throwError "Egg: target not equality: {<- getMainTarget}"
    | .some eq => pure eq

  let rewrites ←  (addNamedRewrites (<- getMainGoal) (rewriteNames.getElems.toList)).getRewrites
  dbg_trace "simplifying {(← exprToSexp goalLhs)} {(← exprToSexp goalRhs)} {rewrites}"

  let (simplifiedLhs,simplifiedRhs,simplifiedRewrites,mapping) := simplifyRequest
    (← exprToSexp goalLhs) (← exprToSexp goalRhs) rewrites
  dbg_trace "simplification result {simplifiedLhs} {simplifiedRhs} {simplifiedRewrites}"
  let eggRequest := {
    targetLhs := simplifiedLhs.toString,
    targetRhs := simplifiedRhs.toString,
    rewrites := simplifiedRewrites
    varMapping := mapping
    : EggRequest
  }
  let explanations := (← runEggRequest (← getMainGoal) eggRequest)
  for e in explanations do
    dbg_trace (s!"14) applying rewrite explanation {e}")
    dbg_trace (s!"14.5) current goal: {(<- getMainGoal).name} : {(<- inferType (Expr.mvar (<- getMainGoal)))}")
    let eggRewrite <-
      match rewrites.find? (fun rw => rw.name == e.rule) with
      | .some rw => pure rw
      |  .none => throwTacticEx `rawEgg (<- getMainGoal) (f!"unknown local declaration {e.rule} in rewrite {e}")
    dbg_trace (s!"14.6) found eggRewrite {eggRewrite}\n\twith rw {eggRewrite.rw} : {<- inferType eggRewrite.rw}")
    dbg_trace (s!"15) applying rewrite expression eggRewrite: {eggRewrite} to target: {<- getMainTarget}")
    -- let rwType <- e.instantiateTarget eggRewrite.rwType
    -- let rewriteResult <- rewrite
    --   (← getMainGoal)
    --   (← getMainTarget)
    --   (← instantiateMVars eggRewrite.rw)
    --   (symm := e.direction == Backward)
    -- dbg_trace (s!"16) rewritten to: {rewriteResult.eNew} with proof: {rewriteResult.eqProof}")
    -- dbg_trace (s!"16) rewritten to: {e.result} with proof: {rewriteResult.eqProof}")
    -- let goal' ← replaceTargetEq (<- getMainGoal) rewriteResult.eNew rewriteResult.eqProof
    let (eggxplanationRw, eggxplanationRwTy) ← e.instantiateEqType eggRewrite
    -- let (eggLhs, eggRhs) := if e.direction == EggRewriteDirection.Forward
    --      then (e.source, e.result)
    --      else (e.result, e.source)

    let (mainLhs, mainRhs) ← match (← matchEq? (<- getMainTarget)) with
      | .none => throwError "Egg: target not equality: {<- getMainTarget}"
      | .some (_, lhs, rhs) => pure (lhs, rhs)
    -- dbg_trace (s!"16) eggLhs:       {eggLhs}")
    dbg_trace (s!"16) mainLhs     : {mainLhs}")
    dbg_trace s!"16) --"
    dbg_trace (s!"16) mainRhs     : {mainRhs}")
    -- dbg_trace (s!"16) eggRhs     : {eggRhs}")
    dbg_trace s!"16) --"
    -- let isEq ← isDefEq eggLhs mainLhs
    -- dbg_trace (s!"16) isEq:          : {isEq}")
    dbg_trace (s!"16) rewrite        : {eggxplanationRw}")
    dbg_trace (s!"16) rewrite type   : {← inferType eggxplanationRw}")
    -- TODO: maybe revive the code that passes the direction (and the burden)
    -- to `rewriteResult` (or stop using rewrite altogether)
    let rewriteResult <- (<- getMainGoal).rewrite
        (<- getMainTarget)
        eggxplanationRw

    dbg_trace (f!"rewritten to: {rewriteResult.eNew}")
    let mvarId' ← replaceTargetEq (← getMainGoal) rewriteResult.eNew rewriteResult.eqProof
    replaceMainGoal (mvarId' :: rewriteResult.mvarIds)

    -- let goal'ty <- inferType (Expr.mvar goal')
    -- dbg_trace (s!"18) new goal: {goal'.name} : {goal'ty}")
    -- replaceMainGoal [goal'] -- replace main goal with new goal + subgoals
  -- TODO: replace 'simp' with something that dispatches 'a=a' sanely.
  let _ <- simpGoal (<- getMainGoal) (<- Simp.Context.mkDefault)
  return ()
