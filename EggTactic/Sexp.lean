import Lean
open Lean

-- @bollu: I removed the substring in `list` as we don't really use it for anything and
-- it just complicates things
inductive Sexp
| atom: String → Sexp
| list: List Sexp → Sexp
deriving BEq, Inhabited, Repr

def Sexp.fromString : String → Sexp
| s => Sexp.atom s

instance : Coe String Sexp where
  coe s := Sexp.fromString s

def Sexp.fromList : List Sexp → Sexp
| xs => Sexp.list xs

instance : Coe (List Sexp) Sexp where
  coe := Sexp.fromList


partial def Sexp.toString : Sexp → String
| .atom s => s
| .list xs => "(" ++ " ".intercalate (xs.map Sexp.toString) ++ ")"

instance : ToString Sexp := ⟨Sexp.toString⟩

def Sexp.toList? : Sexp → Option (List Sexp)
| .atom _ => .none
| .list xs => .some xs

def Sexp.toAtom! : Sexp → String
| .atom s => s
| .list xs => panic! s!"expected atom, found list at {List.toString xs}"


inductive SexpTok
| sexp: Sexp →  SexpTok
| opening: String.Pos → SexpTok
deriving BEq, Inhabited, Repr


structure SexpState where
  it: String.Iterator
  stack: List SexpTok := []
  sexps: List Sexp := []
  depth : Nat := 0
deriving BEq, Repr

def SexpState.fromString (s: String): SexpState :=
  { it := s.iter : SexpState }

instance : Inhabited SexpState where
  default := SexpState.fromString ""

inductive SexpError
| unmatchedOpenParen (ix: String.Iterator): SexpError
| unmatchedCloseParen (ix: String.Iterator): SexpError
| notSingleSexp (s: String) (xs: List Sexp): SexpError
deriving BEq, Repr

instance : ToString SexpError where toString := λ err => match err with
  | .unmatchedOpenParen ix => s!"Unmatched open parenthesis at {ix}"
  | .unmatchedCloseParen ix => s!"Unmatched close parenthesis at {ix}"
  | .notSingleSexp s xs => s!"not a single sexp '{s}', parsed as: '{xs}'"

abbrev SexpM := EStateM SexpError SexpState

def SexpM.peek: SexpM (Option (Char × String.Pos)) := do
  let state ← get
  return if state.it.atEnd then .none else .some (state.it.curr, state.it.i)

def SexpM.curPos: SexpM String.Pos := do
  let state ← get
  return state.it.i

-- Stop is a good name, because it indicates that it's exclusive
-- (AG: I don't read it as being exclusive from the name 'stop')
def SexpM.mkSubstring (l: String.Pos) (r: String.Pos): SexpM Substring := do
  let state ← get
  return { str := state.it.s, startPos := l, stopPos := r}

def SexpM.advance: SexpM Unit := do
  modify (fun state => { state with it := state.it.next })

def SexpM.pushTok (tok: SexpTok): SexpM Unit := do
  modify (fun state => { state with stack := tok :: state.stack })

def SexpM.pushSexp (sexp: Sexp): SexpM Unit := do
  let state ← get
  if state.stack.length == 0
  then set { state with stack := [], sexps := sexp :: state.sexps }
  else set { state with stack := (SexpTok.sexp sexp) :: state.stack }


def SexpM.incrementDepth: SexpM Unit :=
  modify (fun state => { state with depth := state.depth + 1 })

def SexpM.decrementDepth: SexpM Unit :=
  modify (fun state => { state with depth := state.depth - 1 })


instance [Inhabited α] : Inhabited (SexpM α) where
  default := do return default


def SexpM.pop: SexpM SexpTok := do
  let state ← get
  match state.stack with
  | [] => panic! "empty stack"
  | x::xs => do
      set { state with stack := xs }
      return x

-- abbrev SexpTokStack := List SexpTok

-- Remove elements from the stack of tokens `List SexpToken` till we find a `SexpToken.opening`.
-- When we do, return (1) the position of the open paren, (2) the list of SexpTokens left on the stack, and (3) the list of Sexps
-- Until then, accumulate the `SexpToken.sexp`s into `sexps`.
def stackPopTillOpen (stk: List SexpTok) (sexps: List Sexp := []): Option (String.Pos × (List SexpTok) × (List Sexp)) :=
  match stk with
  | [] => .none
  | SexpTok.opening openPos :: rest => (.some (openPos, rest, sexps))
  | SexpTok.sexp s :: rest => stackPopTillOpen rest (s :: sexps)

-- collapse the current stack till the last ( into a single Sexp.list
def SexpM.matchClosingParen: SexpM Unit := do
  let state ← get
  match stackPopTillOpen state.stack with
  | (.some (_, stk, sexps)) =>
    let sexp := Sexp.list sexps
    modify (fun state => { state with stack := stk })
    SexpM.pushSexp sexp
  | (.none) => throw (SexpError.unmatchedCloseParen state.it)


partial def SexpM.takeString (startPos: String.Pos): SexpM Substring := do
  match (← SexpM.peek) with
  | .none => SexpM.mkSubstring startPos (← SexpM.curPos)
  | .some (' ', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | .some ('(', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | .some (')', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | .some _ => do
     SexpM.advance
     SexpM.takeString startPos

partial def SexpM.parse: SexpM Unit := do
  match (← SexpM.peek) with
  | .some  ('(', i) => do
     SexpM.advance
     SexpM.pushTok (SexpTok.opening i)
     SexpM.incrementDepth
     SexpM.parse
  | .some (')', _) => do
     SexpM.advance
     SexpM.matchClosingParen
     SexpM.parse
     -- return cur ++ rest
  | .some (' ', _) => do
      SexpM.advance
      SexpM.parse
  | .some (_, i) => do
      let s ← SexpM.takeString i
      SexpM.pushSexp ((Sexp.atom s.toString))
      SexpM.parse
  | .none => do
      let state ← get
      match stackPopTillOpen state.stack with
      | (.some (openPos, _, _)) =>
          throw <| SexpError.unmatchedOpenParen   ({ s := state.it.s, i := openPos : String.Iterator })
      | (.none) => return ()

-- | Parse a list of (possibly empty) sexps.
def parseSexpList (s: String):  Except SexpError (List Sexp) :=
  let initState := SexpState.fromString s
  match EStateM.run SexpM.parse initState with
  | .ok () state => .ok state.sexps.reverse
  | .error e _ => .error e

-- | Parse a single s-expression, and error if found no sexp or multiple sexps
def parseSingleSexp (s: String): Except SexpError Sexp := do
  match (← parseSexpList s) with
  | [x] => .ok x
  | xs => .error (.notSingleSexp s xs)

-- To simplify Sexps, we want to replace some subterms in an Sexp:
-- Have to mark this as partial since the termination checker doesn't like
-- these higher-order functions like map. See: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20using.20higher-order.20functions.20on.20inductive.20types.3A.20termin.2E.2E.2E
partial def replaceTerm (toReplace : Sexp) (replaceWith : Sexp) (atSexp : Sexp) : Sexp :=
  if toReplace == atSexp then replaceWith
  else match atSexp with
  | .atom _ => atSexp
  | .list sexps => sexps.map $ replaceTerm toReplace replaceWith

-- The idea of this simplification is to do substitutions that replace a term,
-- such that the replaced term never appears as a proper subterm elsewhere in
-- the request, i.e. neither as the goal/starting point nor in any of the
-- rewrites. Ideally maximal subterms with this property

-- For this, we start by finding wether a subexpression is contained in an Sexp
-- Yes, this is not optimal because of the checks, feel free to rewrite.

-- Need this order of arguments (awkward for recursive call) for `.` notation
partial def Sexp.containsSubexpr (mainExpr : Sexp) (subExpr : Sexp) : Bool :=
  if subExpr == mainExpr then true
  else match mainExpr with
    | .atom _ => false
    | .list sexps => sexps.any (containsSubexpr · subExpr)

partial def Sexp.vars : Sexp → List String
  | .atom s => [s]
  | .list sexps => List.join $ sexps.map vars

-- We only consider fvars
partial def Sexp.fvars : Sexp → List Sexp
  | .atom _ => []
  | fvar@(.list ("fvar"::_)) => [fvar]
  | .list sexps => List.join $ sexps.map fvars

partial def Sexp.consts : Sexp → List Sexp
  | .atom _ => []
  | c@(.list ("const"::_)) => [c]
  | .list sexps => List.join $ sexps.map consts

def Sexp.selectStr : Sexp → List String := Sexp.vars
  --λ e => e.fvars.map Sexp.toString ++ e.consts.map Sexp.toString

-- basically: sexp.variables ∩ vars ≠ ∅
partial def Sexp.containsVars : Sexp → List String → Bool
  | .atom s, vars => vars.contains s
  | .list sexps, vars => sexps.any (containsVars · vars)

-- We could maybe replace this with `Std.HashMap`, but this should do it for now.
abbrev VariableMapping := List (String × Sexp)

-- Some generic helper functions
def _root_.List.revLookup? {α β : Type 0} [BEq β] : List (α × β) → β → Option α
  | [], _ => none
  | (a,b)::rest, b' => if b == b' then some a else rest.revLookup? b'

def _root_.List.unique {α : Type 0} [BEq α] : List α → List α
  | [] => []
  | a :: as => if as.contains a then as.unique else (a :: as.unique)

def _root_.List.unzip3 {α β γ : Type 0} : List (α × β × γ) → List α × List β × List γ
  | abc => let (a,bc) := abc.unzip
    (a,bc.unzip)

def freshVar (vars : List String) : String := Id.run do
  let mut idx := vars.length
  let mut fresh := s!"v{idx}"
  while vars.contains fresh do
    idx := idx + 1
    fresh := s!"v{idx}"
  return fresh

-- Here we simplify a single Sexp in an auxilariy function. We return the
-- obtained mapping and also the rest of the expressions with the substitution
-- in-place.
partial def simplifySingleSexp : (Sexp → List String) → Sexp → List (List Sexp)
  → Sexp × VariableMapping × List (List Sexp)
  -- If we actually get to atoms there's nothing left to simplify, so trivial.
  | _, exp@(.atom _), other => (exp, [], other)
  -- We use the second argument, `other`, as some sort of stack for other
  -- expressions that should be simplified as well.
  | varfun, exp@(.list subexps), other =>
    let restVars := List.join $ other.join.map varfun
    -- try to substitute (both in the done and new
    let fresh := freshVar (exp.vars ++ restVars)
    let substituted := other.map
      λ subExps => subExps.map
        λ otherExp => replaceTerm exp (Sexp.atom fresh) otherExp
    -- check if we broke something
    let substitutedVars := substituted.map (λ subExps => subExps.map varfun)
      |>.join.unique.join.unique -- collect all unique variables
    --dbg_trace (s!"{(varfun exp)}.all λ v => !{substitutedVars}.contains v ="
    --  ++ s!"{(varfun exp).all λ v => !substitutedVars.contains v}")
    if (varfun exp).all λ v => !substitutedVars.contains v
      -- we didn't? Then it's safe to substitute!
      then
        (Sexp.atom fresh, [(fresh, exp)], substituted)
      else -- can't substitute, recurse on subexpressions
      match subexps with
        | [] => (exp, [], other) -- nothing to substitute
        | headSubexp::tailSubexps => Id.run do
          let mut mapping := []
          let mut curSubexp := headSubexp
          let mut curSubstituted := []::tailSubexps::other
          let mut finished := false
          while !finished do
            let new := simplifySingleSexp varfun curSubexp curSubstituted
            mapping := mapping ++ new.2.1
            let newDone::remainingSubexps::newOther := new.2.2
              | panic! "lost some subexpressions along the way?!"
            if let newSubexp::newTail := remainingSubexps then
               curSubexp := newSubexp
               curSubstituted := (newDone ++ [new.1])::newTail::newOther
            else -- nothing remaning
              finished := true
              curSubstituted := (newDone ++ [new.1])::newOther
          (Sexp.list curSubstituted.head!,mapping,curSubstituted.tail!)

partial def simplifySExpsAux : (Sexp → List String) → List Sexp → VariableMapping → List Sexp →  List Sexp × VariableMapping
  | _, [], mapping, done => (done, mapping)
  | varfun, sexp::rest, mapping, done =>
    let (newSexp,newMapping, substituted) := simplifySingleSexp varfun sexp [done, rest]
    match substituted with
      | [newDone,newRest] =>
        simplifySExpsAux varfun newRest (mapping ++ newMapping) (newDone ++ [newSexp])
      | _ => panic! ""

def simplifySexps : List Sexp → List Sexp × VariableMapping
  | sexps =>
    let fvars := sexps.map (λ exp => exp.fvars.unique) |>.join.unique
    let consts := sexps.map (λ exp => exp.consts.unique) |>.join.unique
    let initialSubst := Id.run do
      let mut allVars := sexps.map (λ exp => exp.vars.unique) |>.join.unique
      let mut mapping := []
      let mut exps := sexps
      for fvar in fvars do
        let vname := freshVar allVars
        mapping := (vname,fvar)::mapping
        allVars := vname::allVars
        exps := exps.map λ exp => replaceTerm fvar (Sexp.atom vname) exp
      for c in consts do
        let vname := freshVar allVars
        mapping := (vname,c)::mapping
        allVars := vname::allVars
        exps := exps.map λ exp => replaceTerm c (Sexp.atom vname) exp
      return (exps, mapping)
  simplifySExpsAux Sexp.selectStr initialSubst.1 initialSubst.2 []

def Sexp.unsimplify : Sexp →  VariableMapping → Sexp
  | sexp, mapping => sexp.vars.foldl (init := sexp)
    λ e var => match mapping.lookup var with
      | none => e
      | some subexp => replaceTerm (Sexp.atom var) subexp e

def unsimplifySExps : List Sexp →  VariableMapping → List Sexp
  | sexps, mapping => sexps.map
    λ exp => exp.vars.foldl (init := exp)
      λ e var => match mapping.lookup var with
        | none => e
        | some subexp => replaceTerm (Sexp.atom var) subexp e


def ab := parseSingleSexp "(a b)" |>.toOption |>.get!
def aab := parseSingleSexp "(a (a b))" |>.toOption |>.get!
def c := Sexp.atom "c"
def a := Sexp.atom "a"
#eval ab.toString
#eval replaceTerm ab c ab |>.toString
#eval replaceTerm ab c aab |>.toString
#eval replaceTerm a c aab |>.toString
#eval replaceTerm ab c aab |> replaceTerm c ab |>.toString

def realexample := parseSexpList "(ap (ap (ap (ap (ap (ap (const (str (str anonymous HSub) hSub) (levels (zero zero zero))) (const (str anonymous Int) nolevels)) (const (str anonymous Int) nolevels)) (const (str anonymous Int) nolevels)) (ap (ap (const (str anonymous instHSub) (levels (zero))) (const (str anonymous Int) nolevels)) (const (str (str anonymous Int) instSubInt) nolevels))) (fvar (num (str anonymous _uniq) 117))) (fvar (num (str anonymous _uniq) 117))) (ap (ap (ap (ap (ap (ap (const (str (str anonymous HSub) hSub) (levels (zero zero zero))) (const (str anonymous Int) nolevels)) (const (str anonymous Int) nolevels)) (const (str anonymous Int) nolevels)) (ap (ap (const (str anonymous instHSub) (levels (zero))) (const (str anonymous Int) nolevels)) (const (str (str anonymous Int) instSubInt) nolevels))) (fvar (num (str anonymous _uniq) 118))) (fvar (num (str anonymous _uniq) 118))) (ap (ap (ap (ap (ap (ap (const (str (str anonymous HSub) hSub) (levels (zero zero zero))) (const (str anonymous Int) nolevels)) (const (str anonymous Int) nolevels)) (const (str anonymous Int) nolevels)) (ap (ap (const (str anonymous instHSub) (levels (zero))) (const (str anonymous Int) nolevels)) (const (str (str anonymous Int) instSubInt) nolevels))) ?_uniq.121) ?_uniq.121) (ap (ap (ap (const (str (str anonymous OfNat) ofNat) (levels (zero))) (const (str anonymous Int) nolevels)) (litNat 0)) (ap (const (str (str anonymous Int) instOfNatInt) nolevels) (litNat 0)))" |>.toOption |>.get!
#eval realexample.map Sexp.selectStr
def realexampleSimplified := simplifySexps realexample
#eval realexampleSimplified.1.toString
#eval realexampleSimplified.2.map λ (s,sexp) => (s,sexp.toString)
#eval realexampleSimplified.1.map (Sexp.unsimplify · realexampleSimplified.2) |>.zip realexample |>.map λ (a,b) => a == b
def exp1 := parseSexpList "(a (a b)) (b (a b))" |>.toOption |>.get!
def exp2 := parseSexpList "(c (a b)) ((a b) c)" |>.toOption |>.get!
def exp3 := parseSexpList "(d ((a b) c)) (((a b) c) d)" |>.toOption |>.get!
def simp1 := simplifySexps exp1
def simp2 := simplifySexps exp2
def simp3 := simplifySexps exp3

#eval simp1.1 |>.map Sexp.toString
#eval simp2.1 |>.map Sexp.toString
#eval simp3.1 |>.map Sexp.toString

#eval unsimplifySExps simp1.1 simp1.2 == exp1
#eval unsimplifySExps simp2.1 simp2.2 == exp2
#eval unsimplifySExps simp3.1 simp3.2 == exp3

#eval aab.containsSubexpr a
#eval aab.containsSubexpr ab
#eval aab.containsSubexpr c

#eval parseSexpList ""
#eval parseSexpList "(a, b)"
#eval parseSexpList "(a, "
#eval parseSexpList "a)"
#eval parseSexpList "a b c"
#eval parseSexpList "(a b) (c d)"
#eval parseSingleSexp "(a b)"
#eval parseSingleSexp "(a (b c) d)"
