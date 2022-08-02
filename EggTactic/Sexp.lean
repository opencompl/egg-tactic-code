import Lean
open Lean

inductive Sexp
| atom: Substring → Sexp
| list: Substring → List Sexp → Sexp
deriving BEq, Inhabited, Repr

inductive SexpTok
| sexp: Sexp →  SexpTok
| opening: String.Pos → SexpTok
deriving BEq, Inhabited, Repr


structure SexpState where 
  it: String.Iterator
  stack: List SexpTok := []
deriving BEq, Repr

def SexpState.fromString (s: String): SexpState :=
  { it := s.iter, stack := [] : SexpState }

-- abbrev SexpTokStack := List SexpTok

-- Remove elements from the stack of tokens `List SexpToken` till we find a `SexpToken.opening`.
-- When we do, return (1) the position of the open paren, (2) the list of SexpTokens left on the stack, and (3) the list of Sexps
-- Until then, accumulate the `SexpToken.sexp`s into `sexps`.
def stackPopTillOpen (toks: List SexpTok) (sexps: List Sexp := []): Option (String.Pos × (List SexpTok)) × (List Sexp) := 
  match toks with 
  | [] => (.none, sexps)
  | SexpTok.opening openPos :: rest => (.some (openPos, rest), sexps)
  | SexpTok.sexp s :: rest => stackPopTillOpen rest (s :: sexps)
  

instance : Inhabited SexpState where 
  default := SexpState.fromString ""


inductive SexpError
| unmatchedOpenParen (ix: String.Iterator): SexpError
| unmatchedCloseParen (ix: String.Iterator): SexpError
deriving BEq, Repr

instance : ToString SexpError where toString := λ err => match err with
  | .unmatchedOpenParen ix => s!"Unmatched open parenthesis at {ix}"
  | .unmatchedCloseParen ix => s!"Unmatched close parenthesis at {ix}"

abbrev SexpM := EStateM SexpError SexpState 


def SexpM.peek: SexpM (Option (Char × String.Pos)) := do 
  let state ← get
  return if state.it.atEnd then .none else .some (state.it.curr, state.it.i)

def SexpM.curPos: SexpM String.Pos := do
  let state ← get
  return state.it.i

-- Stop is a good name, because it indicates that it's exclusive
def SexpM.mkSubstring (l: String.Pos) (r: String.Pos): SexpM Substring := do
  let state ← get
  return { str := state.it.s, startPos := l, stopPos := r}


def SexpM.advance: SexpM Unit := do 
  modify (fun state => { state with it := state.it.next })

def SexpM.push (tok: SexpTok): SexpM Unit := do 
  modify (fun state => { state with stack := tok :: state.stack })


instance [Inhabited α] : Inhabited (SexpM α) where 
  default := do return default


def SexpM.pop: SexpM SexpTok := do 
  let state ← get
  match state.stack with 
  | [] => panic! "empty stack"
  | x::xs => do 
      set { state with stack := xs }
      return x


-- collapse the current stack till the last ( into a single Sexp.list
def SexpM.matchClosingParen: SexpM (List Sexp) := do
  let state ← get
  match stackPopTillOpen state.stack with 
  | (.some (openPos, toks), sexps) => 
    let substr := Substring.mk state.it.s openPos state.it.i
    set { state with stack := SexpTok.sexp (Sexp.list substr sexps) :: toks }
    return sexps
  | (.none, _) => throw (SexpError.unmatchedCloseParen state.it)


partial def SexpM.takeString (startPos: String.Pos): SexpM Substring := do 
  match (← SexpM.peek) with 
  | .none => SexpM.mkSubstring startPos (← SexpM.curPos)
  | .some (' ', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | .some ('(', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | .some (')', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | .some _ => do 
     SexpM.advance 
     SexpM.takeString startPos

partial def SexpM.parse: SexpM (List Sexp) := do 
  match (← SexpM.peek) with 
  | .some  ('(', i) => do 
     SexpM.advance
     SexpM.push (SexpTok.opening i)
     SexpM.parse
  | .some (')', _) => do 
     SexpM.advance
     let cur ← SexpM.matchClosingParen
     let rest ← SexpM.parse
     return cur ++ rest
  | .some (' ', _) => do 
      SexpM.advance
      SexpM.parse
  | .some (_, i) => do
      let s ← SexpM.takeString i
      SexpM.push (SexpTok.sexp (Sexp.atom s))
      SexpM.parse
  | .none => do
      let state ← get
      match stackPopTillOpen state.stack with
      | (.some (openPos, _), _) => 
          throw <| SexpError.unmatchedOpenParen ({ s := state.it.s, i := openPos : String.Iterator })
      | (.none, sexps) => return sexps

def parseSexp (s: String):  Except SexpError (List Sexp) :=
  let initState := SexpState.fromString s
  match EStateM.run SexpM.parse initState with
  | .ok v _ => .ok v
  | .error e _ => .error e

#eval parseSexp ""
#eval parseSexp "(a, b)"
#eval parseSexp "(a, "
#eval parseSexp "a)"
#eval parseSexp "a b c"
#eval parseSexp "(a b) (c d)"
