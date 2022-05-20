
inductive AST : Type where
| mul : AST → AST → AST
| inv : AST → AST
| symbol : String → AST
| rewrite : String → AST → AST
| seq : AST → AST → AST
| const : Nat → AST

declare_syntax_cat eggExpr
syntax "(" "*" eggExpr eggExpr ")" : eggExpr
syntax "(" "^-1" eggExpr ")" : eggExpr
syntax "(" "Rewrite" "<=" ident eggExpr ")" : eggExpr
syntax "(" "Rewrite" "=>" ident eggExpr ")" : eggExpr
syntax eggExpr "," eggExpr : eggExpr
-- syntax "(" eggExpr ")" : eggExpr
syntax ident : eggExpr
syntax num : eggExpr

-- auxiliary notation for translating `eggExpr` into `term`
syntax "`[Egg| " eggExpr "]" : term
macro_rules
| `(`[Egg| (* $x:eggExpr $y:eggExpr) ]) => `(AST.mul `[Egg| $x] `[Egg| $y])
| `(`[Egg| (^-1 $x:eggExpr) ]) => `(AST.inv `[Egg| $x])
-- | `(`[Egg| ( $x:eggExpr ) ]) => `[Egg| $x]
| `(`[Egg| $x:ident ]) => `(AST.symbol  $(Lean.quote (toString x.getId)))
| `(`[Egg| (Rewrite<= $x:ident $y:eggExpr) ]) => `(AST.rewrite ("<=" ++ $(Lean.quote (toString x.getId))) `[Egg| $y])
| `(`[Egg| (Rewrite => $x:ident $y:eggExpr) ]) => `(AST.rewrite ("=>" ++ $(Lean.quote (toString x.getId))) `[Egg| $y])
| `(`[Egg| $x , $y ]) => `(AST.seq `[Egg| $x] `[Egg| $y])
| `(`[Egg| $num:numLit ]) => `(AST.const $num )

def pretty_print : AST → String
 | AST.mul x y => "(" ++ (pretty_print x) ++ ") * (" ++ (pretty_print y) ++ ")"
 | AST.inv x => "(" ++ (pretty_print x) ++ ")^{-1}"
 | AST.rewrite _ x => pretty_print x
 | AST.symbol x => x
 | AST.const x => toString x
 | AST.seq x y => (pretty_print x) ++ " → " ++ (pretty_print y)

-- #check `[Egg| (* a b)]
#eval pretty_print `[Egg| (* a b)]

def rewrite : AST := `[Egg| (^-1 (* a b))
, (Rewrite=> one_mul' (* 1 (^-1 (* a b))))
, (* 1 (Rewrite=> one_mul' (* 1 (^-1 (* a b)))))
, (Rewrite=> assoc_mul (* (* 1 1) (^-1 (* a b))))
, (* (Rewrite<= one_mul' 1) (^-1 (* a b)))
, (* (Rewrite=> inv_left'' (* (^-1 b) b)) (^-1 (* a b)))
, (Rewrite=> assoc_mul' (* (^-1 b) (* b (^-1 (* a b)))))
, (* (Rewrite=> mul_one' (* (^-1 b) 1)) (* b (^-1 (* a b))))
, (Rewrite=> assoc_mul' (* (^-1 b) (* 1 (* b (^-1 (* a b))))))
, (* (^-1 b) (* (Rewrite=> inv_right'' (* b (^-1 b))) (* b (^-1 (* a b)))))
, (* (^-1 b) (Rewrite<= assoc_mul (* b (* (^-1 b) (* b (^-1 (* a b)))))))
, (* (^-1 b) (* b (Rewrite<= assoc_mul' (* (* (^-1 b) b) (^-1 (* a b))))))
, (* (^-1 b) (* b (* (Rewrite<= inv_left'' 1) (^-1 (* a b)))))
, (* (^-1 b) (* b (* (Rewrite=> one_mul' (* 1 1)) (^-1 (* a b)))))
, (* (^-1 b) (* b (Rewrite<= assoc_mul (* 1 (* 1 (^-1 (* a b)))))))
, (* (^-1 b) (* b (* 1 (Rewrite<= one_mul' (^-1 (* a b))))))
, (* (^-1 b) (* b (Rewrite<= one_mul' (^-1 (* a b)))))
, (* (^-1 b) (* (Rewrite=> one_mul' (* 1 b)) (^-1 (* a b))))
, (* (^-1 b) (* (* 1 (Rewrite=> one_mul' (* 1 b))) (^-1 (* a b))))
, (* (^-1 b) (* (Rewrite=> assoc_mul (* (* 1 1) b)) (^-1 (* a b))))
, (* (^-1 b) (* (* (Rewrite<= one_mul' 1) b) (^-1 (* a b))))
, (* (^-1 b) (* (* (Rewrite=> inv_left' (* (^-1 a) a)) b) (^-1 (* a b))))
, (* (^-1 b) (* (Rewrite=> assoc_mul' (* (^-1 a) (* a b))) (^-1 (* a b))))
, (* (^-1 b) (Rewrite=> assoc_mul' (* (^-1 a) (* (* a b) (^-1 (* a b))))))
, (* (^-1 b) (* (^-1 a) (Rewrite=> inv_right 1)))
, (* (^-1 b) (Rewrite<= mul_one' (^-1 a)))
]

def rewrite2 : AST := `[Egg|
(^-1 (^-1 a))
,(Rewrite=> mul_one' (* (^-1 (^-1 a)) 1))
,(* (Rewrite=> mul_one' (* (^-1 (^-1 a)) 1)) 1)
,(Rewrite=> assoc_mul' (* (^-1 (^-1 a)) (* 1 1)))
,(* (Rewrite=> one_mul' (* 1 (^-1 (^-1 a)))) (* 1 1))
,(* (* 1 (Rewrite=> one_mul' (* 1 (^-1 (^-1 a))))) (* 1 1))
,(* (Rewrite=> assoc_mul (* (* 1 1) (^-1 (^-1 a)))) (* 1 1))
,(* (* (Rewrite<= one_mul' 1) (^-1 (^-1 a))) (* 1 1))
,(* (* (Rewrite=> inv_right' (* a (^-1 a))) (^-1 (^-1 a))) (* 1 1))
,(* (Rewrite=> assoc_mul' (* a (* (^-1 a) (^-1 (^-1 a))))) (* 1 1))
,(* (* a (* (^-1 a) (^-1 (^-1 a)))) (Rewrite<= one_mul' 1))
,(Rewrite=> assoc_mul' (* a (* (* (^-1 a) (^-1 (^-1 a))) 1)))
,(* a (Rewrite<= assoc_mul (* (^-1 a) (* (^-1 (^-1 a)) 1))))
,(* a (* (^-1 a) (Rewrite<= mul_one' (^-1 (^-1 a)))))
,(* a (Rewrite=> inv_right 1))
,(* a (Rewrite=> one_mul' (* 1 1)))
,(Rewrite<= assoc_mul' (* (* a 1) 1))
,(* (Rewrite<= mul_one' a) 1)
,(Rewrite<= mul_one' a)
]
#eval pretty_print rewrite
#eval pretty_print rewrite2

class group (G : Type) extends has_mul G,
    has_one G, has_inv G :=
  (mul_asoc : ∀ (a b c : G),
   a * b * c = a * (b * c))
  (one_mul : ∀ (a : G), 1 * a = a)
  (mul_one : ∀ (a : G), a * 1 = a)
  (mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)
  (mul_right_inv : ∀ (a : G), a * a⁻¹ = 1)
