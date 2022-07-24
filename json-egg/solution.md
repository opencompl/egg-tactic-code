- Create a separate e-graph with a term, then apply the rule to match against
  the e-graph. Then find the match at the head node.

- If we have 1 = (mul (?a (inv ?a))), we can directly modify the e-graph and
  set up an equivalence between the LHS and the RHS.


- Enumerate the e-class for LHS and RHS if we don't have the equality, then
  show the end-user the variants of the LHS and the RHS.

- Generate lemmas for all the "obvious" equalities.

- Sketches? Skip steps in a proof?

- rule scheduling to decide when to run different rules.
- iteration limit, node limit, time limit.
