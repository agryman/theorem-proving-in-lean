-- 5.8 Exercises
-- #2
-- Use tactic combinators to obtain a one line proof of the following:

example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
begin
  split, left, assumption,
  split, right, left, assumption,
  right, right, assumption,
end
