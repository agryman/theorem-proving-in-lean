-- Negation and Falsity

variables p q r : Prop

example (hpq : p → q) (hnq : ¬ q) : ¬ p :=
assume hp : p,
show false, from hnq (hpq hp)

example (hp : p) (hnp : ¬ p) : q := false.elim (hnp hp)

example (hp : p) (hnp : ¬ p) : q := absurd hp hnp

example (hnp : ¬ p) (hq : q) (hqp : q → p) : r :=
absurd (hqp hq) hnp
