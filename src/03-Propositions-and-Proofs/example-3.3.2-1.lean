-- Disjunction

variables p q : Prop

example (hp : p) : p ∨ q := or.intro_left q hp
example (hq : q) : p ∨ q := or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
or.elim h
  (assume hp : p,
    show q ∨ p, from or.intro_right q hp)
  (assume hq : q,
    show q ∨ p, from or.intro_left p hq)

example (h : p ∨ q) : q ∨ p :=
or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq)

example (h : p ∨ q) : q ∨ p :=
h.elim
  (assume hp : p, or.inr hp)
  (assume hq : q, or.inl hq)
