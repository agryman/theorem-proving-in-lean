-- Exercises
-- #2

open classical

variables p q r s : Prop

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
assume h : p → r ∨ s,
show (p → r) ∨ (p → s),
from or.elim (em p)
  (assume hp : p,
    have hrs : r ∨ s := h hp,
    or.elim hrs
    (assume hr : r, or.inl (λ hp' : p, hr))
    (assume hs : s, or.inr (λ hp' : p, hs))
  )
  (assume hnp : ¬p,
    or.inl (assume hp : p, show r, from absurd hp hnp)
  )

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  assume h : ¬(p ∧ q),
  show ¬p ∨ ¬q,
  from or.elim (em p)
  (assume hp : p,
    have hnq : ¬q,
    from (assume hq : q, h ⟨hp, hq⟩), 
    or.inr hnq
  )
  (assume hnp : ¬p, or.inl hnp)

-- I need lemma1 and dne to prove the next example
-- This seems too complicated.
-- Is there a shorter proof of ¬(p → q) → p ∧ ¬q?
lemma lemma1 {p q : Prop} (h : ¬q → ¬p) : p → q :=
  show p → q,
  from assume hp : p,
    or.elim (em q)
      (assume hq : q, hq)
      (assume hnq : ¬q, absurd hp (h hnq))

theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)

example : ¬(p → q) → p ∧ ¬q :=
assume h : ¬(p → q),
have hnq : ¬q := (λ hq : q, h (λ hp : p, hq)),
suffices hp : p, from ⟨hp, hnq⟩,
show p, 
from have hdnp : ¬¬p :=
  (assume hnp: ¬p,
    have hnqnp : ¬q → ¬p := (λ hnq' : ¬q, hnp),
    have hpq : p → q := lemma1 hnqnp,
    show false, from (h hpq)
  ),
  dne hdnp

example : (p → q) → (¬p ∨ q) :=
assume h : p → q,
or.elim (em p)
(assume hp : p, or.inr (h hp))
(assume hnp : ¬p, or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
assume h : ¬q → ¬p, lemma1 h

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
assume h : (p → q) → p,
or.elim (em q)
(assume hq : q, h (assume hp : p, hq))
(assume hnq : ¬q,
  dne (assume hnp: ¬p,
    have hnqnp : ¬q → ¬p := (λ hnq', hnp),
    have hpq : p → q := lemma1 hnqnp,
    show false,
    from hnp (h hpq)
  )
)
