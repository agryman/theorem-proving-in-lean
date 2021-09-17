-- Examples of Propositional Validities

open classical

variables p q r : Prop

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro 
  (assume h : p ∧ (q ∨ r),
    have hp : p, from h.left,
    or.elim (h.right)
    (assume hq : q,
      show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨hp, hq⟩)
    (assume hr : r,
      show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨hp, hr⟩))
  (assume h : p ∧ q ∨ p ∧ r,
      show p ∧ (q ∨ r), from
        or.elim h
        (assume hpq : p ∧ q,
          show p ∧ (q ∨ r), from ⟨hpq.left, or.inl hpq.right⟩)
        (assume hpr : p ∧ r,
          show p ∧ (q ∨ r), from ⟨hpr.left, or.inr hpr.right⟩))

-- an example that requires classical thinking
example : ¬ (p ∧ ¬ q) → (p → q) :=
assume h : ¬ (p ∧ ¬ q),
assume hp : p,
show q, from
  or.elim (em q)
    (assume hq : q, hq)
    (assume hnq : ¬ q, false.elim (h (and.intro hp hnq)))
