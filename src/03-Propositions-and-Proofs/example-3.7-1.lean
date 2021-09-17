-- Exercises
-- #1

variables p q r : Prop

-- commutativity of ∧ and ∨

example : p ∧ q ↔ q ∧ p :=
iff.intro
(show p ∧ q → q ∧ p, from
  assume h : p ∧ q, ⟨h.right, h.left⟩)
(show q ∧ p → p ∧ q, from
  assume h : q ∧ p, ⟨h.right, h.left⟩)

example : p ∨ q ↔ q ∨ p :=
iff.intro
(show p ∨ q → q ∨ p, from 
  assume h : p ∨ q, 
  show q ∨ p, from or.elim h
    (assume hp : p, or.inr hp)
    (assume hq : q, or.inl hq))
(show q ∨ p → p ∨ q, from
  assume h : q ∨ p,
  show p ∨ q, from or.elim h
    (assume hq : q, or.inr hq)
    (assume hp : p, or.inl hp))

-- associativity of ∧ and ∨

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro 
(assume h : (p ∧ q) ∧ r,
  have hpq : p ∧ q := h.left,
  have hp : p := hpq.left,
  have hq : q := hpq.right,
  have hr : r := h.right,
  ⟨hp, ⟨hq, hr⟩⟩)
(assume h : p ∧ (q ∧ r),
  have hp : p := h.left,
  have hqr : q ∧ r := h.right,
  have hq : q := hqr.left,
  have hr : r := hqr.right,
  show (p ∧ q) ∧ r, from ⟨ ⟨ hp, hq⟩, hr⟩
)

example : p ∨ (q ∨ r) ↔ (p ∨ q) ∨ r :=
iff.intro
(assume h : p ∨ (q ∨ r), 
  show (p ∨ q) ∨ r, 
  from or.elim h
    (assume hp : p, or.inl (or.inl hp))
    (assume hqr : q ∨ r, 
      show (p ∨ q) ∨ r,
      from or.elim hqr
        (assume hq : q, or.inl (or.inr hq))
        (assume hr : r, or.inr hr)
    )
)
(assume h : (p ∨ q) ∨ r,
  show p ∨ (q ∨ r),
  from or.elim h
    (assume hpq : p ∨ q,
      or.elim hpq
      (assume hp : p, or.inl hp)
      (assume hq : q, or.inr (or.inl hq))
    )
    (assume hr : r, or.inr (or.inr hr))
)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
iff.intro
(assume h : p ∧ (q ∨ r), 
  have hp : p := h.left,
  have hqr : q ∨ r := h.right,
  show (p ∧ q) ∨ (p ∧ r),
  from or.elim hqr
    (assume hq : q, or.inl ⟨hp, hq⟩)
    (assume hr : r, or.inr ⟨hp, hr⟩)
)
(assume h : (p ∧ q) ∨ (p ∧ r), 
  show p ∧ (q ∨ r),
  from or.elim h
    (assume hpq : p ∧ q, ⟨hpq.left, or.inl hpq.right⟩)
    (assume hpr : p ∧ r, ⟨hpr.left, or.inr hpr.right⟩)
)

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
iff.intro
(assume h : p ∨ (q ∧ r),
  show (p ∨ q) ∧ (p ∨ r),
  from or.elim h
    (assume hp : p, 
      ⟨or.inl hp, or.inl hp⟩
    )
    (assume hqr : q ∧ r, 
      have hq : q := hqr.left, 
      have hr : r := hqr.right,
      ⟨or.inr hq, or.inr hr⟩ 
    )
)
(assume h : (p ∨ q) ∧ (p ∨ r),
  have hpq : p ∨ q := h.left,
  have hpr : p ∨ r := h.right,
  show p ∨ (q ∧ r),
  from or.elim hpq
    (assume hp : p, or.inl hp)
    (assume hq : q, 
      or.elim hpr
        (assume hp : p, or.inl hp)
        (assume hr : r, or.inr ⟨hq, hr⟩)
    )
)

-- other properties

example : (p → (q → r)) ↔ (p ∧ q → r) :=
iff.intro
(assume h : p → (q → r),
  show p ∧ q → r,
  from assume hpq : p ∧ q,
    have hp : p := hpq.left,
    have hq : q := hpq.right,
    h hp hq 
)
(assume h : p ∧ q → r,
  show p → (q → r),
  from assume hp : p,
    assume hq : q,
    h ⟨hp, hq⟩ 
)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
iff.intro
(assume h : (p ∨ q) → r,
  have hpr : p → r := (assume hp : p, h (or.inl hp)),
  have hqr : q → r := (assume hq : q, h (or.inr hq)),
  show (p → r) ∧ (q → r),
  from ⟨hpr, hqr⟩ 
)
(assume h : (p → r) ∧ (q → r),
  have hpr : p → r := h.left,
  have hqr : q → r := h.right,
  show (p ∨ q) → r,
  from assume hpq : p ∨ q,
    or.elim hpq
    (assume hp : p, hpr hp)
    (assume hq : q, hqr hq)
)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro
(assume h : ¬(p ∨ q),
  show ¬p ∧ ¬q,
  from
    have hnp : ¬p := (assume hp : p, h (or.inl hp)),
    have hnq : ¬q := (assume hq : q, h (or.inr hq)),
    ⟨hnp, hnq⟩ 
)
(assume h : ¬p ∧ ¬q,
  have hnp : ¬ p := h.left,
  have hnq : ¬ q := h.right,
  show ¬(p ∨ q),
  from assume hpq : p ∨ q,
    or.elim hpq
    (assume hp : p, hnp hp)
    (assume hq : q, hnq hq)
)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
assume h : ¬p ∨ ¬q,
show ¬(p ∧ q),
from assume hpq : p ∧ q,
  have hp : p := hpq.left,
  have hq : q := hpq.right,
    or.elim h
    (assume hnp : ¬ p, hnp hp)
    (assume hnq : ¬ q, hnq hq)

example : ¬(p ∧ ¬p) :=
assume h : p ∧ ¬p,
have hp : p := h.left,
have hnp : ¬p := h.right,
show false,
from hnp hp

example : p ∧ ¬q → ¬(p → q) :=
assume h : p ∧ ¬q,
have hp : p := h.left,
have hnq : ¬q := h.right,
show ¬(p → q),
from assume hpq : p → q,
hnq (hpq hp)

example : ¬p → (p → q) :=
assume hnp : ¬p,
show p → q,
from assume hp : p,
absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
assume h : ¬p ∨ q,
assume hp : p,
show q,
from or.elim h
(assume hnp : ¬p, absurd hp hnp)
(assume hq : q, hq)

example : p ∨ false ↔ p :=
iff.intro
(assume h : p ∨ false,
  show p,
  from or.elim h
  (assume hp : p, hp)
  (assume hf : false, false.elim hf)
)
(assume hp : p,
  show p ∨ false,
  from or.inl hp
)

example : p ∧ false ↔ false :=
iff.intro
(assume h : p ∧ false, false.elim (h.right))
(assume hf : false, false.elim hf)

example : (p → q) → (¬q → ¬p) :=
assume h : p → q,
show ¬q → ¬p,
from
  assume hnq : ¬q,
  show ¬p,
  from
    assume hp : p,
    hnq (h hp)
