-- 4.6 Exercises

-- #1

variables (α : Type*) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
(assume h: ∀ x, p x ∧ q x,
  have hp: ∀ x, p x := (assume a: α, (h a).left),
  have hq: ∀ x, q x := (assume a: α, (h a).right),
  show (∀ x, p x) ∧ (∀ x, q x),
  from ⟨hp, hq⟩ 
)
(assume h: (∀ x, p x) ∧ (∀ x, q x),
  have hp: ∀ x, p x := h.left,
  have hq: ∀ x, q x := h.right,
  show ∀ x, p x ∧ q x,
  from assume a: α, ⟨hp a, hq a⟩ 
)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
assume hapq: ∀ x, p x → q x,
assume hap: ∀ x, p x,
assume a: α, show q a, from (hapq a) (hap a)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
assume h: (∀ x, p x) ∨ (∀ x, q x),
assume a: α, show p a ∨ q a, from
or.elim h
(assume hap: ∀ x, p x, show p a ∨ q a, from or.inl (hap a))
(assume haq: ∀ x, q x, show p a ∨ q a, from or.inr (haq a))
