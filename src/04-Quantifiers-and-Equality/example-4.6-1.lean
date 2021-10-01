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

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry