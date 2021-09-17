-- Logical Equivalance

variables p q : Prop

theorem and_swap : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume h : p ∧ q,
    show q ∧ p, from and.intro h.right h.left)
  (assume h : q ∧ p,
    show p ∧ q, from ⟨ h.right, h.left ⟩)

#check and_swap p q

variable h : p ∧ q
example : q ∧ p := iff.mp (and_swap p q) h

theorem and_swap' : p ∧ q ↔ q ∧ p :=
⟨λ h : p ∧ q, ⟨ h.right, h.left ⟩ , λ h : q ∧ p, ⟨ h.right, h.left ⟩ ⟩ 

example (h : p ∧ q) : q ∧ p := (and_swap' p q).mp h

