import data.nat.basic

variables (u w x x' y y' z : ℕ) (p : ℕ → Prop)

example (h₁ : x + 0 = x') (h₂ : y + 0 = y') :
  x + y + 0 = x' + y' :=
  by {simp at *, simp *}