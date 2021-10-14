import data.nat.basic

example (u w x y z : ℕ) (h₁ : x = y + z) (h₂ : w = u + x) :
  w = z + y + u :=
by simp [*, add_assoc, add_comm, add_left_comm]

variables (p q r : Prop)

example (hp : p) : p ∧ q ↔ q :=
by simp *

example (hp : p) : p ∨ q :=
by simp *

example (hp : p) (hq : q) : p ∧ (q ∨ r) :=
by simp *
