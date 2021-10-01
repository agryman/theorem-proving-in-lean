-- 4.5 More on the Proof Language

variable f : ℕ → ℕ
variable h : ∀ x : ℕ, f x ≤ f (x + 1)

example : f 0 ≤ f 3 :=
have f 0 ≤ f 1, from h 0,
have f 0 ≤ f 2, from le_trans this (h 1),
show f 0 ≤ f 3, from le_trans this (h 2)

example : f 0 ≤ f 3 :=
have f 0 ≤ f 1, from h 0,
have f 0 ≤ f 2, from le_trans (by assumption) (h 1),
show f 0 ≤ f 3, from le_trans (by assumption) (h 2)

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
assume : f 0 ≥ f 1,
assume : f 1 ≥ f 2,
have f 0 ≥ f 2, from le_trans this ‹ f 0 ≥ f 1 ›,
have f 0 ≤ f 2, from le_trans (h 0) (h 1),
show f 0 = f 2, from le_antisymm this ‹ f 0 ≥ f 2 › 

example : f 0 ≤ f 3 :=
have f 0 ≤ f 1, from h 0,
have f 1 ≤ f 2, from h 1,
have f 2 ≤ f 3, from h 2,
show f 0 ≤ f 3, from le_trans ‹ f 0 ≤ f 1 › (le_trans ‹ f 1 ≤ f 2 › ‹ f 2 ≤ f 3 › )

example (n : ℕ) : ℕ := ‹ℕ›

example : f 0 ≥ f 1 → f 0 = f 1 :=
assume : f 0 ≥ f 1,
show f 0 = f 1, from le_antisymm (h 0) this

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
assume : f 0 ≥ f 1,
assume : f 1 ≥ f 2,
have f 0 ≥ f 2, from le_trans ‹f 2 ≤ f 1› ‹f 1 ≤ f 0›,
have f 0 ≤ f 2, from le_trans (h 0) (h 1),
show f 0 = f 2, from le_antisymm this ‹f 0 ≥ f 2› 
