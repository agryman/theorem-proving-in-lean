import data.nat.basic

theorem T2 
  (a b c d : ℕ)
  (h1 : a = b)
  (h2 : b ≤ c)
  (h3 : c + 1 < d) : a < d :=
calc
  a   = b     : h1
  ... < b + 1 : nat.lt_succ_self b
  ... ≤ c + 1 : nat.succ_le_succ h2
  ... < d     : h3

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
calc
  (x + y) * (x + y) = (x + y) * x + (x + y) * y : by rw mul_add
  ... = x * x + y * x + (x + y) * y             : by rw add_mul
  ... = x * x + y * x + (x * y + y * y)         : by rw add_mul
  ... = x * x + y * x + x * y + y * y           : by rw ←add_assoc

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
by rw [mul_add, add_mul, add_mul, ←add_assoc]

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
by simp [mul_add, add_mul, add_assoc, add_left_comm]
