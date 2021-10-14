import algebra.ring

variables {α : Type*} [comm_ring α]

local attribute [simp] mul_comm mul_assoc mul_left_comm
local attribute [simp] add_assoc add_comm add_left_comm

example (x y z : α) : (x - x) * y + z = z :=
begin simp end

example (x y z w : α) : x * y + z * w * x = x * w * z + y * x :=
by simp

def f (m n : ℕ) : ℕ := m + n + m

example {m n : ℕ} (h : n = 1) (h' : 0 = m) : (f m n) = n :=
by simp [h, h'.symm, f]
