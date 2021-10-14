import data.list.basic

variable {α : Type*}

open list

example (xs : list ℕ) :
  reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs :=
by simp

example (xs ys : list α) :
  length (reverse (xs ++ ys)) = length xs + length ys :=
by simp [add_comm]

variables (x y z : ℕ) (p : ℕ → Prop)

example (h : p ((x + 0) * (0 + y * 1 + z * 0))) :
  p (x * y) :=
by { simp at h, assumption }
