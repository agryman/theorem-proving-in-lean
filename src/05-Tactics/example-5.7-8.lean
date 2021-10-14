import data.list.basic

open list

variables {α : Type*} (x y z : α) (xs ys zs : list α)

def mk_symm (xs : list α) := xs ++ reverse xs

theorem reverse_mk_symm (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by { unfold mk_symm, simp}

theorem reverse_mk_symm' (xs : list α) :
  let r := mk_symm xs in reverse r = r :=
by simp [mk_symm]

example (xs ys : list ℕ) :
  reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
by simp [reverse_mk_symm]

example (xs ys : list ℕ) (p : list ℕ → Prop)
  (h : p (reverse (xs ++ (mk_symm ys)))) :
  p (mk_symm ys ++ reverse xs) :=
by simp [reverse_mk_symm] at h; assumption

@[simp] theorem reverse_mk_symm'' (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by simp [mk_symm]

example (xs ys : list ℕ) :
  reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
by simp

example (xs ys : list ℕ) (p : list ℕ → Prop)
  (h : p (reverse (xs ++ (mk_symm ys)))) :
  p (mk_symm ys ++ reverse xs) :=
by simp at h; assumption

attribute [simp]
theorem reverse_mk_symm''' (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by simp [mk_symm]
