#check let y := 2 + 2 in y * y
#reduce let y := 2 + 2 in y * y

def t (x : ℕ) : ℕ :=
  let y := x + x in y * y

#check t
#reduce t 2
#reduce t 3

#check let y := 2 + 2, z := y + y in z * z 
#reduce let y := 2 + 2, z := y + y in z * z

def foo := let a := nat in λ x : a, x + 2
#check foo

-- fails to type check because a cannot be infered within (λ a, λ x : a, x + 2)
-- def bar := (λ a, λ x : a, x + 2) nat