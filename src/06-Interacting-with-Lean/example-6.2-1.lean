import data.nat.basic

section
variables x y : ℕ

def double := x + x

#check double
#check double (2 * x)

local attribute [simp] add_assoc add_comm add_left_comm

theorem t1 : double (x + y) = double x + double y :=
by simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y :=
by simp [double, add_mul]

end

section
variables (x y z : ℕ)
variables (h₁ : x = y) (h₂ : y = z)

include h₁ h₂
theorem foo : x = z :=
begin
  rw [h₁, h₂],
end
omit h₁ h₂

theorem bar : x = z :=
eq.trans h₁ h₂

theorem baz : x = x := rfl

#check @foo
#check @bar 
#check @baz

end
