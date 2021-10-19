section
variables (x y z : ℕ)
variables (h₁ : x = y) (h₂ : y = z)

section
variables {x y z}
include h₁ h₂
theorem foo : x = z :=
begin
  rw [h₁, h₂]
end
end

theorem bar : x = z :=
eq.trans h₁ h₂

variable {x}
theorem baz : x = x := rfl

#check @foo
#check @bar
#check @baz

end

section
parameters {α : Type*} (r : α → α → Prop)
parameter transr : ∀ {x y z}, r x y → r y z → r x z

variables {a b c d e : α}

theorem t1 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) : r a d :=
transr (transr h₁ h₂) h₃

theorem t2 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) (h₄ : r d e): r a e :=
transr h₁ (t1 h₂ h₃ h₄)

#check t1
#check t2
end

#check t1
#check t2
