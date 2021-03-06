-- 6.4 Attributes

variable {α : Type*}

def is_prefix (l₁ : list α) (l₂ : list α ) : Prop :=
∃ t, l₁ ++ t = l₂

infix ` <+: `:50 := is_prefix

attribute [simp]
theorem list.is_prefix_refl (l : list α) : l <+: l :=
⟨[], by simp⟩

example : [1, 2, 3] <+: [1, 2, 3] := by simp

@[simp]
theorem list.is_prefix_refl' (l : list α) : l <+: l :=
⟨[], by simp⟩

theorem list.is_prefix_refl'' (l : list α) : l <+: l :=
⟨[], by simp⟩

attribute [simp] list.is_prefix_refl''
