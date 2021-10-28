variable {α : Type*}

def is_prefix (l₁ : list α) (l₂ : list α) : Prop :=
∃ t, l₁ ++ t = l₂

#check is_prefix

def list_has_le : has_le (list α) := ⟨is_prefix⟩

#check list_has_le

#check has_le
#print has_le

section
local attribute [instance] list_has_le

theorem foo (l : list α) : l ≤ l := ⟨[], by simp⟩
end

-- theorem bar (l : list α) : l ≤ l := ⟨[], by simp⟩