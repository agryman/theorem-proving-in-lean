example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    apply or.elim (and.right h),
      intro hq,
      apply or.inl,
      apply and.intro,
        exact and.left h,
      exact hq,
    intro hr,
    apply or.inr,
    apply and.intro,
      exact and.left h,
    exact hr,
  intro h,
  apply or.elim h,
  intro hpq,
  apply and.intro,
    exact and.left hpq,
  apply or.inl,
    exact and.right hpq,
  intro hpr,
  apply and.intro,
    exact and.left hpr,
  apply or.inr,
    exact and.right hpr,
end

example (α : Type*) : α → α :=
begin
  intro a,
  exact a,
end

example (α : Type*) : ∀ x : α, x = x :=
begin
  intro x,
  exact eq.refl x,
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros a b c h₁ h₂,
  exact eq.trans (eq.symm h₂) h₁,
end

variables x y z w : ℕ

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
begin 
  apply eq.trans h₁,
  apply eq.trans h₂,
  assumption,
end

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
begin
  apply eq.trans,
  assumption,
  apply eq.trans,
  assumption,
  assumption,
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  apply eq.trans,
  apply eq.symm,
  assumption,
  assumption,
end

example (y : ℕ) : (λ x : ℕ, 0) y = 0 :=
begin
  refl,
end

example (x : ℕ) : x ≤ x :=
begin
  refl,
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  transitivity,
  symmetry,
  assumption,
  assumption,
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros a b c h₁ h₂,
  transitivity a,
  symmetry,
  assumption,
  assumption,
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  transitivity,
  symmetry,
  repeat {assumption},
end

example : ∃ a : ℕ, 5 = a :=
begin
    apply exists.intro,
    reflexivity,
end

example : ∃ a : ℕ, a = a :=
begin
    fapply exists.intro,
    exact 0,
    reflexivity,
end

example (x : ℕ) : x = x :=
begin
  revert x,
  intro y,
  reflexivity,
end

example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert h,
  intro h₁,
  symmetry,
  assumption,
end

example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert x,
  intros,
  symmetry,
  assumption,
end

example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert x y,
  intros,
  symmetry,
  assumption,
end

example : 3 = 3 :=
begin
  generalize : 3 = x,
  revert x,
  intro y,
  reflexivity,
end

example : 2 + 3 = 5 :=
begin
  generalize : 3 = x,
  sorry,
end

example : 2 + 3 = 5 :=
begin
  generalize h : 3 = x,
  rw ←h,
end