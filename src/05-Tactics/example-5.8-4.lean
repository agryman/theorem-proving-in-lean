-- 5.8 Exercises
-- #1

-- 4.6 Exercises
-- #1

variables (α : Type*) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
begin
  apply iff.intro,
    intro h,
    split,
      intro a,
      have hpq : p a ∧ q a := h a,
      cases hpq with hp hq,
      assumption,
    intro a,
    have hpq : p a ∧ q a := h a,
    cases hpq with hp hq,
    assumption,
  intro h,
  cases h with hp hq,
  intro a,
  split,
    exact hp a,
  exact hq a,
end

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
begin
  intro h,
  intro hp,
  intro a,
  have hpq : p a → q a := h a,
  have hpa : p a := hp a,
  apply hpq,
  assumption,
end

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
begin
  intros h a,
  cases h with hp hq,
    left,
    exact hp a,
  right,
  exact hq a,
end
