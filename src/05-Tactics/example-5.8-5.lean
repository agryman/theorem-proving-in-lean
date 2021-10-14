-- 5.8 Exercises
-- #1

-- 4.6 Exercises
-- #2

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
begin
  intro a,
  apply iff.intro,
    intro h,
    apply h,
    assumption,
  intro h,
  intro a',
  assumption,
end

open classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
begin
  apply iff.intro,
    intro h,
    cases (em r) with hr hnr,
      right,
      assumption,
    left,
    intro a,
    have ha : p a ∨ r := h a,
    cases ha with hpa hr,
      assumption,
    contradiction,
  intros h a,
  cases h with hp hr,
    left,
    exact hp a,
  right,
  assumption,
end

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
begin
  apply iff.intro,
    intros h hr a,
    exact (h a) hr,
  intros h a hr,
  exact (h hr) a,
end
