-- 5.8 Exercises
-- #1

-- 3.7 Exercises
-- #2

open classical

variables p q r s : Prop

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
begin
  intro h,
  cases (em r) with hr hnr,
    left,
    intro hp,
    assumption,
  cases (em s) with hs hns,
    right,
    intro hp,
    assumption,
  cases (em p) with hp hnp,
    have hrs : r ∨ s := h hp,
    cases hrs with hr hs,
      left,
      intro hp',
      assumption,
    right,
    intro hp',
    assumption,
  left,
  intro hp,
  exfalso,
  apply hnp,
  assumption,
end

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
begin
  intro h,
  cases (em p) with hp hnp,
    cases (em q) with hq hnq,
      exfalso,
      exact h ⟨hp, hq⟩,
    right,
    assumption,
  left,
  assumption, 
end

example : ¬(p → q) → p ∧ ¬q := 
begin
  intro h,
  cases (em p) with hp hnp,
    cases (em q) with hq hnq,
      exfalso,
      apply h,
      intro hp',
      assumption,
    exact ⟨hp, hnq⟩,
  exfalso,
  apply h,
  intro hp',
  contradiction,
end

example : (p → q) → (¬p ∨ q) :=
begin
  intro h,
  cases (em q) with hq hnq,
    right,
    assumption,
  cases (em p) with hp hnp,
    right,
    apply h,
    assumption,
  left,
  assumption,
end

example : (¬q → ¬p) → (p → q) :=
begin
  intros h hp,
  cases (em q) with hq hnq,
    assumption,
    have hnp : ¬ p := h hnq,
    contradiction,
end

example : p ∨ ¬p :=
begin
  exact em p,
end

example : (((p → q) → p) → p) :=
begin
  intro h,
  cases (em p) with hp hnp,
    assumption,
  apply h,
  intro hp,
  contradiction,
end
