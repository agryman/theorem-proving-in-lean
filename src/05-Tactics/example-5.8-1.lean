-- 5.8 Exercises
-- #1

-- 3.7 Exercises
-- #1

variables p q r : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
begin
  apply iff.intro,
    intro h,
    cases h with hp hq,
    exact ⟨hq, hp⟩,
  intro h,
  cases h with hq hp,
  exact ⟨hp, hq⟩
end

example : p ∨ q ↔ q ∨ p :=
begin
  apply iff.intro,
    intro h,
    cases h with hp hq,
      right,
      assumption,
    left,
    assumption,
  intro h,
  cases h with hq hp,
    right,
    assumption,
  left,
  assumption,
end

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h with hpq hr,
    cases hpq with hp hq,
    split,
      assumption,
    split,
      assumption,
    assumption,
  intro h,
  cases h with hp hqr,
  cases hqr with hq hr,
  split,
    split,
      assumption,
    assumption,
  assumption
end

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
begin
  apply iff.intro,
    intro h,
    cases h with hpq hr,
      cases hpq with hp hq,
        left,
        assumption,
      right,
      left,
      assumption,
    right,
    right,
    assumption,
  intro h,
  cases h with hp hqr,
    left,
    left,
    assumption,
  cases hqr with hq hr,
    left,
    right,
    assumption,
  right,
  assumption,
end

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
      left,
      apply and.intro, -- equivalent to split
        assumption,
      assumption,
    right,
    split,
      assumption,
    assumption,
  intro h,
  cases h with hpq hpr,
  cases hpq with hp hq,
    split,
      assumption,
    left,
    assumption,
  cases hpr with hp hr,
  split,
    assumption,
  right,
  assumption,
end

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
begin
  apply iff.intro,
    intro h,
    cases h with hp hqr,
      split,
        left,
        assumption,
      left,
      assumption,
    cases hqr with hq hr,
    split,
      right,
      assumption,
    right,
    assumption,
  intro h,
  cases h with hpq hpr,
  cases hpq with hp hq,
    left,
    assumption,
  cases hpr with hp hr,
    left,
    assumption,
  right,
  split,
    assumption,
    assumption,
end

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
begin
  apply iff.intro,
    intros hpqr hpq,
    cases hpq with hp hq,
    apply hpqr,
      assumption,
    assumption,
  intros hpqr hp hq,
  apply hpqr,
  split,
    assumption,
  assumption,
end

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
begin
  apply iff.intro,
    intro h,
    split,
      intro hp,
      apply h,
      left,
      assumption,
    intro hq,
    apply h,
    right,
    assumption,
  intros h hpq,
  cases h with hpr hqr,
  cases hpq with hp hq,
    apply hpr,
    assumption,
  apply hqr,
  assumption,
end

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
begin
  apply iff.intro,
    intro h,
    split,
      intro hp,
      apply h,
      left,
      assumption,
    intro hq,
    apply h,
    right,
    assumption,
  intro h,
  cases h with hnp hnq,
  intro hpq,
  cases hpq with hp hq,
    apply hnp,
    assumption,
  apply hnq,
  assumption,
end

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
begin
  intro h,
  intro hpq,
  cases hpq with hp hq,
  cases h with hnp hnq,
    apply hnp,
    assumption,
  apply hnq,
  assumption,
end

example : ¬(p ∧ ¬p) :=
begin
  intro h,
  cases h with hp hnp,
  apply hnp,
  assumption,
end

example : p ∧ ¬q → ¬(p → q) :=
begin
  intro h,
  intro hpq,
  cases h with hp hnq,
  apply hnq,
  apply hpq,
  assumption,
end

example : ¬p → (p → q) :=
begin
  intros hnp hp,
  exfalso,
  apply hnp,
  assumption,
end

example : (¬p ∨ q) → (p → q) :=
begin
  intros h hp,
  cases h with hnp hq,
    exfalso,
    apply hnp,
    assumption,
  assumption,
end

example : p ∨ false ↔ p :=
begin
  apply iff.intro,
    intro h,
    cases h with hp hf,
      assumption,
    exfalso,
    assumption,
  intro hp,
  left,
  assumption,
end

example : p ∧ false ↔ false :=
begin
  apply iff.intro,
    intro h,
    cases h with hp hf,
    assumption,
  intro hf,
  exfalso,
  assumption,
end

example : (p → q) → (¬q → ¬p) :=
begin
  intros hpq hnq,
  intros hp,
  apply hnq,
  apply hpq,
  assumption,
end
