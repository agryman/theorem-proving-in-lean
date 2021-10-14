-- 5.8 Exercises
-- #1
-- Go back to the exercises in Chapter 3 and Chapter 4 and redo as many as you can now with tactic proofs, 
-- using also rw and simp as appropriate.


-- 4.6 Exercises
-- #5
-- Prove as many of the identities listed in Section 4.4 as you can.

open classical

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : (∃ x : α, r) → r :=
begin
  intro h,
  cases h with w hr,
  assumption,
end

example (a : α) : r → (∃ x : α, r) :=
begin
  intro hr,
  exact exists.intro a hr,
end

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
begin
  apply iff.intro,
    intro h,
    cases h with w hw,
    cases hw with hpw hr,
    split,
      exact exists.intro w hpw,
    assumption,
  intro h,
  cases h with hep hr,
  cases hep with w hpw,
  exact exists.intro w ⟨hpw, hr⟩, 
end

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
begin
  apply iff.intro,
    intro h,
    cases h with w hpq,
    cases hpq with hp hq,
      left,
      exact ⟨w, hp⟩,
    right,
    exact ⟨w, hq⟩,
  intro h,
  cases h with hp hq,
    cases hp with w hpw,
    existsi w,
    left,
    assumption,
  cases hq with w hqw,
  existsi w,
  right,
  assumption,
end

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
begin
  split,
    intro h,
    intro henp,
    cases henp with w hnpw,
    have hpw : p w := h w,
    contradiction,
  intro h,
  assume a : α,
  cases (em (p a)) with hpa hnpa,
    assumption,
  exfalso,
  apply h,
  exact ⟨a, hnpa⟩,
end

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
begin
  split,
    intro h,
    cases h with w hpw,
    intro hnpx,
    have hnpw : ¬ p w := hnpx w,
    contradiction,
  intro h,
  apply by_contradiction,
    intro hnepx,
    apply h,
    intro w,
    intro hpw,
    have hepx : ∃ x, p x := ⟨w, hpw⟩,
    contradiction,
end

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
begin
  split,
    intro h,
    assume w,
    assume hpw,
    have hepx : ∃ x, p x := ⟨w,hpw⟩,
    contradiction,
  intro h,
  intro hepx,
  cases hepx with w hpw,
  have hnpw :=h w,
  contradiction,
end

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
begin
  split,
    intro h,
    apply by_contradiction,
    intro hnenpx,
    apply h,
    intro w,
    apply by_contradiction,
    intro hnpw,
    have henpx : ∃ x, ¬ p x := ⟨w, hnpw⟩,
    contradiction,
  intro h,
  cases h with w hnpw,
  intro hapx,
  have hpw := hapx w,
  contradiction,
end

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
begin
  split,
    intros h1 h2,
    cases h2 with w hpw,
    have hpwr := h1 w,
    exact hpwr hpw,
  intro h,
  intro w,
  intro hpw,
  exact h ⟨w, hpw⟩,
end

lemma not_forall_exists_not : ¬ (∀ x: α, p x) → ∃ x, ¬(p x) :=
begin
  intro h,
  apply by_contradiction,
  intro h1,
  have h2 : ∀ x, p x :=
  begin
    intro w,
    apply by_contradiction,
    intro hnpw,
    have henpx : ∃ x, ¬ p x := ⟨w, hnpw⟩,
    contradiction,
  end,
  apply h,
  assumption,
end

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
begin
  split,
    intros h1 h2,
    cases h1 with w hw,
    exact hw (h2 w),
  intro h,
  cases (em r) with hr hnr,
    have hpar : p a → r := λ _, hr,
    exact ⟨a, hpar⟩,
  cases (em (∀ x, p x)) with hapx hnapx,
    have hr : r := h hapx,
    contradiction,
  have henpx := not_forall_exists_not α p hnapx,
  cases henpx with w hnpw,
  existsi w,
  intro hpwr,
  contradiction,
end

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
begin
  split,
    intros h hr,
    cases h with w hw,
    exact ⟨w, hw hr⟩,
  intro h,
  cases (em (p a)) with hpa hnpa,
    have hrpa : r → p a := λ hr : r, hpa,
    exact ⟨a, hrpa⟩,
  cases (em r) with hr hnr,
    have hepx := h hr,
    cases hepx with w hpw,
    have hrpw : r → p w := λ _, hpw,
    exact ⟨w, hrpw⟩,
    have hrpa : r → p a :=
    begin
      intro hr,
      contradiction,
    end,
  exact ⟨a, hrpa⟩,
end
