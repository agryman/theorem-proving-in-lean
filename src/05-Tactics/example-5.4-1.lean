-- 5.4 Structuring Tactic Proofs

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  exact
    have hp : p, from h.left,
    have hqr : q ∨ r, from h.right,
    show (p ∧ q) ∨ (p ∧ r),
    begin
      cases hqr with hq hr,
        left, exact ⟨hp, hq⟩,
      right, exact ⟨hp, hr⟩,
    end
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h.right with hq hr,
      exact or.inl ⟨h.left, hq⟩,
    exact or.inr ⟨h.left, hr⟩,
  intro h,
  cases h with hpq hpr,
    exact ⟨hpq.left, or.inl hpq.right⟩,
  exact ⟨hpr.left, or.inr hpr.right⟩,
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h.right with hq hr,
      show (p ∧ q) ∨ (p ∧ r),
      from or.inl ⟨h.left, hq⟩,
    show (p ∧ q) ∨ (p ∧ r),
    from or.inr ⟨h.left, hr⟩,
  intro h,
  cases h with hpq hpr,
    show p ∧ (q ∨ r),
    from ⟨hpq.left, or.inl hpq.right⟩,
  show p ∧ (q ∨ r),
  from ⟨hpr.left, or.inr hpr.right⟩,
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h.right with hq hr,
      show (p ∧ q) ∨ (p ∧ r),
      { left, split, exact h.left, assumption },
    show (p ∧ q) ∨ (p ∧ r),
    {right, split, exact h.left, assumption },
  intro h,
  cases h with hpq hpr,
    show p ∧ (q ∨ r),
    { cases hpq, split, assumption, left, assumption },
  show p ∧ (q ∨ r),
  { cases hpr, split, assumption, right, assumption }
end

example (n : ℕ) : n + 1 = nat.succ n :=
begin
  show nat.succ n = nat.succ n,
  reflexivity,
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  split,
    show q, from hq,
  show p, from hp,
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  split,
    show p, from hp,
  show q, from hq,
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  cases h with hp hqr,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    have hpq : p ∧ q,
      from and.intro hp hq,
    left, exact hpq,
  have hpr : p ∧ r,
    from and.intro hp hr,
  right, exact hpr,
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  cases h with hp hqr,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    have hpq : p ∧ q,
      split; assumption,
    left, exact hpq,
  have hpr : p ∧ r,
    split; assumption,
  right, exact hpr,
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  cases h with hp hqr,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    have : p ∧ q,
      split; assumption,
    left, exact this,
  have : p ∧ r,
    split; assumption,
  right, exact this,
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  have hp : p := h.left,
  have hqr : q ∨ r := h.right,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    exact or.inl ⟨hp, hq⟩,
  exact or.inr ⟨hp, hr⟩,
end

example : ∃ x, x + 2 = 8 :=
begin
  let a : ℕ := 3 * 2,
  existsi a,
  reflexivity,
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  begin
    intro h,
    cases h.right with hq hr,
    begin
      show (p ∧ q) ∨ (p ∧ r),
      exact or.inl ⟨h.left, hq⟩ 
    end,
    show (p ∧ q) ∨ (p ∧ r),
      exact or.inr ⟨h.left, hr⟩
  end,
  intro h,
  cases h with hpq hpr,
  begin
    show p ∧ (q ∨ r),
    exact ⟨hpq.left, or.inl hpq.right⟩ 
  end,
  show p ∧ (q ∨ r),
  exact ⟨hpr.left, or.inr hpr.right⟩,
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  { intro h,
    cases h.right with hq hr,
    { show (p ∧ q) ∨ (p ∧ r),
      exact or.inl ⟨h.left, hq⟩ },
    show (p ∧ q) ∨ (p ∧ r),
      exact or.inr ⟨h.left, hr⟩ },
  intro h,
  cases h with hpq hpr,
  { show p ∧ (q ∨ r),
    exact ⟨hpq.left, or.inl hpq.right⟩ },
  show p ∧ (q ∨ r),
  exact ⟨hpr.left, or.inr hpr.right⟩,
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  { intro h,
    cases h.right with hq hr,
    { show (p ∧ q) ∨ (p ∧ r),
      exact or.inl ⟨h.left, hq⟩ },
    { show (p ∧ q) ∨ (p ∧ r),
      exact or.inr ⟨h.left, hr⟩ }},
  { intro h,
    cases h with hpq hpr,
    { show p ∧ (q ∨ r),
      exact ⟨hpq.left, or.inl hpq.right⟩ },
    { show p ∧ (q ∨ r),
      exact ⟨hpr.left, or.inr hpr.right⟩ }},
end

example (p q : Prop) : p ∧ q ↔ q ∧ p :=
begin
  apply iff.intro,
  { intro h,
    have hp : p := h.left,
    have hq : q := h.right,
    show q ∧ p,
    exact ⟨hq, hp⟩ },
  intro h,
  have hp : p := h.right,
  have hq : q := h.left,
  show p ∧ q,
  exact ⟨hp, hq⟩,
end
