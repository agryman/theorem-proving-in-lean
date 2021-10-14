example (p q : Prop) : p ∨ q → q ∨ p :=
begin
  intro h,
  cases h with hp hq,
    right, exact hp,
  left, exact hq,
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  constructor,
    exact hq,
  exact hp,
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
    left, constructor, repeat { assumption },
    right, constructor, repeat { assumption },
  intro h,
  cases h with hpq hpr,
    cases hpq with hp hq,
    constructor, exact hp, left, exact hq,
  cases hpr with hp hr,
  constructor, exact hp, right, exact hr,
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  constructor, left, exact px,
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  existsi x, left, assumption,
end

example (p q : ℕ → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
begin
  intro h,
  cases h with x hpq,
  cases hpq with hp hq,
  existsi x,
  -- constructor, assumption, assumption,
  split; assumption
end

universes u v

def swap_pair {α : Type u} {β : Type v}: α × β → β × α :=
begin
  intro p,
  cases p with a b,
  constructor, exact b, exact a,
end

def swap_pair' {α : Type u} {β : Type v}: α ⊕ β → β ⊕ α :=
begin
  intro p,
  cases p with a b,
    right, exact a,
  left, exact b,
end

open nat

example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) : P m :=
begin
  cases m with m',
    exact h₀,
  exact (h₁ m'),
end

example (p q : Prop) : p ∧ ¬ p → q :=
begin
  intro h,
  cases h with hp hnp,
  contradiction,
end