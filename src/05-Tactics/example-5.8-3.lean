-- 5.8 Exercises
-- #1

-- 3.7 Exercises
-- #3

variable p : Prop

example : ¬ (p ↔ ¬ p) :=
begin
  intro h,
  cases h with h1 h2,
  have hnp : ¬ p := λ hp : p, (h1 hp) hp,
  have hp : p := h2 hnp,
  contradiction,
end
