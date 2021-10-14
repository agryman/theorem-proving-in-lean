-- 5.8 Exercises
-- #1

-- 4.6 Exercises
-- #3

variables (men : Type*) (barber : men)
variable  (shaves : men → men → Prop)

open classical

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=
begin
  have hb := h barber,
  cases hb with h1 h2,
  cases (em (shaves barber barber)) with hsbb hnsbb,
    have hnsbb := h1 hsbb,
    contradiction,
  have hsbb := h2 hnsbb,
  contradiction,
end
