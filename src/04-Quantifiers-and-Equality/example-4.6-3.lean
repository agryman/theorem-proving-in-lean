-- #3

variables (men : Type*) (barber : men)
variable  (shaves : men → men → Prop)

open classical

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=
  have hb: shaves barber barber ↔ ¬ shaves barber barber := h barber,
  have hbb: shaves barber barber → ¬ shaves barber barber := iff.elim_left hb,
  have hnbb: ¬ shaves barber barber → shaves barber barber := iff.elim_right hb,
  or.elim (em (shaves barber barber))
  (assume hsbb: shaves barber barber, absurd hsbb (hbb hsbb))
  (assume hnsbb: ¬ shaves barber barber, absurd (hnbb hnsbb) hnsbb)
