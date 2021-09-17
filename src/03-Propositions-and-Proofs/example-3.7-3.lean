-- Exercises
-- #3

variable p : Prop

example : ¬(p ↔ ¬p) := 
assume h : p ↔ ¬p,
show false, from
have h1 : p → ¬p := h.elim_left,
have h2 : ¬p → p := h.elim_right,
have hnp : ¬p := (λ hp : p, (h1 hp) hp),
have hp : p := h2 hnp,
absurd hp hnp
