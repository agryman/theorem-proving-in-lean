variables {p q : Prop} (hp : p) (hq : q)

include hp hq

example : p ∧ q ∧ p :=
begin
  apply and.intro hp,
  exact and.intro hq hp,
end

omit hp hq

section
include hp hq

example : p ∧ q ∧ p :=
begin
  apply and.intro hp,
  exact and.intro hq hp,
end
end

example : p ∧ q ∧ p :=
let hp := hp, hq := hq in
begin
  apply and.intro hp,
  exact and.intro hq hp
end
