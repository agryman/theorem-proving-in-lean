theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro,
    exact hp,
  apply and.intro,
    exact hq,
  exact hp,
end

#print test

theorem test' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro hp,
  exact and.intro hq hp,
end

#print test'

theorem test'' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro hp; exact and.intro hq hp,
end

theorem test''' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
by exact and.intro hp (and.intro hq hp)
