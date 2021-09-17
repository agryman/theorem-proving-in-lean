variables p q : Prop

theorem t1 : p → q → p := λ (hp : p) (hq : q), hp
#check t1

variable hp : p

theorem t1' : q → p := λ hq : q, hp
#check t1'
#print t1'

variables r s : Prop

#check t1 p q
#check t1 r s
#check t1 (r → s) (s → r)

variable h : r → s
#check t1 (r → s) (s → r) h

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
assume h₃ : p,
show r, from h₁ (h₂ h₃)

-- t2 says that implication is a transitive binary relation on the set of propositions
