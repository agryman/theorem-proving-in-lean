-- 4.2 Equality

#check eq
#check eq.refl
#check eq.symm
#check eq.trans

universe u

#check @eq
#check @eq.refl.{u}
#check @eq.symm.{u}
#check @eq.trans.{u}

variables (α : Type*) (a b c d: α)
variables (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
have hbc : b = c, from eq.symm hcb,
have hac : a = c, from eq.trans hab hbc,
show a = d, 
from eq.trans hac hcd

example : a = d :=
eq.trans (eq.trans hab (eq.symm hcb)) hcd

example : a = d := (hab.trans hcb.symm).trans hcd

variable β : Type*

example (f : α → β) (a : α) : (λ x, f x) a = f a := eq.refl _
example (a : α) (b : α) : (a, b).1 = a := eq.refl _
example : 2 + 3 = 5 := eq.refl _

example (f : α → β) (a : α) : (λ x, f x) a = f a := rfl
example (a : α) (b : α) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

