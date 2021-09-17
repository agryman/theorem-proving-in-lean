-- 4.1 The Universal Quantifier

variables (α : Type*) (p q : α → Prop)

example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
assume h : ∀ x : α, p x ∧ q x,
assume y : α,
show p y,
from (h y).left

example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
assume h : ∀ x : α, p x ∧ q x,
assume z : α,
show p z,
from and.elim_left (h z)

variable r : α → α → Prop
variable trans_r : ∀ x y z, r x y → r y z → r x z

variables a b c : α
variables (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc


