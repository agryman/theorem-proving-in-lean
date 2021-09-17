variables (α : Type*) (r : α → α → Prop)
variable trans_r : ∀ {x y z}, r x y → r y z → r x z

variables (a b c : α)
variables (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc

variable refl_r : ∀ x, r x x
variable symm_r : ∀ {x y}, r x y → r y x

example (a b c d : α ) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
trans_r (trans_r hab (symm_r hcb)) hcd
