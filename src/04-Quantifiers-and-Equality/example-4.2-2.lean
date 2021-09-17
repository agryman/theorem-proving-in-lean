example (α : Type*) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
eq.subst h1 h2

example (α : Type*) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
h1 ▸ h2

variable α : Type
variables a b : α 
variables f g : α → ℕ
variable h₁ : a = b
variable h₂ : f = g

example : f a = f b := congr_arg f h₁
example : f a = g a := congr_fun h₂ a
example : f a = g b := congr h₂ h₁

#check congr
#check congr_fun
#check congr_arg
