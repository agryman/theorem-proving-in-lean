universe u

section
variable {α : Type u}
variable x : α 
def ident := x
end

variables α β : Type u
variables (a : α ) (b : β)

#check ident
#check ident a
#check ident b

#check list
#check list.nil 
#check id

#check (list.nil : list ℕ)
#check (id : ℕ → ℕ )

#check 2
#check (2 : ℕ )
#check (2 : ℤ )

#check id
#check @id
#check @id α 
#check @id β
#check @id α a 
#check @id β b 