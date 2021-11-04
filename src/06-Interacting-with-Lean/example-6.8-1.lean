-- 6.8 Displaying Information

#check eq
#check @eq
#check eq.symm
#check @eq.symm

#print eq.symm

#check and
#check and.intro
#check @and.intro

def foo {α : Type*} (x : α) : α := x

#check foo
#check @foo
#reduce foo
#reduce (foo nat.zero)
#print foo

-- #print def
#print foo

-- #print inductive
#print nat

#print notation
#print notation ↔ ∃ ∀

#print axioms

#print options

#print prefix nat

#print classes

#print instances has_add

-- #print fields <structure>
