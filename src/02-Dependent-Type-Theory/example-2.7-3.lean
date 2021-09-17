namespace foo
def a : ℕ := 5
def f (x : ℕ) : ℕ := x + 7

def fa : ℕ := f a
def ffa : ℕ := f (f a)

#print "inside foo"

#check a
#check f
#check fa
#check ffa
#check foo.ffa
end foo

#print "outside the namespace"

-- #check a
-- #check f
#check foo.a
#check foo.f
#check foo.fa
#check foo.ffa

open foo

#print "opened foo"

#check a
#check f
#check fa
#check foo.fa

#check list.nil
#check list.cons
#check list.append

open list

#check nil
#check cons
#check append

