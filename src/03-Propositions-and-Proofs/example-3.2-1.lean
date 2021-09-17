constants p q : Prop 

theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
#check t1
#print t1

theorem t1' : p → q → p :=
assume hp : p,
assume hq : q,
hp
#print t1

theorem t1'' : p → q → p :=
assume hp : p,
assume hq : q,
show p, from hp
#print t1''

lemma t1l : p → q → p :=
assume hp : p,
assume hq : q,
show p, from hp
#check t1l
#print t1l 

theorem t1f (hp : p) (hq : q) : p := hp
#check t1f
#print t1f

axiom hp : p

theorem t2 : q → p := t1 hp
#check t2
#print t2

theorem t1g (p q : Prop) (hp : p) (hq : q) : p : hp
#check t1g

theorem t1g' : ∀ (p q : Prop), p → q → p := 
λ (p q : Prop) (hp : p) (hq : q), hp
#check ∀ (p q : Prop), p → q → p
#check λ (p q : Prop) (hp : p) (hq : q), hp
#check t1g'
#print t1g'
