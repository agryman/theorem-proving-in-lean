#check Prop
#print Prop

#check and
#print and

namespace hidden
constant and : Prop → Prop → Prop
constant or : Prop → Prop → Prop
constant not : Prop → Prop
constant implies : Prop → Prop → Prop

variables p q r : Prop
#check and p q
#check or (and p q) r
#check implies (and p q) (and q p)

constant Proof : Prop → Type

constant and_comm : Π p q : Prop, Proof (implies (and p q) (and q p))
#check and_comm p q 

constant modus_ponens : Π p q : Prop, Proof (implies p q) → Proof p → Proof q
#check modus_ponens p q

constant implies_intro : Π p q : Prop, (Proof p → Proof q) → Proof (implies p q)
#check implies_intro p q

constants t1 t2 : p
#check t1
#check t1 = t2
-- #eval t1 = t2 

end hidden

