#print nat.mul
#print nat.add
#print nat.succ
#print nat.sub

open nat (renaming mul → times) (renaming add → plus) (hiding succ sub)

#check times
#check plus
-- #check sub
