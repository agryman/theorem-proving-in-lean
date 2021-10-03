-- #7

import data.int.basic

#check sub_self
#check mul_comm
#check eq.symm
#check eq.trans

example (x : ℤ) : x * 0 = 0 :=
have h : x - x = 0 := sub_self x,
-- have h1 : 0 = x - x := eq.symm h,
have h2 : x * 0 = x * 0 := eq.refl (x * 0),
have h3 : x * 0 = x * (x - x), by rw h,
have h4 : x * (x - x) = x * x - x * x := mul_sub x x x,
have h5 : x * x - x * x = 0 := sub_self (x * x),
have h6 : x * 0 = x * x - x * x := eq.trans h3 h4,
show x * 0 = 0,
from eq.trans h6 h5

-- write the above proof using calc
example (x : ℤ) : x * 0 = 0 :=
calc
  x * 0 =  x * (x - x)  : by rw (sub_self x)
  ...   = x * x - x * x : mul_sub x x x
  ...   = 0             : sub_self (x * x)
