/- declare some constants -/

constant m : nat      -- m is a natural number
constant n : nat
constants b1 b2 : bool  -- declare two constants at once

/- check their types -/
#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check tt

-- Try some examples on your own.

#check ff
#check ff && tt
#eval ff && tt
#eval ff || tt

#check nat → bool
#check nat × bool
#check nat → (bool × nat)

#check int
#check set int
#check list int
#check int × (int × int)
#check (int × int) × int
#check {}

#check nat -- Type
#check Type -- Type 1
