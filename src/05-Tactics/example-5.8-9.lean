-- 5.8 Exercises
-- #1
-- Go back to the exercises in Chapter 3 and Chapter 4 and redo as many as you can now with tactic proofs, 
-- using also rw and simp as appropriate.

-- 4.6 Exercises
-- #7 
-- Prove the theorem below, using only the ring properties of ℤ enumerated in 
-- Section 4.2 and the theorem sub_self.

import data.int.basic

#check sub_self

example (x : ℤ) : x * 0 = 0 :=
sorry