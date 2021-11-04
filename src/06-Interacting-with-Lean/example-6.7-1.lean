-- 6.7 Coercions

variables m n : ℕ
variables i j : ℤ

#check i + m
#check i + m + j
#check i + m + n
#check i = m
#check ↑m = i

#check ↑m + i
#check ↑(m + n) + i
#check ↑m + ↑n + i
