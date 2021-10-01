import data.int.basic

variables a b c d : ℤ

#check -a

example : a + 0 = a := add_zero a
example : 0 + a = a := zero_add a
example : a * 1 = a := mul_one a
example : 1 * a = a := one_mul a
example : -a + a = 0 := neg_add_self a
example : a + -a = 0 := add_neg_self a
example : a - a = 0 := sub_self a
example : a + b = b + a := add_comm a b
example : a + b + c = a + (b + c) := add_assoc a b c
example : a * b = b * a := mul_comm a b
example : a * b * c = a * (b * c) := mul_assoc a b c
example : a * (b + c) = a * b + a * c := mul_add a b c
example : a * (b + c) = a * b + a * c := left_distrib a b c
example : (a + b) * c = a * c + b * c := add_mul a b c
example : (a + b) * c = a * c + b * c := right_distrib a b c
example : a * (b - c) = a * b - a * c := mul_sub a b c
example : (a - b) * c = a * c - b * c := sub_mul a b c

variables x y z : ℤ

example (x y z : ℕ) : x * (y + z) = x * y + x * z := mul_add x y z
example (x y z : ℕ) : (x + y) * z = x * z + y * z := add_mul x y z
example (x y z : ℕ) : x + y + z = x + (y + z) := add_assoc x y z

#check mul_add x y z

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y,
  from mul_add (x + y) x y,
have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
  from (add_mul x y x) ▸ (add_mul x y y) ▸ h1,
h2.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm
