-- #4

import data.nat.basic
import data.nat.pow

#check pow
#check pow 2 3
#check 2 ^ 3

#check even

def prime (n : ℕ) : Prop := 
n > 1 ∧ ∀ a b : ℕ, n = a * b → a = 1 ∧ b = n ∨ a = n ∧ b = 1

def infinitely_many_primes : Prop := ∀ n : ℕ, ∃ p : ℕ, prime p ∧ p > n

def two_pow : ℕ → ℕ
| 0 := 1
| (n + 1) := 2 * two_pow n

def two_pow' (n : ℕ) : ℕ := 2 ^ n

def pow' (b n : ℕ ) : ℕ := b ^ n

#eval 2 ^ 3
#eval 0 ^ 3
#eval 3 ^ 0
#eval 0 ^ 0

def Fermat_number (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1

def Fermat_prime (n : ℕ) : Prop := prime n ∧ ∃ m : ℕ, n = Fermat_number m

def infinitely_many_Fermat_primes : Prop := ∀ n : ℕ, ∃ m : ℕ, m > n ∧ Fermat_prime m

def goldbach_conjecture : Prop :=
∀ n : ℕ, even n ∧ n > 2 → ∃ a b : ℕ, prime a ∧ prime b ∧ n = a + b

def Goldbach's_weak_conjecture : Prop :=
∀ n : ℕ, odd n ∧ n > 5 → ∃ a b c : ℕ, prime a ∧ prime b ∧ prime c ∧ n = a + b + c 

def Fermat's_last_theorem : Prop :=
∀ x y z n : ℕ, x > 0 ∧ y > 0 ∧ n > 1 ∧ x ^ n + y ^ n = z ^ n → n = 2
