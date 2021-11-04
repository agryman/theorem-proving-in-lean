import data.int.basic

namespace int

def dvd (m n : ℤ) : Prop := ∃ k, n = m * k
instance : has_dvd int  := ⟨int.dvd⟩

@[simp]
theorem dvd_zero (n : ℤ) : dvd n 0 :=
⟨0, by simp⟩

theorem dvd_intro {m n : ℤ} (k : ℤ) (h : n = m * k) : dvd m n :=
⟨k, h⟩

end int

open int

section mod_m
parameter (m : ℤ)
variables (a b c : ℤ)

definition mod_equiv := dvd m (b - a)

#check mod_equiv
#print mod_equiv

local infix `≡`:50 := mod_equiv

theorem mod_refl : a ≡ a :=
show dvd m (a - a), by simp

theorem mod_symm (h : a ≡ b) : b ≡ a :=
by cases h with c hc; apply dvd_intro (-c); simp [eq.symm hc]

local attribute [simp] add_assoc add_comm add_left_comm

theorem mod_trans (h₁ : a ≡ b) (h₂ : b ≡ c) : a ≡ c :=
begin
  cases h₁ with d hd,
  cases h₂ with e he,
  apply dvd_intro (d + e),
  simp [mul_add, eq.symm hd, eq.symm he, sub_eq_add_neg]
end

end mod_m

#check (mod_refl : ∀ (m a : ℤ), mod_equiv m a a)

#check (mod_symm : ∀ (m a b : ℤ), mod_equiv m a b → mod_equiv m b a)

#check (mod_trans : ∀ (m a b c : ℤ), mod_equiv m a b → mod_equiv m b c → mod_equiv m a c)
