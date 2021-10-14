import data.nat.basic

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
  rw [add_assoc, add_comm b,  ←add_assoc]
end

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
  rw [add_assoc, add_assoc, add_comm b]
end

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
  rw [add_assoc, add_assoc, add_comm _ b]
end

variables (f : ℕ → ℕ) (a : ℕ)

example (h : a + 0 = 0) : f a = f 0 :=
by {rw add_zero at h, rw h}

def tuple (α : Type*) (n : ℕ) :=
  { l : list α // list.length l = n }

variables {α : Type*} {n : ℕ}

example (h : n = 0) (t : tuple α n) : tuple α 0 :=
begin
  rw h at t,
  exact t,
end

