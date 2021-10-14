-- 5.6 Rewriting

variables (f : ℕ → ℕ) (k : ℕ)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := 
begin
  rw h₂,
  rw h₁,
end

example (x y : ℕ ) (p : ℕ → Prop) (q : Prop) (h : q → x = y) (h' : p y) (hq : q) : 
  p x :=
by { rw (h hq), assumption}

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := 
by rw [h₂, h₁]

variables (a b : ℕ)

example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 :=
by rw [←h₁, h₂]
