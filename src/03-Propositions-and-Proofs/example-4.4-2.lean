import data.nat.basic

def is_even (a : nat) := ∃ b, a = 2 * b

theorem even_plus_even {a b : nat}
  (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  exists.elim h1 (assume w1, assume hw1 : a = 2 * w1,
  exists.elim h2 (assume w2, assume hw2 : b = 2 * w2,
    exists.intro (w1 + w2)
      (calc
        a + b = 2 * w1 + 2 * w2 : by rw [hw1, hw2]
        ...   = 2 * (w1 + w2)   : by rw mul_add)))

theorem even_plus_even' {a b : nat}
  (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
match h1, h2 with
  ⟨ w1, hw1⟩, ⟨ w2, hw2⟩ := ⟨ w1 + w2, by rw [hw1, hw2, mul_add]⟩
end
