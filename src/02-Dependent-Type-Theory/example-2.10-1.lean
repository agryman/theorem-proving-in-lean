-- #1

universe u

def Do_Twice {α : Type u} : (α → α) → α → α :=
  λ f : α → α , λ a : α, f (f a)

def square (n : ℕ) : ℕ := n * n

#eval square 3
#eval square (square 3)
#eval Do_Twice square 3

-- #2

def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ :=
  λ a : α, λ b : β, f (a, b)

def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ :=
  λ p : α × β, f p.1 p.2

-- #3

constant vec : Type u → ℕ → Type u

constant vec_add {n : ℕ} : vec ℕ n → vec ℕ n → vec ℕ n
#check vec_add

constant vec_reverse {α : Type u} {n : ℕ } : vec α n → vec α n 
#check vec_reverse

constant a7 : vec ℕ 7
constant b7 : vec ℕ 7
#check vec_add a7 b7 
#check vec_reverse a7

constant c8 : vec ℕ 8

-- #check vec_add a7 c8

-- #4

constant matrix : Type u → ℕ → ℕ → Type u
#check matrix

constant matrix_add {m n : ℕ } : matrix ℕ m n → matrix ℕ m n → matrix ℕ m n
#check matrix_add

constant a23 : matrix ℕ 2 3
constant b23 : matrix ℕ 2 3
#check matrix_add a23 a23
#check matrix_add b23 a23

constant matrix_mul {l m n : ℕ } : matrix ℕ l m → matrix ℕ m n → matrix ℕ l n
#check matrix_mul

constant c34 : matrix ℕ 3 4
#check matrix_mul a23 c34

constant matrix_vec {m n : ℕ } : matrix ℕ m n → vec ℕ n → vec ℕ n
#check matrix_vec

constant v4 : vec ℕ 4
#check matrix_vec c34 v4
-- #check matrix_vec b23 v4
