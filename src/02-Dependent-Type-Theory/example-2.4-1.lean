def foo : (ℕ → ℕ) → ℕ := λ f, f 0
#check foo
#print foo

def foo' := λ f : ℕ → ℕ, f 0 
#check foo'
#print foo'

def foo'' (f: ℕ → ℕ) : ℕ := f 0
#check foo''
#print foo''

-- omit type information and let Lean infer it
def one := 1
#check one

def double (x : ℕ) : ℕ := x + x
#print double
#check double
#reduce double 3

-- omit type of result
def square (x : ℕ) := x * x 
#print square
#check square
#reduce square 3

def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)
#check do_twice
#reduce do_twice double 2

def double' : ℕ → ℕ := λ x, x + x
#check double'
#reduce double' 7

def square' : ℕ → ℕ := λ x, x * x
#reduce square' 7

def square'' := λ x : ℕ, x * x
#check square''

def do_twice' : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)
#check do_twice'

def do_twice'' := λ (f : ℕ → ℕ) x, f (f x)
#check do_twice''

def compose (α β γ : Type*) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

def quadruple (x : ℕ) : ℕ := do_twice double x
#check quadruple
#reduce quadruple 3

def octuple (x : ℕ) := quadruple (double x)
#check octuple
#reduce octuple 3

def Do_Twice (t : (ℕ → ℕ) → ℕ → ℕ) (f : ℕ → ℕ) (x : ℕ) := t (t f) x
#check Do_Twice
#reduce Do_Twice do_twice double 2
#eval Do_Twice do_twice double 2
#eval Do_Twice do_twice double 3

def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ := 
  λ (a : α) (b : β), f (a, b)
#check curry

def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ :=
  λ p : α × β, f p.1 p.2
#check uncurry

def add := λ p : ℕ × ℕ, p.1 + p.2
#check add
#eval add (2, 3)

def cadd := curry ℕ ℕ ℕ add
#check cadd
#eval cadd 2 3

def ucadd := uncurry ℕ ℕ ℕ cadd
#check ucadd
#eval ucadd (2, 3)

-- let Lean infer the types
def cadd' := curry _ _ _ add
#check cadd'
