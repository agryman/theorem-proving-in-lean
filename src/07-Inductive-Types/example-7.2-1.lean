-- 7.2 Constructors with Arguments

universes u v

namespace hidden

inductive empty

inductive unit
| star : unit

#check empty = unit
#reduce empty = unit

inductive prod (α : Type u) (β : Type v)
| mk : α → β → prod

inductive sum (α : Type u) (β : Type v)
| inl : α → sum
| inr : β → sum

def fst {α : Type u} {β : Type v} (p : prod α β) : α :=
prod.rec_on p (λ a b, a)

def snd {α : Type u} {β : Type v} (p : prod α β) : β :=
prod.rec_on p (λ a b, b)

#print prod.rec_on

#check bool × ℕ 

def prod_example (p : prod bool ℕ) : ℕ :=
prod.rec_on p (λ b n, cond b (2 * n) (2 * n + 1))

#reduce prod_example (prod.mk bool.tt 3) -- 6
#reduce prod_example (prod.mk bool.ff 3) -- 7

#print cond

def sum_example (s : (sum ℕ ℕ)) : ℕ :=
sum.cases_on s (λ n, 2 * n) (λ n, 2 * n + 1)

#print sum.cases_on

#reduce sum_example (sum.inl 3) -- 6
#reduce sum_example (sum.inr 3) -- 7

#check ℕ ⊕ ℕ 
#check sum ℕ ℕ 
#check (ℕ ⊕ ℕ) = (sum ℕ ℕ)

end hidden
