namespace hidden

universes u v

inductive prod (α : Type u) (β : Type v)
| mk (fst : α) (snd : β) : prod

inductive sum (α : Type u) (β : Type v)
| inl {} (a : α) : sum
| inr {} (b : β) : sum

structure prod' (α β : Type*) :=
mk :: (fst : α) (snd : β)

#print prod'.rec

#print prod'.rec_on

#check prod'.fst

#check prod'.snd

#check prod'.rec

#check prod'.rec_on

structure color := (red : nat) (green : nat) (blue : nat)
def yellow := color.mk 255 255 0
#reduce color.red yellow

#check color.red
#check color.blue yellow

structure Semigroup :=
(carrier : Type u)
(mul : carrier → carrier → carrier)
(mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

inductive sigma {α : Type u} {β : α → Type v}
| dpair : Π a : α, β a → sigma

inductive option (α : Type*)
| none {} : option
| some    : α → option

inductive inhabited (α : Type*)
| mk : α → inhabited

end hidden