-- Conjunction

variables p q : Prop

example (hp : p) (hq: q) : p ∧ q := and.intro hp hq

#check assume (hp : p) (hq : q), and.intro hp hq

example (h : p ∧ q) : p := and.elim_left h
example (h : p ∧ q) : q := and.elim_right h

example (h : p ∧ q) : q ∧ p :=
and.intro (and.right h) (and.left h)

variables (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)

#check (0 : ℕ)
def zero : ℕ := (0 : ℕ)
#check zero

variable l : list ℕ

#check list.head l
#check l.head

example (h : p ∧ q) : q ∧ p :=
⟨ h.right, h.left ⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
⟨ h.right, ⟨ h.left, h.right ⟩ ⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
⟨ h.right, h.left, h.right ⟩ 