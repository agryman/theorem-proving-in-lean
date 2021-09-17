-- Classical Logic

open classical

variables p q : Prop
#check em p

theorem dne {p : Prop} (h : ¬¬ p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬ p, absurd hnp h)

-- theorem converse {p : Prop} : p ∨ ¬ p :=
-- stopped here - no idea how to prove this!

-- There is a classical proof in Lemmon, result 44, p52!
-- As a warm-up for converting natural deduction proofs
-- into Lean proofs, try result 23 on p27.

theorem lemmon_23 {p : Prop} (h : p → ¬ p) : ¬ p :=
assume hp : p,
have hnp : ¬ p, from h hp,
show false, from hnp hp

#check @lemmon_23 p
#print lemmon_23

-- Write lemmon_23 as a term

theorem lemmon_23' {p : Prop} (h : p → ¬ p) : ¬ p :=
λ hp : p, (h hp) hp

#check @lemmon_23' p
#check lemmon_23'

theorem lemmon_44 {p : Prop} : p ∨ ¬ p :=
have hdn : ¬ ¬ (p ∨ ¬ p), from (
  assume h : ¬ (p ∨ ¬ p),
  have hnp : ¬ p, from (
    assume hp : p,
    have h1 : p ∨ ¬ p, from or.intro_left (¬ p) hp,
    show false, from h h1),
  have h2 : p ∨ ¬ p, from or.intro_right p hnp,
  show false, from h h2),
show p ∨ ¬ p, from dne hdn

-- Not sure about the "assume", "show" syntax, 
-- but it looks like lambda abstraction.
-- Does "show" pair up with the nearest "assume" and close its scope?
-- I think "show" simply annotates the result given by the "from".

-- "show" and "from" are used to annotate a term, 
-- which could be expected in the context of either the definition or the lambda

#check @lemmon_44 p
#check lemmon_44
#print lemmon_44

-- Try using "suffices" to improve lemmon_44

theorem lemmon_44' {p : Prop} : p ∨ ¬ p :=
suffices hdn : ¬ ¬ (p ∨ ¬ p), from dne hdn,
assume h : ¬ (p ∨ ¬ p),
have hnp : ¬ p, from (
  assume hp : p,
  have h1 : p ∨ ¬ p, from or.intro_left (¬ p) hp,
  show false, from h h1),
have h2 : p ∨ ¬ p, from or.intro_right p hnp,
show false, from h h2

#check lemmon_44'

example (h : ¬ ¬ p) : p :=
by_cases
  (assume h1 : p, h1)
  (assume h1 : ¬ p, absurd h1 h)

example (h : ¬ ¬ p) : p :=
by_contradiction
  (assume h1 : ¬ p,
    show false, from h h1)

example (h : ¬ (p ∧ q)) : ¬ p ∨ ¬ q :=
or.elim (em p)
  (assume hp : p,
    or.inr 
      (show ¬ q, from
        assume hq : q, 
        h ⟨ hp, hq ⟩ ))
  (assume hp : ¬ p, 
    or.inl hp)
