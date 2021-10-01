-- #2

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) :=
assume a: α, show (∀ x : α, r) ↔ r, from
iff.intro
(assume h: ∀ x : α, r, show r, from h a)
(assume hr: r, show ∀ x : α, r, from
  assume w: α, hr
)

open classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
iff.intro
(assume h: ∀ x, p x ∨ r, show (∀ x, p x) ∨ r, from 
  or.elim (em r)
  (assume hr: r, show (∀ x, p x) ∨ r, from or.inr hr)
  (assume hnr: ¬r,
    have hap: ∀ x, p x := 
    (assume a: α,
      have hpar: p a ∨ r := h a,
      show p a, 
      from or.elim hpar
      (assume hpa: p a, hpa)
      (assume hr: r, absurd hr hnr)
    ),
    show (∀ x, p x) ∨ r, 
    from or.inl hap
  )
)
(assume h: (∀ x, p x) ∨ r, show ∀ x, p x ∨ r, from 
  or.elim h
  (assume hap: ∀ x, p x, show ∀ x, p x ∨ r, from
    assume a: α, show p a ∨ r, from or.inl (hap a)
  )
  (assume hr: r, show ∀ x, p x ∨ r, from
    assume a: α, show p a ∨ r, from or.inr hr
  )
)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
iff.intro
(assume h: ∀ x, r → p x, show r → ∀ x, p x, from
  (assume hr: r, show ∀ x, p x, from
    assume a: α,
    have hrpa: r → p a := h a,
    show p a, 
    from hrpa hr
  )
)
(assume h: r → ∀ x, p x, show ∀ x, r → p x, from
  assume a: α, show r → p a, from
  assume hr: r, show p a, from h hr a
)