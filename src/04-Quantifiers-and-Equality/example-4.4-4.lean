open classical

variables (α : Type*) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r := 
assume h : ∃ x : α, r,
show r, from
exists.elim h 
  (assume w : α,
    assume hw : r, hw)

-- a shorter proof using an implicit match in assume
example : (∃ x : α, r) → r :=
assume ⟨w, hw⟩, hw 

example : r → (∃ x : α, r) :=
assume hr : r,
exists.intro a hr

-- a shorter proof using the constructor for exists.intro
example : r → (∃ x : α, r) := λ hr : r, ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro
(assume h : ∃ x, p x ∧ r,
  exists.elim h
    (assume w : α,
      assume hw : p w ∧ r,
      show (∃ x, p x) ∧ r,
      from ⟨⟨w, hw.left⟩, hw.right⟩
    )
)
(assume h : (∃ x, p x) ∧ r,
  have hp : ∃ x, p x := h.left,
  have hr : r := h.right,
  exists.elim hp
    (assume w : α,
      assume hw : p w,
      show ∃ x, p x ∧ r,
      from ⟨w, ⟨hw, hr⟩⟩)
)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
(assume h : ∃ x, p x ∨ q x,
  exists.elim h
    (assume w : α, assume hw : p w ∨ q w,
      show (∃ x, p x) ∨ (∃ x, q x),
      from or.elim hw
      (assume hp : p w, or.inl ⟨w, hp⟩)
      (assume hq : q w, or.inr ⟨w, hq⟩)
    )
)
(assume h : (∃ x, p x) ∨ (∃ x, q x),
  show ∃ x, p x ∨ q x,
  from or.elim h
  (assume hp : ∃ x, p x,
    exists.elim hp
    (assume w : α, assume hw : p w, ⟨w, or.inl hw⟩)
  )
  (assume hq : ∃ x, q x,
    exists.elim hq
    (assume w : α, assume hw : q w, ⟨w, or.inr hw⟩)
  )
)

theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)
  
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
iff.intro
(assume h : ∀ x, p x, show ¬ (∃ x, ¬ p x), from
  assume henp : ∃ x, ¬ p x,
  match henp with ⟨w, hw⟩ :=
    hw (h w)
  end
)
(assume h : ¬ (∃ x, ¬ p x), show ∀ x, p x, from
  assume w : α, show p w, from
    or.elim (em ¬ p w)
      (assume hnpw : ¬ p w, absurd (exists.intro w hnpw) h)
      (assume hnnpw : ¬ ¬ p w, dne hnnpw)
)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
iff.intro
(assume h: (∃ x, p x), show ¬ (∀ x, ¬ p x), from
  assume hnp: (∀ x, ¬ p x), show false, from
  exists.elim h (
    assume w: α , assume hw: p w, absurd hw (hnp w)
  )
)
(assume h: ¬ (∀ x, ¬ p x), show ∃ x, p x, from
  by_contradiction
    (assume h1: ¬ ∃ x, p x, show false, from
      have h2: ∀ x, ¬ p x :=
        (assume w: α, show ¬ p w, from
          (assume h3: p w, show false, from
            h1 ⟨w, h3⟩ 
          )
        ),
      h h2
    )
)

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
iff.intro
(assume h: ¬ ∃ x, p x, show ∀ x, ¬ p x, from
  assume w: α, show ¬ p w, from
  assume h1: p w, show false, from
  h ⟨w, h1⟩ 
)
(assume h: ∀ x, ¬ p x, show ¬ ∃ x, p x, from
  assume h1: ∃ x, p x, show false, from
  exists.elim h1
  (assume w: α, assume hw: p w, h w hw)
)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
iff.intro
(assume h: ¬ ∀ x, p x, show ∃ x, ¬ p x, from
  by_contradiction
    (assume h1: ¬ ∃ x, ¬ p x, show false, from
      have h2: ∀ x, p x :=
        (assume w: α, show p w, from
          or.elim (em (p w))
          (assume hpw: p w, hpw)
          (assume hnpw: ¬ p w, absurd (exists.intro w hnpw)  h1)
        ),
      h h2
    )
)
(assume h: ∃ x, ¬ p x, show ¬ ∀ x, p x, from
  match h with ⟨w, hw⟩ :=
    assume h1: ∀ x, p x, show false, from
    hw (h1 w)
  end
)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
iff.intro
(assume h: ∀ x, p x → r, show (∃ x, p x) → r, from
  assume h1: ∃ x, p x, show r, from
    match h1 with ⟨w, hw⟩ :=
      have h2: p w → r := h w,
      h2 hw
    end
)
(assume h: (∃ x, p x) → r, show ∀ x, p x → r, from
  assume w: α, show p w → r, from
    assume hpw: p w, show r, from
      h ⟨w, hpw⟩
)

-- The predicate calculus example: (∃ x, p x → r) ↔ (∀ x, p x) → r 
-- is analogous to
-- the propositional calculus example: (P → r) ∨ (Q → r) ↔ P ∧ Q → r
-- First prove: (P ∧ Q → r) → (P → r) ∨ (Q → r)
-- and then modify it to be a proof of the predicate calculus example.

variables P Q : Prop

example : (P ∧ Q → r) → (P → r) ∨ (Q → r) :=
assume h: P ∧ Q → r, show (P → r) ∨ (Q → r), from
or.elim (em r)
(assume hr: r, show (P → r) ∨ (Q → r), from
  or.inl (assume hP: P, hr)
)
(assume hnr: ¬r, show (P → r) ∨ (Q → r), from
  or.elim (em P)
  (assume hP: P,show (P → r) ∨ (Q → r), from
    or.elim (em Q)
    (assume hQ: Q, 
      have hPQ: P ∧ Q := and.intro hP hQ,
      have hr: r := h hPQ,
      show (P → r) ∨ (Q → r), from
      absurd hr hnr
    ) 
    (assume hnQ: ¬Q, 
    have hQr : Q → r := (assume hQ: Q, show r, from absurd hQ hnQ),
    show (P → r) ∨ (Q → r), from or.inr hQr)
  )
  (assume hnP: ¬P,
    have hPr : P → r := (assume hP: P, show r, from absurd hP hnP),
    show (P → r) ∨ (Q → r), from or.inl hPr
  )
)

-- In the above proof we first use em on r.
-- The proof when r holds is trivial since anything implies r.
-- We then deal with the case when ¬ r holds.
-- Then we examine each conjunct and apply em to it.
-- I need the following lemma, which I proved in an example above.

lemma not_forall_exists_not : ¬ (∀ x: α, p x) → ∃ x, ¬(p x) :=
assume h: ¬ ∀ x: α, p x, show ∃ x, ¬(p x), from
by_contradiction
  (assume h1: ¬(∃ x, ¬(p x)), show false, from
    have h2: ∀ x, p x :=
      (assume w: α, show p w, from
        or.elim (em (p w))
        (assume hpw: p w, hpw)
        (assume hnpw: ¬ p w, absurd (exists.intro w hnpw)  h1)
      ),
    h h2
  )

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
iff.intro
(assume h: ∃ x, p x → r, show (∀ x, p x) → r, from
  match h with ⟨w, hw⟩ :=
    assume h1: ∀ x, p x, show r, from
    have h2: p w := h1 w,
    hw h2
  end
)
(assume h: (∀ x, p x) → r, show ∃ x, p x → r, from
  by_cases
  (assume hr: r, 
    have h1: ∀ x: α, p x → r := assume w: α, assume hw: p w, hr,
    show ∃ x, p x → r, from
    ⟨a, h1 a⟩
  )
  (assume hnr: ¬r, show ∃ x, p x → r, from 
    by_cases
    (assume h1: ∀ x, p x, show ∃ x, p x → r, from
      absurd (h h1) hnr
    )
    (assume h1: ¬ ∀ x, p x, 
      have h2: ∃ x, ¬ (p x) := not_forall_exists_not α p h1,
      show ∃ x, p x → r, from 
        match h2 with ⟨w, hw⟩ :=
          have hpwr : p w → r := (assume hpw, absurd hpw hw),
          ⟨w, hpwr⟩ 
        end
    )
  )
)

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
iff.intro
(assume h: ∃ x, r → p x, show r → ∃ x, p x, from 
  assume hr: r, show ∃ x, p x, from
  match h with ⟨w, hw⟩ :=
    have hpw: p w := hw hr,
    ⟨w, hpw⟩ 
  end
)
(assume h: r → ∃ x, p x, show ∃ x, r → p x, from 
  by_cases
    (assume hr: r, 
      have hepx : ∃ x, p x := h hr,
      show ∃ x, r → p x, from
      match hepx with ⟨w, hpw⟩ :=
        have hrpw : r → p w := (assume hr1: r, hpw),
        ⟨w, hrpw⟩ 
      end
    )
    (assume hnr: ¬r,
      have hrpa: r → p a := (assume hr: r, absurd hr hnr),
      ⟨a, hrpa⟩ 
    )
)

#check @by_cases

#check @by_contradiction
