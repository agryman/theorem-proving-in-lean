-- 4.4 The Existential Quantifier

open nat

example : ∃ x : ℕ, x > 0 :=
have h : 1 > 0, from zero_lt_succ 0,
exists.intro 1 h

#print zero_lt_succ

example (x : ℕ ) (h : x > 0) : ∃ y, y < x :=
exists.intro 0 h

example (x y z : ℕ ) (hxy : x < y) (hyz : y < z) :
  ∃ w, x < w ∧ w < z :=
exists.intro y (and.intro hxy hyz)

#check @exists.intro

example : ∃ x : ℕ, x > 0 :=
⟨ 1, zero_lt_succ 0 ⟩

example (x : ℕ ) (h : x > 0) : ∃ y, y < x :=
⟨0, h⟩ 

example (x y z : ℕ ) (hxy : x < y) (hyz : y < z) :
  ∃ w, x < w ∧ w < z :=
⟨y, hxy, hyz⟩

variable g : ℕ → ℕ → ℕ
variable hg : g 0 0 = 0

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩
 

set_option pp.implicit true -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

variables (α : Type*) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
exists.elim h
  (assume w,
    assume hw : p w ∧ q w,
    show ∃ x, q x ∧ p x,
    from ⟨ w, hw.right, hw.left⟩ )

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨ w, hw⟩ :=
  ⟨ w, ⟨ hw.right, hw.left⟩ ⟩
end

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨ (w : α ), (hw : p w ∧ q w) ⟩ :=
  ⟨ w, ⟨ hw.right, hw.left ⟩ ⟩
end

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨ w, ⟨ hpw, hqw ⟩ ⟩ :=
  ⟨ w, ⟨ hqw, hpw ⟩ ⟩
end

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
let ⟨w, hpw, hqw⟩ := h in ⟨w, hqw, hpw⟩

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩
