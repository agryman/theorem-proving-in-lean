import data.nat.basic

variables (a b c d e : ℕ)
variable h1 : a = b
variable h2 : b = c + 1
variable h3 : c = d
variable h4 : e = 1 + d

theorem T : a = e :=
calc
  a   = b     : h1
  ... = c + 1 : h2
  ... = d + 1 : congr_arg _ h3
  ... = 1 + d : add_comm _ _
  ... = e     : eq.symm h4

include h1 h2 h3 h4
theorem T' : a = e :=
calc
  a   = b     : by rw h1
  ... = c + 1 : by rw h2
  ... = d + 1 : by rw h3
  ... = 1 + d : by rw add_comm
  ... = e     : by rw h4

#print T
#print T'

theorem T'' : a = e :=
calc
  a   = d + 1 : by rw [h1, h2, h3]
  ... = 1 + d : by rw add_comm
  ... = e     : by rw h4

#print T''

theorem T''' : a = e :=
by rw [h1, h2, h3, add_comm, h4]

#print T'''

theorem T₁ : a = e :=
by simp [h1, h2, h3, h4, add_comm]

#print T₁
