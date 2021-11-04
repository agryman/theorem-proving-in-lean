local notation `[` a `**` b `]` := a * b + 1
local infix `<*>`:50 := λ a b : ℕ, a * a * b * b

#reduce [2**3]
#reduce 2<*>3

