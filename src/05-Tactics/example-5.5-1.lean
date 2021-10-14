-- 5.5 Tactic Combinators

example (p q : Prop) (hp : p) : p ∨ q :=
begin left, assumption end

example (p q : Prop) (hp : p) : p ∨ q :=
by { left, assumption }

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
by split; assumption

example (p q : Prop) (hp : p) : p ∨ q :=
by {left, assumption} <|> {right, assumption}

example (p q : Prop) (hq : q) : p ∨ q :=
by {left, assumption} <|> {right, assumption}

example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
by repeat {{left, assumption} <|> right <|> assumption}

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
by repeat {{left, assumption} <|> right <|> assumption}

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
by repeat {{left, assumption} <|> right <|> assumption}

meta def my_tac : tactic unit :=
`[ repeat {{left, assumption} <|> right <|> assumption}]

example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
by my_tac

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
by my_tac

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
by my_tac

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r :=
by split; try {split}; assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r :=
begin
  split,
  all_goals {try {split}},
  all_goals {assumption}
end

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r :=
begin
  split,
  any_goals {split},
  any_goals {assumption}
end

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
begin
  repeat { any_goals { split }},
  all_goals { assumption }
end

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
by repeat { any_goals { split <|> assumption} }
