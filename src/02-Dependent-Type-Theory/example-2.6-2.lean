section useful
variables (α β γ : Type*)
variables (g : β → γ) (f : α → β) (h : α → α)
variable x : α

def compose := g (f x)
end useful