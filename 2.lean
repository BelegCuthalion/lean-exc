def curry (α β γ : Type) (f : α × β → γ) : α → β → γ :=
begin
  assume a b,
  exact f ⟨a,b⟩
end

def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ :=
begin
  assume p,
  exact f p.1 p.2
end