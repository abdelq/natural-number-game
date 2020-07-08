example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) :=
begin
intro f,
intro h,
intro p,
exact h(f(p)),
end
