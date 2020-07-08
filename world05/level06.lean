example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
intro f,
intro h,
intro p,
apply (f p),
apply (h p),
end
