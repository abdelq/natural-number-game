lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
repeat {rw not_iff_imp_false},
intro f,
intro q,
intro p,
apply q,
apply f,
exact p,
end
