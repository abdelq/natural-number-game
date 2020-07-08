lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
intro hpq,
intro hqr,
cases hpq with hpq hqp,
cases hqr with hqr hrq,
split,
cc,
cc,
end
