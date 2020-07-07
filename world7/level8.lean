lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
split,
cc,
intro h,
cases h with hpq hpr,
cases hpq with p q,
split,
exact p,
left,
exact q,
cases hpr with p r,
split,
exact p,
right,
exact r,
end
