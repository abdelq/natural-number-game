lemma lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) :=
begin
intro h,
split,
apply le_trans _ (succ a),
exact le_succ_self a,
exact h,
intro h2,
apply not_succ_le_self a,
exact le_trans (succ a) b a h h2,
end
