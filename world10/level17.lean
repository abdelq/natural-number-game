definition lt (a b : mynat) := a ≤ b ∧ ¬ (b ≤ a)
instance : has_lt mynat := ⟨lt⟩

lemma lt_iff_succ_le (a b : mynat) : a < b ↔ succ a ≤ b :=
begin
split,
exact lt_aux_one a b,
exact lt_aux_two a b,
end
