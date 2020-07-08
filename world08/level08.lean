lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = 0 :=
begin
intro h,
apply add_left_cancel a,
rw add_zero,
exact h,
end
