lemma one_mul (m : mynat) : 1 * m = m :=
begin
induction m with h hd,
rw mul_zero,
refl,
rw mul_succ,
rw hd,
rw succ_eq_add_one,
refl,
end
