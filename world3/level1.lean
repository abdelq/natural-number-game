import mynat.mul

lemma zero_mul (m : mynat) : 0 * m = 0 :=
begin
induction m with h hd,
rw mul_zero,
refl,
rw mul_succ,
rw add_zero,
rw hd,
refl,
end
