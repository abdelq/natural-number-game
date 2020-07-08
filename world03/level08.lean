lemma mul_comm (a b : mynat) : a * b = b * a :=
begin
induction a with h hd,
rw zero_mul,
rw mul_zero,
refl,
rw succ_mul,
rw mul_succ,
rw hd,
refl,
end
