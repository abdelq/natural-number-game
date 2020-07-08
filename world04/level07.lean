lemma pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n) :=
begin
induction n with h hd,
rw mul_zero,
repeat {rw pow_zero},
rw pow_succ,
rw hd,
rw mul_succ,
rwa pow_add,
end
