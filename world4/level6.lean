lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n :=
begin
induction n with h hd,
repeat {rw pow_zero},
rwa mul_one,
repeat {rw pow_succ},
rw hd,
simp,
end
