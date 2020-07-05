lemma pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n :=
begin
induction n with h hd,
rwa [add_zero, pow_zero, mul_one],
rw pow_succ,
rw add_succ,
rw pow_succ,
rw hd,
rw mul_assoc,
refl,
end
