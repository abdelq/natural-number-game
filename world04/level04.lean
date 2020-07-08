lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 :=
begin
induction m with h hd,
rwa pow_zero,
rw pow_succ,
rw hd,
refl,
end
