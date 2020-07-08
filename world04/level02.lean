lemma zero_pow_succ (m : mynat) : (0 : mynat) ^ (succ m) = 0 :=
begin
rw pow_succ,
rwa mul_zero,
end
