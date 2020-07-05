lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin
induction c with h hd,
repeat {rw mul_zero},
rw mul_succ,
rw mul_succ,
rwa [hd, mul_add],
end
