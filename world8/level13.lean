lemma ne_succ_self (n : mynat) : n ≠ succ n :=
begin
induction n with h hd,
apply zero_ne_succ,
intro hs,
apply hd,
apply succ_inj,
exact hs,
end
