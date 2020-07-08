lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin
induction c with h hd,
rw add_zero,
rw add_zero,
refl,
rw add_succ,
rw add_succ,
rw add_succ,
rw hd,
refl,
end
