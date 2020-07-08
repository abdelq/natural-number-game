theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) :=
begin
intro h,
cases h with c hc,
induction a with d hd,
rw succ_add at hc,
exact zero_ne_succ _ hc,
rw succ_add at hc,
apply hd,
apply succ_inj,
exact hc,
end
