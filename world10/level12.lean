theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b :=
begin
intro h,
cases h with d hd,
use d,
apply succ_inj,
rw ← succ_add,
exact hd,
end
