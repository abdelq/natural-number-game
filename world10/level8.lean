lemma succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b :=
begin
cases h with d hd,
use d,
rw hd,
rwa succ_add,
end
