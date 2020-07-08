theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a :=
begin
revert a,
induction b with d hd,
intro a,
right,
exact zero_le _,
intro a,
cases a,
left,
exact zero_le _,
cases hd a,
left,
exact succ_le_succ _ _ h,
right,
exact succ_le_succ _ _ h,
end
