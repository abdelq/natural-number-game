theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
begin
intro h,
intro t,
induction t with d hd,
rw add_zero,
rw add_zero,
exact h,
rw add_succ,
rw add_succ,
apply succ_le_succ,
exact hd,
end
