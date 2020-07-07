theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin
intros f h j,
cases b with b,
apply h,
refl,
cases a with a,
apply f,
refl,
rw mul_succ at j,
rw add_succ at j,
exfalso,
exact succ_ne_zero _ j,
end
