lemma add_right_eq_zero {a b : mynat} : a + b = 0 → a = 0 :=
begin
cases a with d,
intro h,
refl,
intro h,
rw succ_add at h,
exfalso,
apply succ_ne_zero (d + b),
exact h,
end
