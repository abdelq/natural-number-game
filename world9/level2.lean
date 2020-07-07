theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) :
  a = 0 ∨ b = 0 :=
begin
cases a with a,
left,
refl,
cases b with b,
right,
refl,
exfalso,
rw mul_succ at h,
rw add_succ at h,
exact succ_ne_zero _ h,
end
