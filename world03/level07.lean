lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t :=
begin
induction t with h hd,
repeat {rw mul_zero},
refl,
repeat {rw mul_succ},
rw hd,
rw add_right_comm,
rw add_assoc,
rw add_assoc,
rw add_comm (b * h),
rw add_assoc,
refl,
end
