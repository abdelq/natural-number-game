theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b :=
begin
intro h,
induction t with h hd,
rw ← add_zero a,
rw ← add_zero b,
exact h,
apply hd,
rw add_succ at h,
rw add_succ at h,
exact succ_inj(h),
end
