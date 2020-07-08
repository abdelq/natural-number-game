theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin
cases hab,
cases hbc,
use (hab_w + hbc_w),
rw ← add_assoc,
rw hbc_h,
rw hab_h,
refl,
end
