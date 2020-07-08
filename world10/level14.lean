theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b :=
begin
cases h with d hd,
use d,
rw hd,
cc,
end
