lemma lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b :=
begin
intro h,
cases h with h1 h2,
cases h1 with d hd,
cases d,
exfalso,
apply h2,
rw hd,
rw add_zero,
exact le_refl a,
use d,
rw hd,
rw add_succ,
rw succ_add,
refl,
end
