import tactic.tauto

lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q :=
begin
intro h,
cases h with p np,
rw not_iff_imp_false at np,
exfalso,
apply np,
exact p,
end
