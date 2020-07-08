import tactic.tauto
local attribute [instance, priority 10] classical.prop_decidable

lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=
begin
by_cases p : P; by_cases q : Q,
repeat {cc},
end
