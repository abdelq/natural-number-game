lemma zero_le (a : mynat) : 0 ≤ a :=
begin
rw le_iff_exists_add,
use a,
rwa zero_add,
end
