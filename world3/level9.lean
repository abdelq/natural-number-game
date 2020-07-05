lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin
rw ← mul_assoc,
rw mul_comm a,
rw mul_assoc,
refl,
end
