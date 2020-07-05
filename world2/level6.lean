lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin
rw add_assoc,
rw add_assoc,
rw add_comm b,
refl,
end
