{ SAT
  caused a loop when the saturation for the difference modality was not exhaustive,
  ie when we did not check if the "second different word" was already created
}
begin
-N1; -P3;
D N1;
P3 v ( E(N1 v N1:P2) & A(N1 v E P3));
E(-P2 & B(-P3));
N1 v A(P2 v D(P3 v <>(P3 & N1)))
end
