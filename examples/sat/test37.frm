{sat}
{may be found unsatisfiable if the dependencies are not
correctly propagated when [] constraints and accessibility
formulas meet, after an equivalence class merge}

begin
N1;
<><>(N2 & P1);
Efalse v [](N1 v Etrue);
[](-P1 v N2:(N1 & -P1))
end
