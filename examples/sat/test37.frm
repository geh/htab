% sat
% may be found unsatisfiable if the dependencies are not
% correctly propagated when [] constraints and accessibility
% formulas meet, after an equivalence class merge

signature { automatic } theory

{
N1;
<><>(N2 & P1);
E false v [](N1 v E true);
[](!P1 v N2:(N1 & !P1))
}
