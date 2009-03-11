% satisfiable 
% found unsatisfiable if the branching dependencies are not copied
% to the right structures when there is an equivalence class merge

signature { automatic } theory

{

n1:[]false;
n2:<>true;
(<><>true ) v (n2 & n1)
}
