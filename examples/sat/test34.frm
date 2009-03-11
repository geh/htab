% caused a problem of in the interaction between backjumping and equivalence classes

signature { automatic } theory
{
P1 v !N1:(!N1 v !P1);
N1 v !N1:(!N1 v P1);
P1 v N1:(!P1 v !N1);
!P1 v ![R1](!N1 v P1);
P1 v [R1](P1 v N1)
}
