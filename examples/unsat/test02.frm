signature { automatic } theory

{
 P1 | P2 | P3 | P4;
 !P1 | !P2;
 !(P1 --> ((P3 <--> P4) --> P1))
}
