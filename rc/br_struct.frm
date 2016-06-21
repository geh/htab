signature {
propositions { s, a, b, c, d }
nominals { }
relations { br }
}

theory

{
  s;
  []false;
  [br](s --> [br]!s);
  [br](!s --> []!s);

  <br>(!s & <br>(
     !s &  a & !b & !c & !d &
  <>(!s & !a &  b & !c & !d &
  <>(!s & !a & !b &  c & !d &
  <>(!s & !a & !b & !c &  d
  )))));

}
