signature {
propositions { s, t, a, b, c, d }
nominals { }
relations { br }
}

theory

{
  s;
  []false;
  [br](s --> [br]!s);
  [br](!s --> []!s);

  <br>(!s & t & <br>( !s & !t &
           a & !b & !c & !d &
  <>(!s & !a &  b & !c & !d &
  <>(!s & !a & !b &  c & !d &
  <>(!s & !a & !b & !c &  d
  )))));

}
