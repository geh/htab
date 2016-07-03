signature {
propositions { s, t }
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
    <br>(s & <br>( (<>s) &  <>(!s & <>s)))
  ));
}
