signature {
propositions { s }
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
    <br>(s & <br>( (<>s) &  <>(!s & <>s)))
  ));
}
