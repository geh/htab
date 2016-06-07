signature {
propositions { s }
nominals { }
relations { br, gbr }
}

theory

{
  s;
  [] false;
  [br](s --> [br]!s);
  [br](!s --> [] !s);
  <br><br> true;
  [br]<> true;
  [br][br](s --> [](!s --> [][]!s));
  [br][][][br](s --> <>( !s & <><>s ));
}
