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
  [br][]!s;
}
