signature {
propositions { s, a, b, c }
nominals { }
relations { br }
}

theory

{
  s;
  []false;
  [br](s --> [br]!s);
  [br](!s --> []!s);

  <br>(!s & <br>(!s & a & !b & !c & <>(!s & !a & b & !c &  <>(!s & !a & !b & c ))
                ));
}
