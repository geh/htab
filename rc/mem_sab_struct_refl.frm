signature {
propositions { s, a, b, c }
nominals { }
relations { sb }
}

theory

{
  s;
  []!s;

  []<>s;
  [sb][sb](s --> []<>s);
  [][sb](s --> <>[]!s);

  [][](!s --> <>s);
  [][][](s --> []<>s);
  [][][sb](  s --> <>[]!s);

  [][sb](s --> [sb]( ([]!s) --> [][](s --> []<>s)));
  [][sb](s --> [](([]!s) --> [][](s --> <>[]!s)));


  <>( <sb>(s & <sb>( (!<>s) &  <>(  (!<>s ) ) ) ) );
}
