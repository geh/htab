signature {
propositions { s, a, b, c, d }
nominals { }
relations { sw }
}

theory

{
  s;
  []!s;
  [](!s     --> ((<>(s & []false)) & [sw](s --> []!<>s)));
  [][](!s   --> ((<>(s & []false)) & [sw](s --> []!<>s)));
  [][][](!s --> ((<>(s & []false)) & [sw](s --> []!<>s)));

  [sw][sw][][][][](s --> [] false);
  [sw][sw](!s --> <sw>(s & <><><>(s & <>!<>s)));


  <>(!s &  a & !b & !c & !d &
  <>(!s & !a &  b & !c & !d &
  <>(!s & !a & !b &  c & !d &
  <>(!s & !a & !b & !c &  d
  ))));
}
