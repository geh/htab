signature {
propositions { s, a, b, c }
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


  <>(a & !b & !c & <>(!s & !a & b & !c &  <>(!s & !a & !b & c )));
}
