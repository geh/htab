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

  [][sw](s --> [][][](s --> [] false));
  [][][sw](s --> [][][](s --> [] false));


  [sw][sw](!s --> <sw>(s & <><><sw>(s & <>!<>s)));


  <>( a & <sw>(s & <><>(!s & !<>s)));
}
