signature {
propositions { s }
nominals { }
relations { sb, gsb }
}

theory

{
  s;
  []!s;
  <> true;
  [](  <>s &   <gsb>!<>s );
  []<>!s;
  [][]( !s --> ( <>s  & <gsb>!<>s) );
  [gsb]( (<>(<>s  & <>(!s & !<>s)) )  -->  <>!<>s);
  [gsb][]( (!<>s)   -->  []<>s );
  [gsb](!<>( (!<>s) & <><>( !s & (<>s) & <>!<>s)));
  [gsb][gsb]( (<>((!<>s) & <><>(!s & !<>s))) --> <>(!<>s & <>!<>s));
}
