signature {
propositions { s }
nominals { }
relations { sw }
}

theory

{
  s;
  []!s;
  [][]!s;
  [][][]!s;
  [][][][]!s;
  [][][][][]!s;
  [][][][][][]!s;
  [][][][][][][]!s;
  [][][][][][][][]!s;
  [][][][][][][][][]!s;
  <> true;
  []<> true;
  [sw][sw](!s --> <><><><><>s);
  [sw][][]!s;
  [sw][sw][sw](([]!s) --> <><><>(!s & <><><>s));
}
