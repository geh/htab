signature {
propositions { s }
nominals { }
relations { gsw }
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
  [][][gsw][gsw][][](s --> <><><>s);
  [][gsw](<>s -> [][]!s);
  [][][][gsw][gsw][gsw]((<><><>s) --> <><><>(!s & <><><>s));
}
