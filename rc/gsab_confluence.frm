signature {
propositions { a, b, c }
nominals { }
relations { gsb }
}

theory

{
 <>(a & !b &  <><>a );
 <>(b & !a &  <><>b );
 [][](c & []!c);
 <gsb>[][][] false;
}
