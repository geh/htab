signature {
propositions { p, q, a, b }
nominals { }
relations { gsb }
}

theory

{
 !a & !b & !p & !q;
 <>(p  & !a & !b & <> (q  & <> (!q & a) ));
 <>(!p & !a & !b & <> (q  & <> (!q & b) ));
 <gsb>[][][] false;
}
