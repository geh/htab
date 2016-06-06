signature {
propositions { a, b }
nominals { }
relations { sb }
}

theory

{
 <>(a & !b & <><>a);
 <>(b & !a & <><>b);
 [sb](a --> [][]!a);
 [sb](b --> [][]!b);
}
