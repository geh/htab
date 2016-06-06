signature {
propositions { a, b }
nominals { }
relations { sw }
}

theory

{
  <>(a & !b);
  <>(b & !a);
  []<> true;
  [][][] false;
  [sw][][sw][][] false;
  [][sw][][] false;
  <sw><sw><><><><><> true;
}
