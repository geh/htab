signature {
propositions { a, b }
nominals { }
relations { sw }
}

theory

{
  <>(a & !b & <>a);
  <>(b & !a & <>b);
  [sw][][sw][][] false;
  [][sw][][] false;
  <sw><sw><><><><><> true;
}
