signature {
propositions { p }
nominals { }
relations { sw }
}

theory

{
  <>p;
  <>!p;
  []<> true;
  [][][] false;
  [sw][][sw][][] false;
  [][sw][][] false;
  <sw><sw><><><><><> true;
}
