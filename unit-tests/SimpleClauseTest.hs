module SimpleClauseTest(testSimpleClause)
where

import Test.HUnit
import Formula
import SimpleClause

p1, p2 :: Formula
p1 = prop 1
p2 = prop 2

testSimpleClause = TestCase (assertBool "order among propositions failed" (p2 > p1))
