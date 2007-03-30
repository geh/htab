module Main
where

import Test.HUnit
import SimpleClauseTest(testSimpleClause)

main :: IO Counts
main = runTestTT testSimpleClause