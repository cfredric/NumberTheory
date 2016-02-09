module Main where

import NumberTheory
import Test.HUnit


main = runTestTT testcase


testcase = TestCase $ assertEqual "Should factorize" [(3,1), (5,1)] (factorize 15)
