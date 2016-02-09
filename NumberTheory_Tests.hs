module Main where

import NumberTheory
import Test.HUnit

main :: IO Counts
main = runTestTT tests

tests :: Test
tests = TestList [TestLabel "Continued Fraction Tests" continuedFractionTests]

continuedFractionTests :: Test
continuedFractionTests = TestList $
    [ TestCase $ assertBool ("Test conversion to and from continued fraction: (" ++ (show m) ++ "+ sqrt(" ++ (show d) ++ "))/" ++ (show q))
       (abs ((((fromIntegral m) + ((sqrt :: Double -> Double) $ fromIntegral d)) / (fromIntegral q)) -
        (fromRational . continuedFractionToRational $ continuedFractionFromQuadratic m d q))
        < 0.00000000000001)
    | m <- [0 .. 20]
    , d <- [0 .. 20]
    , q <- [1 .. 20]
    ]
