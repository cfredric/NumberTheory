module Main where

import NumberTheory
import Test.HUnit

main :: IO Counts
main = runTestTT tests

tests :: Test
tests = TestList [ TestLabel "Continued Fraction Tests" continuedFractionTests
                , TestLabel "Pythagorean Triples Tests" pythTests
                ]

pythTests :: Test
pythTests = TestList $
    [ TestCase $ assertEqual "test pythSide" [(35, 12, 37),(37, 684, 685)] (pythSide (37 :: Int))
    , TestCase $ assertEqual "test pythLeg" [(15, 8, 17),(15, 20, 25),(15, 36, 39),(15, 112, 113)] (pythLeg (15 :: Int))
    , TestCase $ assertEqual "test pythHyp" [(7, 24, 25),(15, 20, 25)] (pythHyp (25 :: Int))
    ]

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
