module Main where

import NumberTheory
import Test.HUnit

main :: IO Counts
main = runTestTT tests

tests :: Test
tests = TestList [ TestLabel "Continued Fraction Tests" continuedFractionTests
                , TestLabel "Pythagorean Triples Tests" pythTests
                , TestLabel "Z mod M Tests" zModMTests
                ]

pythTests :: Test
pythTests = TestList $
    [ TestCase $ assertEqual "test pythSide" [(35, 12, 37),(37, 684, 685)] (pythSide (37 :: Int))
    , TestCase $ assertEqual "test pythLeg" [(15, 8, 17),(15, 20, 25),(15, 36, 39),(15, 112, 113)] (pythLeg (15 :: Int))
    , TestCase $ assertEqual "test pythHyp" [(7, 24, 25),(15, 20, 25)] (pythHyp (25 :: Int))
    ]

sampleMixed :: [Integer]
sampleMixed = [1..100]

zModMTests :: Test
zModMTests = TestList
    [ TestList $ [ TestCase $ assertBool
                    ("test canon bounds: " ++ (show n) ++ " mod " ++ (show m))
                    (n' >= 0 && n' < m && n `mod` m == n')
                    | let m = 37
                    , n <- sampleMixed ++ (map negate sampleMixed)
                    , let n' = canon n m
                ]
    , TestCase $ assertEqual "test evalPoly" 2 (evalPoly 5 3 [4, 5, (6 :: Integer)])
    , TestCase $ assertEqual "test polyCong" ([1,4]) (polyCong 5 [4, 5, (6 :: Integer)])
    , TestCase $ assertEqual "test exponentiate" 3 (exponentiate 9 12 (6 :: Integer))
    , TestCase $ assertEqual "test exponentiate negative" 3 (exponentiate (-9) 12 (6 :: Integer))
    , TestList [ TestCase $ assertBool "test rsaGenKeys (ed == 1 mod phi(n))" (canon (privk * pubk) (totient n) == 1 && n == n')
                | let (Right keys) = rsaGenKeys 37 41
                , ((pubk, n), (privk, n')) <- keys
                ]
    , TestList [ TestCase $ assertBool "test rsaGenKeys (inverses)" (plain == text)
                | let text = 77
                , let (Right keys) = rsaGenKeys 19 23
                , (pub, priv) <- keys
                , let (Right cipher) = rsaEval pub text
                , let (Right plain) = rsaEval priv cipher
                ]
    , TestList [ TestCase $ assertBool
                    ("test units invertibility: " ++ (show n))
                    (and $ map (\u -> any (\u' -> canon (u * u') n == 1) us) us)
                | n <- sampleMixed
                , let us = units n
                ]
    , TestList [ TestCase $ assertBool
                    ("test nilpotents: " ++ (show n))
                    (and $ map (\xs -> any (== 0) xs) iteratedLists)
                | n <- sampleMixed
                , let ns = map fromIntegral $ nilpotents n
                , let iteratedLists = map (\x -> take (fromIntegral n) $ iterate (\l -> canon (l * x) n) x) ns
                ]
    , TestList [ TestCase $ assertBool
                    ("test idempotents: " ++ (show n))
                    (and $ map (\i -> canon (i * i) n == i) is)
                | n <- sampleMixed
                , let is = idempotents n
                ]
    , TestCase $ assertEqual "test roots" [3, 5, 6, 7, 10, 11, 12, 14] (roots (17 :: Integer))
    , TestCase $ assertEqual "test almostRoots" [2, 7, 8, 13] (almostRoots (15 :: Integer))
    , TestCase $ assertEqual "test orders" [1, 4, 2, 4, 4, 2, 4, 2] (orders (15 :: Integer))
    , TestCase $ assertEqual "test expressAsRoots" [(-2, 1), (7, 3), (-8, 3), (13, 1)] (expressAsRoots 13 (15 :: Integer))
    , TestCase $ assertEqual "test powerCong" [2] (powerCong 11 3 (5 :: Integer))
    ]

continuedFractionTests :: Test
continuedFractionTests = TestList
    [ TestCase $ assertBool ("Test conversion to and from continued fraction: (" ++ (show m) ++ "+ sqrt(" ++ (show d) ++ "))/" ++ (show q))
       (abs ((((fromIntegral m) + ((sqrt :: Double -> Double) $ fromIntegral d)) / (fromIntegral q)) -
        (fromRational . continuedFractionToRational $ continuedFractionFromQuadratic m d q))
        < 0.00000000000001)
    | m <- [0 .. 20]
    , d <- [0 .. 20]
    , q <- [1 .. 20]
    ]
