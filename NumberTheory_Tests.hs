module Main where

import Data.List
import qualified Data.Numbers.Primes as Primes
import NumberTheory
import Test.HUnit

main :: IO Counts
main = runTestTT tests

tests :: Test
tests = TestList
    [ TestLabel "Continued Fraction Tests" continuedFractionTests
    , TestLabel "Pythagorean Triples Tests" pythTests
    , TestLabel "Z mod M Tests" zModMTests
    , TestLabel "Z Tests" zTests
    , TestLabel "Arithmetic Functions tests" arithmeticFnsTests
    , TestLabel "Gaussian Integer Tests" gaussianIntTests
    ]

limit :: [a] -> [a]
limit = take 20000
--limit = id

pythTests :: Test
pythTests = TestList
    [ TestCase $ assertEqual "test pythSide" [(35, 12, 37),(37, 684, 685)] (pythSide (37 :: Int))
    , TestCase $ assertEqual "test pythLeg" [(15, 8, 17),(15, 20, 25),(15, 36, 39),(15, 112, 113)] (pythLeg (15 :: Int))
    , TestCase $ assertEqual "test pythHyp" [(7, 24, 25),(15, 20, 25)] (pythHyp (25 :: Int))
    ]

-- Note: don't use any functions from NumberTheory to define these (e.g. isPrime).
sampleMixed :: [Integer]
sampleMixed = [1 .. 100]
samplePrimes :: [Integer]
samplePrimes = takeWhile (<= last sampleMixed) Primes.primes
sampleComposites :: [Integer]
sampleComposites = filter (not . flip elem samplePrimes) sampleMixed
sampleMixedGaussInts :: [GaussInt Integer]
sampleMixedGaussInts = [a :+ b | a <- [-25 .. 25], b <- [-25 .. 25]]

zTests :: Test
zTests = TestList
    [ TestList $ limit [ TestCase $ assertEqual "divisors divide evenly" 0 remainder
                | n <- sampleMixed
                , let divs = divisors n
                , d <- divs
                , let remainder = n `mod` d
                ]
    , TestList $ limit [ TestCase $ assertEqual "primes are only divisible by themselves and 1" [1, p] divs
                | p <- samplePrimes
                , let divs = divisors p
                ]
    , TestList $ limit [ TestCase $ assertBool "each divisor has a mate to produce n" found
                | n <- sampleMixed
                , let divs = divisors n
                , d <- divs
                , let found = any (\d' -> d * d' == n) divs
                ]
    , TestList $ limit [ TestCase $ assertEqual "product of factors from factorize is original" n prod
                | n <- sampleMixed
                , let facs = (factorize :: Integer -> [(Integer, Integer)]) n
                , let prod = product $ map (uncurry (^)) facs
                ]
    , TestList $ limit [ TestCase $ assertEqual "test primes on primes" [p] ps
                | p <- samplePrimes
                , let ps = primes p
                ]
    , TestList $ limit [ TestCase $ assertBool "test primes on composites" res
                | n <- sampleMixed
                , let res = all isPrime $ primes n
                ]
    , TestList $ limit [ TestCase $ assertBool "test isPrime on primes" (isPrime p)
                | p <- samplePrimes
                ]
    , TestList $ limit [ TestCase $ assertBool "test isPrime on composites" (not $ isPrime n)
                | n <- sampleComposites
                ]
    , TestList $ limit [ TestCase $ assertBool "test areCoprime on common multiples" res
                | x <- [1 .. 10] :: [Integer]
                , let res = not $ areCoprime 5 (5 * x)
                ]
    , TestList $ limit [ TestCase $ assertBool "test areCoprime on primes" res
                | p <- delete 3 samplePrimes
                , let res = areCoprime 3 p
                ]
    ]

zModMTests :: Test
zModMTests = TestList
    [ TestList $ limit [ TestCase $ assertBool
                    ("test canon bounds: " ++ show n ++ " mod " ++ show m)
                    (n' >= 0 && n' < m && n `mod` m == n')
                    | m <- sampleMixed
                    , n <- sampleMixed ++ map negate sampleMixed
                    , let n' = canon n m
                ]
    , TestCase $ assertEqual "test evalPoly" 2 (evalPoly 5 3 [4, 5, 6 :: Integer])
    , TestCase $ assertEqual "test polyCong" [1, 4] (polyCong 5 [4, 5, 6 :: Integer])
    , TestCase $ assertEqual "test exponentiate" 3 (exponentiate 9 12 (6 :: Integer))
    , TestCase $ assertEqual "test exponentiate negative" 3 (exponentiate (-9) 12 (6 :: Integer))
    , TestList $ limit [ TestCase $ assertEqual ("test inverses with exponentiation (" ++ show x ++ "^" ++ show e ++ " mod " ++ show n ++ ")") 1 p
                | n <- sampleMixed
                , let us = units n
                , u <- us
                , e <- [1 .. genericLength us]
                , let x = exponentiate u e n
                , let y = exponentiate u (-e) n
                , let p = canon (x * y) n
                ]
    , TestList $ limit [ TestCase $ assertBool "test rsaGenKeys (ed == 1 mod phi(n))" (canon (privk * pubk) (totient n) == (1 :: Integer) && n == n')
                | p <- samplePrimes
                , q <- delete p samplePrimes
                , let (Right keys) = rsaGenKeys p q
                , ((pubk, n), (privk, n')) <- keys
                ]
    , TestList $ limit [ TestCase $ assertEqual "test rsaGenKeys (inverses)" text plain
                | text <- sampleMixed
                , p <- samplePrimes
                , q <- delete p samplePrimes
                , let (Right keys) = rsaGenKeys p q
                , (pub, priv) <- keys
                , let (Right cipher) = rsaEval pub text
                , let (Right plain) = rsaEval priv cipher
                ]
    , TestList $ limit [ TestCase $ assertBool
                    ("test units invertibility: " ++ show n)
                    (all (\u -> any (\u' -> canon (u * u') n == 1) us) us)
                | n <- sampleMixed
                , let us = units n
                ]
    , TestList $ limit [ TestCase $ assertBool
                    ("test nilpotents: " ++ show n)
                    (all (\xs ->  0 `elem` xs) iteratedLists)
                | n <- sampleMixed
                , let ns = map fromIntegral $ nilpotents n
                , let iteratedLists = map (\x -> take (fromIntegral n) $ iterate (\l -> canon (l * x) n) x) ns
                ]
    , TestList $ limit [ TestCase $ assertBool
                    ("test idempotents: " ++ show n)
                    (all (\i -> canon (i * i) n == i) is)
                | n <- sampleMixed
                , let is = idempotents n
                ]
    , TestCase $ assertEqual "test roots" [3, 5, 6, 7, 10, 11, 12, 14] (roots (17 :: Integer))
    , TestCase $ assertEqual "test almostRoots" [2, 7, 8, 13] (almostRoots (15 :: Integer))
    , TestCase $ assertEqual "test orders" [1, 4, 2, 4, 4, 2, 4, 2] (orders (15 :: Integer))
    , TestCase $ assertEqual "test expressAsRoots" [(-2, 1), (7, 3), (-8, 3), (13, 1)] (expressAsRoots 13 (15 :: Integer))
    , TestCase $ assertEqual "test powerCong" [2] (powerCong 11 3 (5 :: Integer))
    ]

arithmeticFnsTests :: Test
arithmeticFnsTests = TestList
    [ TestList $ limit [ TestCase $ assertEqual "totient counts number of coprimes <=n" c c'
                | n <- sampleMixed
                , let c = totient n
                , let c' = genericLength $ filter (areCoprime n) [1 .. n]
                ]
    , TestCase $ assertEqual "legendre 3 5" (Right (-1 :: Integer)) (legendre 3 5)
    , TestCase $ assertEqual "legendre checks prime input" (Left "p is not prime") (legendre 3 (4 :: Integer))
    , TestCase $ assertEqual "kronecker 6 5" (Right (1 :: Integer)) (kronecker 6 5)
    , TestCase $ assertEqual "tau 60" (12 :: Integer) (tau 60)
    , TestCase $ assertEqual "sigma 1 60" (168 :: Integer) (sigma 1 60)
    , TestCase $ assertEqual "sigma 4 60" (14013636 :: Integer) (sigma 4 60)
    , TestCase $ assertEqual "mobius 9 (non-squarefree)" (0 :: Integer) (mobius 9)
    , TestCase $ assertEqual "mobius 5" (-1 :: Integer) (mobius 5)
    , TestCase $ assertEqual "littleOmega 60" (3 :: Integer) (littleOmega 60)
    , TestCase $ assertEqual "bigOmega 60" (4 :: Integer) (bigOmega 60)
    ]

gaussianIntTests :: Test
gaussianIntTests = TestList
    [ TestList $ limit [ TestCase $ assertEqual "conjugate with 0i" g g'
                | n <- sampleMixed
                , let g = n :+ 0
                , let g' = conjugate g
                ]
    , TestList $ limit [ TestCase $ assertEqual "conjugate mixed ints" (a :+ b) (a' :+ (-b'))
                | g@(a :+ b) <- sampleMixedGaussInts
                , let (a' :+ b') = conjugate g
                ]
    , TestCase $ assertEqual "Gaussian int multiplication" ((2 :: Integer) :+ 42) ((5 :+ 3) .* (4 :+ 6))
    , TestCase $ assertEqual "Gaussian div on even division" ((4 :: Integer) :+ 6) ((2 :+ 42) ./ (5 :+ 3))
    , TestCase $ assertEqual "Gaussian div on uneven division" ((4 :: Integer) :+ 6) ((2 :+ 43) ./ (5 :+ 3))
    , TestCase $ assertEqual "Gaussian div on negative divisor" ((4 :: Integer) :+ 6) (((-2) :+ (-43)) ./ ((-5) :+ (-3)))
    , TestCase $ assertEqual "Gaussian mod on positive case" ((0 :: Integer) :+ 1) ((2 :+ 43) .% (5 :+ 3))
    , TestCase $ assertEqual "Gaussian mod on negative case" ((0 :: Integer) :+ (-1)) (((-2) :+ (-43)) .% (5 :+ 3))
    , TestCase $ assertEqual "magnitude on integer case" (25 :: Integer) (magnitude (5 :+ 0))
    , TestCase $ assertEqual "magnitude on 5 :+ 3" (34 :: Integer) (magnitude (5 :+ 3))
    , TestCase $ assertBool "gIsPrime on prime" (gIsPrime ((2 :: Integer) :+ 5))
    , TestCase $ assertBool "gIsPrime on composite" (not $ gIsPrime ((3 :: Integer) :+ 5))
    , TestList $ limit [ TestCase $ assertBool "gPrimes generates primes" (gIsPrime p)
                | p <- take 100 (gPrimes :: [GaussInt Integer])
                ]
    , TestCase $ assertEqual "gGCD on even multiple" ((2 :: Integer) :+ 4) (gGCD (2 :+ 4) (12 :+ 24))
    , TestCase $ assertEqual "gGCD on uneven multiple" ((1 :: Integer) :+ 1) (gGCD (2 :+ 4) (5 :+ 3))
    , TestCase $ assertBool "gGCD on uneven multiple (division rounding test)"
            (gGCD ((12::Int) :+ 23) (23 :+ 34) `elem` [x :+ y | x <- [(-1)..1], y <- [(-1)..1], abs x + abs y == 1])
    , TestCase $ assertBool "gFindPrime 5" (head (gFindPrime (5::Int)) `elem` [ a :+ b | a <- [2, -2], b <- [1, -1]])
    , TestCase $ assertEqual "gFindPrime 7" [] (gFindPrime (7::Int))
    , TestList $ limit [ TestCase $ assertEqual "gExponentiate on real ints" ((a ^ pow) :+ 0) (gExponentiate g pow)
                | a <- sampleMixed
                , pow <- [1 .. 5] :: [Integer]
                , let g = a :+ 0
                ]
    , TestCase $ assertEqual "gExponentiate on 1st complex int" ((-119 :: Integer) :+ (-120)) (gExponentiate (2 :+ 3) (4 :: Integer))
    , TestCase $ assertEqual "gExponentiate on 2nd complex int" ((122 :: Integer) :+ (-597)) (gExponentiate (2 :+ 3) (5 :: Integer))
    , TestList $ limit [ TestCase $ assertEqual "gFactorize, gMultiply, gExponentiate recover original GaussInt"
                        g prod
                | g <- sampleMixedGaussInts
                , let factors = gFactorize g
                , let condensedFactors = map (uncurry gExponentiate) factors
                , let prod = foldl (.*) (1 :+ 0) condensedFactors
                ]
    ]

continuedFractionTests :: Test
continuedFractionTests = TestList
    [ TestCase $ assertBool ("Test conversion to and from continued fraction: (" ++ show m ++ "+ sqrt(" ++ show d ++ "))/" ++ show q)
       (abs (((fromIntegral m + (sqrt :: Double -> Double) (fromIntegral d)) / fromIntegral q) -
        (fromRational . continuedFractionToRational $ continuedFractionFromQuadratic m d q))
        < 0.00000000000001)
    | m <- [0 .. 20]
    , d <- [0 .. 20]
    , q <- [1 .. 20]
    ]
