{-# LANGUAGE ScopedTypeVariables #-}
module NumTheory where

import           Control.Parallel.Strategies    (rdeepseq, parList, using)
import           Data.List                      ((\\), delete, findIndex, genericLength, nub, sort)
import qualified Data.Map             as Map    (fromListWith, toList)
import           Data.Monoid
import qualified Data.Numbers.Primes  as Primes (primes)
import           Data.Ratio                     ((%), denominator, numerator, Ratio)
import qualified Data.Set             as Set    (fromList, member, Set, size, toList)


fromRight :: Either a b -> b
fromRight (Right r) = r
fromRight _ = error "Not a right value!"

-- canonical representation of x in Zm
canon :: Integral a => a -> a -> a
canon x m
    | x < 0     = canon (x + m) m
    | otherwise = x `mod` m

-- square root of an integral value, for brevity elsewhere
sqrti :: Integral a => a -> Double
sqrti = (sqrt :: Double -> Double) . fromIntegral

isIntegral :: Double -> Bool
isIntegral x = (floor :: Double -> Integer) x == ceiling x

-- list of all pythagorean triples that include a given length (either as leg
-- or hypotenuse)
pythSide :: Integral a => a -> [(a, a, a)]
pythSide s = sort $ pythLeg s ++ pythHyp s

-- list of all pythagorean triples that include a given leg
pythLeg :: Integral a => a -> [(a, a, a)]
pythLeg leg = sort [ (k * a, k * b, k * c)
                   | k <- divisors leg
                   , (a, b, c) <- primPythLeg $ leg `quot` k
                   ]

-- list of all primitive pythagorean triples including a given leg
primPythLeg :: Integral a => a -> [(a, a, a)]
primPythLeg leg = -- (a, b, c) = (m^2-n^2, 2mn, m^2+n^2) for some integers m, n
    sort [ (a, b, c)
         | (m, n) <- findMN
         , let a = m * m - n * n
               b = 2 * m * n
               c = m * m + n * n
         ]
    where
    findMN
        | leg `mod` 2 == 0 =
            [ (m, n)
            | n <- divisors leg
            , let m = quot leg (2 * n)
            , areLegalParametersForPythTriple m n
            ]
        | otherwise =
            [ (m, n)
            | n <- [1 .. leg]
            , let x = sqrti $ leg + n * n
            , isIntegral x
            , let m = floor x
            , areLegalParametersForPythTriple m n
            ]

-- list of all pythagorean triples with a given hypotenuse
pythHyp :: Integral a => a -> [(a, a, a)]
pythHyp hypotenuse = sort [ (k * a, k * b, k * c)
                          | k <- divisors hypotenuse
                          , (a, b, c) <- primPythHyp $ hypotenuse `quot` k
                          ]

-- list of all primitive pythagorean triples with a given hypotenuse
primPythHyp :: Integral a => a -> [(a, a, a)]
primPythHyp hypotenuse =
    sort [ (a, b, c)
         | n <- [1 .. floor $ sqrti hypotenuse]
         , let x = sqrti (hypotenuse - n * n)
         , isIntegral x
         , let m = floor x
         , areLegalParametersForPythTriple m n
         , let a = m * m - n * n
               b = 2 * m * n
               c = m * m + n * n
         ]

areLegalParametersForPythTriple :: Integral a => a -> a -> Bool
areLegalParametersForPythTriple m n =
    0 < n &&
    n < m &&
    gcd m n == 1 && -- m and n must be coprime
    even (m*n) -- exactly 1 of m and n is divisible by 2 (this test is sufficient since they are coprime)

-- list of all divisors of n (not just proper divisors)
divisors :: Integral a => a -> [a]
divisors n
    | n == 0    = []
    | n == 1    = [1]
    | n < 0     = divisors (-n)
    | otherwise = let divisorPairs = [nub [x, quot n x] | x <- [2 .. limit], n `mod` x == 0]
                      limit        = floor $ sqrti n
                  in sort . ([1, n] ++) $ concat divisorPairs

-- list of prime factors of n, with their multiplicities
factorize :: (Integral a, Num b) => a -> [(a, b)]
factorize n
    | n == 0    = []
    | n < 0     = (-1, 1) : factorize (-n)
    | otherwise = let findFactors :: Integral a => a -> [a] -> [a]
                      findFactors 1 acc = sort acc
                      findFactors k acc =
                          let d = head . tail $ divisors k
                          in findFactors (quot k d) (d : acc)
                  in collapseMultiplicities $ findFactors n []

-- collapse a list of elements to (elt, multiplicity) pairs
collapseMultiplicities :: (Ord a, Num b) => [a] -> [(a, b)]
collapseMultiplicities list = Map.toList (Map.fromListWith (+) [(x, 1)| x <- list])

-- Euler's phi
totient :: Integral a => a -> a
totient n
    | n <  0    = totient (-n)
    | n == 0    = 0
    | n == 1    = 1
    | otherwise = let primeList = primes n
                      offset = n ^ (genericLength primeList - (1 :: Integer))
                      diffList = map ((flip subtract n) . (quot n)) primeList
                    in (product diffList) `quot` offset

-- list of the unique prime factors of n
primes :: Integral a => a -> [a]
primes = (map fst) . (factorize :: Integral a => a -> [(a, Integer)])

-- get the prime factors of n that are congruent to k (mod m)
partitionPrimes :: Integral a => a -> a -> a -> (a, [a])
partitionPrimes n k modulus = (product primeList, primeList)
    where
    isPrimeCongruent = (== k) . (`mod` modulus)
    primeList        = filter isPrimeCongruent $ primes n

isPrime :: Integral a => a -> Bool
isPrime n = Set.member n . Set.fromList $ takeWhile (<= n) Primes.primes

areCoprime :: Integral a => a -> a -> Bool
areCoprime = ((1 ==) .) . gcd

-- evaluate polynomial (in Zm) with coefficients cs at x using Horner's
-- method
evalPoly :: forall a. Integral a => a -> a -> [a] -> a
evalPoly m x cs = evalPolyHelper . reverse $ (map (flip canon m)) cs
    where
    evalPolyHelper :: [a] -> a
    evalPolyHelper []       = 0
    evalPolyHelper [c]      = c `mod` m
    evalPolyHelper (c : ct) = let val = evalPolyHelper ct
                              in (val * x + c) `mod` m

-- find zeros to a given polynomial in Zm, where the coefficients are
-- given in order of descending degree
polyCong :: Integral a => a -> [a] -> [a]
polyCong m cs = filter (\x -> evalPoly m x cs == 0) [0 .. m - 1]

-- raise a to the power of e in Zm
exponentiate :: Integral a => a -> a -> a -> a
exponentiate a e m
    | e <= 0    = 1
    | otherwise =
        if e `mod` 2 == 0
        then let q = exponentiate a (quot e 2) m
            in canon (q * q) m
        else let q = exponentiate a (e - 1) m
            in canon (q * a) m

type Key a = (a, a)
-- given primes p and q, generate all pairs of public/private keys
rsaGenKeys :: Integral a => a -> a -> Either String [(Key a, Key a)]
rsaGenKeys p q
    | not (isPrime p && isPrime q) = Left "p and q must both be prime"
    | otherwise                    =
        Right [ ((e, n), (d, n))
              | let n = p * q
                    phi = totient n
              , e <- filter (areCoprime phi) [2 .. phi - 1]
              , d <- polyCong phi [e, -1]
              ]

-- use the key to encode/decode the message or ciphertext
rsaEval :: Integral a => Key a -> a -> Either String a
rsaEval (k, n) text = Right $ exponentiate text k n

-- compute the group of units of Zm
units :: Integral a => a -> [a]
units n = filter (\u -> areCoprime n u) [1 .. n - 1]

-- compute the nilpotent elements of Zm
nilpotents :: Integral a => a -> [a]
nilpotents m
    | r == 0    = []
    | otherwise = [ n
                  | n <- [0 .. m - 1]
                  , any (== 0) $ map (\e -> exponentiate n e m) [1 .. r]
                  ]
    where r = genericLength $ units m

-- compute the idempotent elements of Zm
idempotents :: Integral a => a -> [a]
idempotents = flip polyCong [1, (-1), 0]

-- compute the roots of Zm
roots :: Integral a => a -> [a]
roots m
    | null us   = []
    | otherwise = [ u | u <- us, order u m == (genericLength us)]
    where us = units m

-- an almost root is a unit, is not a primitive root, and produces the whole group of units
almostRoots :: forall a. Integral a => a -> [a]
almostRoots m = let unitCount = genericLength $ units m
                    expList = [1 .. unitCount + 1]
                    generateUnits :: a -> Set.Set a
                    generateUnits u = Set.fromList $ concat
                                        [ [k, canon (-k) m]
                                        | e <- expList
                                        , let k = exponentiate u e m
                                        ]
                in sort [ u
                        | u <- (units m) \\ (roots m)
                        , unitCount == (fromIntegral . Set.size $ generateUnits u)
                        ]

-- compute the order of x in Zm
order :: Integral a => a -> a -> a
order x m = head [ ord
                 | ord <- [1 .. genericLength $ units m]
                 , exponentiate (canon x m) ord m == 1
                 ]

-- computes the orders of all units in Zm
orders :: Integral a => a -> [a]
orders m = map (flip order m) $ units m

rootsOrAlmostRoots :: Integral a => a -> [a]
rootsOrAlmostRoots m =
    case roots m of
        [] -> almostRoots m
        rs -> rs

-- find powers of all the primitive roots of Zm that are equal to x.
-- Equivalently, express x as powers of roots (almost or primitive) in Zm.
expressAsRoots :: Integral a => a -> a -> [(a, a)]
expressAsRoots x m =
    let rs = rootsOrAlmostRoots m
    in  [ (r', e)
        | r <- rs
        , e <- [1 .. order r m]
        , let k = exponentiate r e m
        , r' <- (if k            == x then [r]  else [])
             ++ (if canon (-k) m == x then [-r] else [])]

-- solve a power congruence X^e = k (mod m)
powerCong :: Integral a => a -> a -> a -> [a]
powerCong e k m = [ x
                  | x <- [1 .. m]
                  , exponentiate x e m == canon k m
                  ]

--given 2 elements of Zm, find what powers of b produce k, if any.
ilogBM :: Integral a => a -> a -> a -> [a]
ilogBM b k m = let bc = canon b m
                   kc = canon k m
               in [ e
                  | e <- [1 .. order bc m]
                  , exponentiate bc e m == kc
                  ]

-- compute the Legendre symbol of p and q
legendre :: Integral a => a -> a -> Either String a
legendre q p
    | not $ isPrime p = Left "p is not prime"
    -- special case p = 2: not defined by Legendre, but makes it possible to call from kronecker.
    | p == 2 = let qc = canon q 8
                in if even qc
                    then Right 0
                    else if abs (4 - qc) == 1
                        then Right (-1)
                        else Right 1
    | otherwise = let r = exponentiate q (quot (p - 1) 2) p
                   in if r > 1
                        then Right (-1)
                        else Right r

-- compute kronecker symbol (q|m)
kronecker :: Integral a => a -> a -> Either String a
kronecker q m = fmap product $ sequence [ fmap (^ e) (legendre q p)
                                        | (p, e) <- (factorize :: Integral a => a -> [(a, Integer)]) m
                                        ]

-- compute the number of divisors of n
tau :: Integral a => a -> a
tau = genericLength . divisors

-- compute the sum of powers of divisors of n
sigma :: Integral a => a -> a -> a
sigma k = sum . map (^ k) . divisors

-- compute mobius of n: (-1)^littleOmega(n) if square-free, 0 otherwise
mobius :: (Integral a) => a -> a
mobius n
    | isSquareFree n = (-1) ^ (littleOmega n)
    | otherwise      = 0
    where
    isSquareFree :: Integral a => a -> Bool
    isSquareFree = and . map (not . even . snd) . (factorize :: Integral a => a -> [(a, Integer)])

-- number of unique prime factors
littleOmega :: Integral a => a -> a
littleOmega = genericLength . (factorize :: Integral a => a -> [(a, Integer)])

-- compute number of prime factors of n (including multiplicities)
bigOmega :: Integral a => a -> a
bigOmega = sum . (map snd) . factorize

---------------------------------------------------------------------------------
-- a Gaussian integer is a+bi, where a and b are both integers
infix 6 :+
data GaussInt a = a :+ a deriving (Ord, Eq)

instance (Show a, Ord a, Num a) => Show (GaussInt a) where
    show (a :+ b) = show a ++ op ++ b' ++ "i"
        where op = if b > 0 then "+" else "-"
              b' = if abs b > 1 then show (abs b) else ""

instance (Monoid a) => Monoid (GaussInt a) where
    mempty = (mempty :: a) :+ (mempty :: a)
    (c :+ d) `mappend` (e :+ f) = (c `mappend` e) :+ (d `mappend` f)

real :: GaussInt a -> a
real (x :+ _) = x

imag :: GaussInt a -> a
imag (_ :+ y) = y

-- conjugate of gaussian integer
conjugate :: Num a => GaussInt a -> GaussInt a
conjugate (r :+ i) = r :+ (-i)

-- magnitude squared of g
magnitude :: Num a => GaussInt a -> a
magnitude (x :+ y) = x * x + y * y

gPlus :: Num a => GaussInt a -> GaussInt a -> GaussInt a
gPlus (gr :+ gi) (hr :+ hi) = (gr + hr) :+ (gi + hi)

gMinus :: Num a => GaussInt a -> GaussInt a -> GaussInt a
gMinus (gr :+ gi) (hr :+ hi) = (gr - hr) :+ (gi - hi)

-- multiply g by h
gMultiply :: Num a => GaussInt a -> GaussInt a -> GaussInt a
gMultiply (gr :+ gi) (hr :+ hi) = (gr * hr - hi * gi) :+ (gr * hi + gi * hr)

-- "div" truncates toward -infinity, "quot" truncates toward 0, but we need
-- something that truncates toward the nearest integer. I.e., we want to
-- truncate with "round".
divToNearest :: (Integral a, Integral b) => a -> a -> b
divToNearest x y = round $ ((x % 1) / (y % 1))

-- divide g by h
gDivide :: Integral a => GaussInt a -> GaussInt a -> GaussInt a
gDivide g h =
    let nr :+ ni = g `gMultiply` (conjugate h)
        denom    = magnitude h
    in (divToNearest nr denom) :+ (divToNearest ni denom)

-- compute g mod m
gMod :: Integral a => GaussInt a -> GaussInt a -> GaussInt a
gMod g m =
    let q = g `gDivide` m
        p = m `gMultiply` q
    in g `gMinus` p

-- is g a prime?
gIsPrime :: Integral a => GaussInt a -> Bool
gIsPrime = isPrime . magnitude

gPrimes :: Integral a => [GaussInt a]
gPrimes = [(a' :+ b')
            | mag <- Primes.primes
            , let radius = floor $ sqrti mag
            , a <- [0 .. radius]
            , let y = sqrti $ mag - a*a
            , isIntegral y
            , let b = floor y
            , a' <- [-a, a]
            , b' <- [-b, b]
            ]

-- compute GCD of two Gaussian integers
gGCD :: Integral a => GaussInt a -> GaussInt a -> GaussInt a
gGCD g h
    | h == 0 :+ 0 = g --done recursing
    | otherwise = gGCD h (g `gMod` h)

-- find a Gaussian integer whose magnitude squared is a prime number
gFindPrime :: Integral a => a -> [GaussInt a]
gFindPrime 2 = [1 :+ 1]
gFindPrime p
    | p `mod` 4 == 1 && isPrime p =
        let r = head $ roots p
            z = exponentiate r (quot (p - 1) 4) p
        in [gGCD (p :+ 0) (z :+ 1)]
    | otherwise = []

-- exponentiate a gaussian integer
gExponentiate :: (Num a, Integral b) => GaussInt a -> b -> GaussInt a
gExponentiate a e
    | e <= 0         = 1 :+ 0
    | e `mod` 2 == 0 = let m = gExponentiate a (quot e 2)
                        in m `gMultiply` m
    | otherwise      = let m = gExponentiate a (e - 1)
                        in a `gMultiply` m

-- compute the prime factorization of g (unique up to units)
gFactorize :: forall a. Integral a => GaussInt a -> [(GaussInt a, a)]
gFactorize g
    | g == 0 :+ 0   = []
    | g == 1 :+ 0   = [(1 :+ 0, 1)]
    | otherwise     =
    let nonUnits       = concat . map processPrime . factorize $ magnitude g
        nonUnitProduct = foldr gMultiply (1 :+ 0) $ map (\(g', e) -> gExponentiate g' e) nonUnits
        remainderUnit  = case g `gDivide` nonUnitProduct of
                            1 :+ 0 -> []
                            g'     -> [(g', 1)]
    in remainderUnit ++ nonUnits
    where
    processPrime :: (a, a) -> [(GaussInt a, a)]
    processPrime (p, e)
        --deal with primes congruent to 3 (mod 4)
        | p `mod` 4 == 3 = [(p :+ 0, (quot e 2))]
        --deal with all other primes
        | otherwise      = collapseMultiplicities $ processGaussPrime g []
        where
        processGaussPrime :: GaussInt a -> [GaussInt a] -> [GaussInt a]
        processGaussPrime g' acc = do
            gp <- gFindPrime p -- find a GaussInt whose magnitude is p
            let fs = filter (\f -> g' `gMod` f == 0 :+ 0) [gp, conjugate gp] --find the list of even divisors
            case fs of
                [] -> acc                                                 -- Couldn't find a factor, so stop recursing
                f : _ -> processGaussPrime (g' `gDivide` f) ([f] ++ acc)    -- add this factor to the list, and keep looking

---------------------------------------------------------------------------------
--Combinatorics and other fun things
factorial :: Integral a => a -> a
factorial n = product [1 .. n]

fibonacci :: Num a => [a]
fibonacci = 0 : 1 : zipWith (+) fibonacci (tail fibonacci)

permute :: Integral a => a -> a -> a
permute n k = (factorial n) `quot` (factorial (n - k))

choose :: Integral a => a -> a -> a
choose n r = (n `permute` r) `quot` (factorial r)

-- given a list of spots, where each spot is a list of its possible values,
-- enumerate all possible assignments of values to spots
enumerate :: [[a]] -> [[a]]
enumerate []     = [[]]
enumerate (c:cs) = [ a : as
                   | a <- c
                   , as <- enumerate cs
                   ]

asSumOfSquares :: Integral a => a -> [(a, a)]
asSumOfSquares n = Set.toList . Set.fromList $
                     [ (x', y')
                     | x <- [1 .. floor $ sqrti n]
                     , let d = n - x * x
                     , d > 0
                     , let sd = sqrti d
                     , isIntegral sd
                     , let y = floor sd
                           [x', y'] = sort [x, y]
                     ]

---------------------------------------------------------------------------------
-- Continued fractions

data ContinuedFraction a = Finite [a] | Infinite ([a], [a])

instance (Show a) => Show (ContinuedFraction a) where
    show (Finite as) = "Finite " ++ (show as)
    show (Infinite (as, ps)) = "Infinite " ++ (show as) ++ (show ps) ++ "..."

continuedFractionFromDouble :: forall a. (Integral a) => Double -> a -> ContinuedFraction a
continuedFractionFromDouble x precision
    | precision < 1 = Finite []
    | otherwise     =
        let ts = getTs (fractionalPart x) precision
        in Finite $ (integralPart x) : (map (integralPart . recip) $ filter (/= 0) ts)
    where
    integralPart :: Double -> a
    integralPart n = fst $ (properFraction :: Double -> (a, Double)) n
    fractionalPart :: Double -> Double
    fractionalPart 0 = 0
    fractionalPart n = snd $ (properFraction :: Double -> (Integer, Double)) n
    getTs :: Integral a => Double -> a -> [Double]
    getTs y n = reverse $ tRunner [y] n
        where
        tRunner ts 0 = ts
        tRunner ts@(t : _) m
            | tn == 0   = ts
            | otherwise = tRunner (tn : ts) (m - 1)
            where tn = fractionalPart $ recip t

-- Usage: finds the continued fraction of (m0 + sqrt(d)) / q0
continuedFractionFromQuadratic :: forall a. (Integral a) => a -> a -> a -> ContinuedFraction a
continuedFractionFromQuadratic m0 d q0
    | q0 == 0                           = error "Cannot divide by 0"
    | isIntegral $ sqrti d              = continuedFractionFromRational ((m0 + (floor . sqrti $ d)) % q0)
    | not . isIntegral $ getNextQ m0 q0 = continuedFractionFromQuadratic (m0 * q0) (d * q0 * q0) (q0 * q0)
    | otherwise                         =
        let a0 = truncate $ ((fromIntegral m0) + (sqrti d)) / (fromIntegral q0)
        in helper [m0] [q0] [a0]
    where
    helper :: [a] -> [a] -> [a] -> ContinuedFraction a
    helper ms@(mp : _) qs@(qp : _) as@(ap : _) =
        let mn = ap * qp - mp
            qn = (truncate :: Double -> a) $ getNextQ mn qp
            an = truncate (((fromIntegral mn) + sqrti d) / (fromIntegral qn))
        in case findIndex (== (mn, qn, an)) (reverse $ zip3 ms qs as) of
            -- We've hit the first repetition of the period
            Just idx -> let as' = reverse as
                        in Infinite (take idx as', drop idx as')
            -- Haven't hit the end of the period yet, keep going as usual
            Nothing  -> helper (mn : ms) (qn : qs) (an : as)
    getNextQ :: a -> a -> Double
    getNextQ mp qp = (fromIntegral (d - mp * mp)) / (fromIntegral qp)

continuedFractionToRational :: (Integral a) => ContinuedFraction a -> Ratio a
continuedFractionToRational frac =
    let list = case frac of
            Finite as              -> as
            Infinite (as, periods) -> as ++ (take 35 $ cycle periods)
    in foldr (\ai rat -> (ai % 1) + (1 / rat)) ((last list) % 1) (init list)

continuedFractionFromRational :: Integral a => Ratio a -> ContinuedFraction a
continuedFractionFromRational rat
    | denominator rat == 1    = Finite [numerator rat]
    | numerator fracPart == 1 = Finite [intPart, denominator fracPart]
    | otherwise               =
        let Finite trail = continuedFractionFromRational (1 / fracPart)
        in Finite (intPart : trail)
    where
    intPart = (numerator rat) `div` (denominator rat)
    fracPart = rat - (intPart % 1)

continuedFractionToFractional :: (Fractional a) => ContinuedFraction Integer -> a
continuedFractionToFractional = fromRational . continuedFractionToRational

---------------------------------------------------------------------------------
-- Tests
-- execute a given test concisely
assert :: Bool -> String -> Either String ()
assert result errorString = if result then Right () else Left errorString

assertProperty :: [a] -> (a -> Bool) -> String -> Either String ()
assertProperty list p errorString = if all p list then Right () else Left errorString

samplePrimes :: [Integer]
samplePrimes = takeWhile (<= 100) Primes.primes
sampleComposites :: [Integer]
sampleComposites = filter (not . flip elem samplePrimes) [1 .. 100]
sampleMixed :: [Integer]
sampleMixed = [1..100]
sampleMixedGaussInts :: [GaussInt Integer]
sampleMixedGaussInts = delete (0 :+ 0) [a :+ b | a <- [-25 .. 25], b <- [-25 .. 25]]
sampleQuadratics :: [(Integer, Integer, Integer)]
sampleQuadratics = [ (m, d, q) | m <- [0 .. 20], d <- [0 .. 20], q <- [1 .. 20]]

pythTests :: [Either String ()]
pythTests =
    [ assert (pythSide (37 :: Int) == [(35, 12, 37),(37, 684, 685)])
            "pythSide failed"
    , assert (pythLeg (15 :: Int) == [(15, 8, 17),(15, 20, 25),(15, 36, 39),(15, 112, 113)])
            "pythLeg failed"
    , assert (pythHyp (25 :: Int) == [(7, 24, 25),(15, 20, 25)])
            "pythHyp failed"
    ] `using` parList rdeepseq

zModMTests :: [Either String ()]
zModMTests =
    [ assertProperty sampleMixed
            (\n -> let m = 37
                       n' = canon n m
                   in n' >= 0 && n' < m && n `mod` m == n')
            "canon failed: not within bounds, or not congruent"
    , assertProperty (map negate sampleMixed)
            (\n -> let m = 37
                       n' = canon n m
                   in n' >= 0 && n' < m && (n' - n) `mod` 37 == 0)
            "canon failed for negative integers"
    , assert (evalPoly 5 3 [4, 5, 6] == (2 :: Integer))
            "evalPoly failed"
    , assert (polyCong 5 [4, 5, 6] == ([1, 4] :: [Integer]))
            "polyCong failed"
    , assert (exponentiate 9 12 6 == (3 :: Integer))
            "exponentiate 9 12 6 failed"
    , assert (exponentiate (-9) 12 6 == (3 :: Integer))
            "exponentiate with negative failed"
    , assert (fromRight $ do
                    keyPairs <- rsaGenKeys 37 (41 :: Integer)
                    let results = map (\((_, n), (_, n')) -> n == n') keyPairs
                    return $ and results
                )
            "rsaGenKeys: n != n'"
    , assert (fromRight $ do
                    keyPairs <- rsaGenKeys 37 41
                    let results = map (\((pubk, n), (privk, _)) -> canon (privk * pubk) (totient n) == (1 :: Integer)) keyPairs
                    return $ and results
                )
            "rsaGenKeys: e*d != 1 (mod phi(n))"
    , assert (fromRight $ do
                    let text = (77 :: Integer)
                    keyPairs <- rsaGenKeys 19 23
                    ciphers <- sequence $ map (\(pub, _) -> rsaEval pub text) keyPairs
                    plains <- sequence $ zipWith (\(_, priv) cipher -> rsaEval priv cipher) keyPairs ciphers
                    let results = zipWith (==) plains $ repeat text
                    return $ and results
                )
            "rsaEval: public and private keys were not inverses!"
    , assertProperty sampleMixed
            (\n -> let us = units n
                   in and $ map (\u -> any (\u' -> canon (u * u') n == 1) us) us)
            "units: some unit not invertible!"
    , assertProperty sampleMixed
            (\n -> let ns = map fromIntegral $ nilpotents n
                       iteratedLists = map (\x -> take (fromIntegral n) $ iterate (\l -> canon (l * x) n) x) ns
                   in and $ map (\xs -> any (== 0) xs) iteratedLists)
            "nilpotents: not every element is nilpotent"
    , assertProperty sampleMixed
            (\n -> let is = idempotents n
                   in and $ map (\i -> canon (i * i) n == i) is)
            "idempotents: not every element is idempotent"
    , assert (roots (17 :: Integer) == [3, 5, 6, 7, 10, 11, 12, 14])
            "roots 17 failed"
    , assert (almostRoots (15 :: Integer) == [2, 7, 8, 13])
            "almostRoots 15 failed"
    , assert (orders (15 :: Integer) == [1, 4, 2, 4, 4, 2, 4, 2])
            "orders 15 failed"
    , assert (expressAsRoots (13 :: Integer) 15 == [(-2, 1), (7, 3), (-8, 3), (13, 1)])
            "expressAsRoots 13 15 failed"
    , assert (powerCong (11 :: Integer) 3 5 == [2])
            "powerCong 11 3 5 failed"
    ] `using` parList rdeepseq

zTests :: [Either String ()]
zTests =
    [ assertProperty sampleMixed
            (\n -> let divs = divisors n
                   in and $ map (\d -> n `mod` d == 0) divs)
            "divisors: not everything divides evenly"
    , assertProperty samplePrimes
            (\p -> divisors p == [1, p])
            "divisors: prime not equal to [1, p]"
    , assertProperty sampleMixed
            (\n -> let divs = divisors n
                   in and $ map (\d -> any (\d' -> d * d' == n) divs) divs)
            "divisors: not every divisor has a d' to multiply with to produce n"
    , assertProperty sampleMixed
            (\n -> let facs = (factorize :: Integral a => a -> [(a, Integer)]) n
                   in n == (product $ map (\(f, e) -> f ^ e) facs))
            "factorize: product of factors not equal to original"
    , assert (collapseMultiplicities ([1, 2, 3] :: [Integer]) == [((1 :: Integer), (1 :: Integer)), (2, 1), (3, 1)])
            "collapseMultiplicities failed on no-op"
    , assert (collapseMultiplicities [1, 2, 2, 3, 3, 3] == ([(1, 1), (2, 2), (3, 3)] :: [(Integer, Integer)]))
            "collapseMultiplicities failed"
    , assertProperty samplePrimes
            (\p -> primes p == [p])
            "primes: failed on prime"
    , assertProperty sampleComposites
            (\n -> and . map isPrime $ primes n)
            "primes: failed on composites"
    , assert (partitionPrimes (49 :: Integer)  3 5 == (1, []))
            "partitionPrimes with empty set failed"
    , assert (partitionPrimes (1155 :: Integer) 1 2 == (1155, [3, 5, 7, 11]))
            "partitionPrimes on whole set failed"
    , assert (partitionPrimes (1155 :: Integer) 3 4 == (231 , [3, 7, 11]))
            "partitionPrimes failed on 1155 3 4"
    , assertProperty samplePrimes
            isPrime
            "isPrime: failed on prime"
    , assertProperty sampleComposites
            (not . isPrime)
            "isPrime: failed on composite"
    , assertProperty ([5*x | x <- [1 .. 100]] :: [Integer])
            (not . (areCoprime 5))
            "areCoprime failed on multiples of 5"
    , assertProperty (delete 3 samplePrimes)
            (areCoprime 3)
            "areCoprime failed on primes"
    ] `using` parList rdeepseq

arithmeticFnsTests :: [Either String ()]
arithmeticFnsTests =
    [ assertProperty sampleMixed
            (\n -> totient n == (genericLength $ filter (areCoprime n) [1 .. n]))
            "totient: does not count number of coprimes <= n."
    , assert (legendre (3 :: Integer) 5 == Right (-1))
            "legendre 3 5 failed"
    , assert (legendre (3 :: Integer) 4 == Left
            "p is not prime") "legendre did not fail on non-prime input"
    , assert (kronecker (6 :: Integer) 5 == Right 1)
            "kronecker 6 5 failed"
    , assert (tau (60 :: Integer) == 12)
            "tau 60 failed"
    , assert (sigma 1 60 == (168 :: Integer))
            "sigma 1 60 failed"
    , assert (sigma 4 60 == (14013636 :: Integer))
            "sigma 4 60 failed"
    , assert (mobius 9 == (0 :: Integer))
            "mobius 9 failed (non-square free)"
    , assert (mobius 5 == (-1 :: Integer))
            "mobius 5 failed"
    , assert (littleOmega 60 == (3 :: Integer))
            "littleOmega 60 failed"
    , assert (bigOmega 60 == (4 :: Integer))
            "bigOmega 60 failed"
    ] `using` parList rdeepseq

gaussianIntTests :: [Either String ()]
gaussianIntTests =
    [ assertProperty (map (\n -> n :+ 0) ([1 .. 10] :: [Integer]))
            (\g -> g == conjugate g)
            "conjugate altered int with 0 imaginary component"
    , assertProperty sampleMixedGaussInts
            (\g@(a :+ b) -> a :+ (-b) == conjugate g)
            "conjugate failed on sample GaussInts"
    , assert (((5::Int) :+ 3) `gMultiply` (4 :+ 6) == 2 :+ 42)
            "gMultiply failed"
    , assert (((2::Int) :+ 42) `gDivide` (5 :+ 3) == 4 :+ 6)
            "gDivide failed on even division"
    , assert (((2::Int) :+ 43) `gDivide` (5 :+ 3) == 4 :+ 6)
            "gDivide failed for uneven division"
    , assert (((-2::Int) :+ (-43)) `gDivide` ((-5) :+ (-3)) == 4 :+ 6)
            "gDivide failed for negative divisor"
    , assert (((2::Int) :+ 43) `gMod` (5 :+ 3) == 0 :+ 1)
            "gMod failed on positive case"
    , assert (((-2::Int) :+ (-43)) `gMod` (5 :+ 3) == 0 :+ (-1))
            "gMod failed for negative case"
    , assert (magnitude ((5::Int) :+ 0) == 25)
            "magnitude failed on integer case"
    , assert (magnitude ((5::Int) :+ 3) == 34)
            "magnitude failed on 5 3"
    , assert (gIsPrime ((2::Int) :+ 5))
            "gIsPrime failed on prime"
    , assert (not $ gIsPrime ((3::Int) :+ 5))
            "gIsPrime failed on composite"
    , assertProperty (take 100 gPrimes::[GaussInt Integer])
            gIsPrime
            "gPrimes generated a composite!"
    , assert (gGCD ((2::Int) :+ 4) (12 :+ 24) == 2 :+ 4)
            "gGCD failed on even multiple"
    , assert (gGCD ((2::Int) :+ 4) (5 :+ 3) == 1 :+ 1)
            "gGCD failed on 2+4i and 5+3i"
    , assert (gGCD ((12::Int) :+ 23) (23 :+ 34) `elem` [x :+ y | x <- [(-1)..1], y <- [(-1)..1], (abs x) + (abs y) == 1])
            "gGCD failed in 12 23, 23 34" --division must round to *nearest* integer for this to work!
    , assert ((head $ gFindPrime (5::Int)) `elem` [ a :+ b | a <- [2, (-2)], b <- [1, (-1)]])
            "gFindPrime failed for 5"
    , assert (null $ gFindPrime (7::Int))
            "gFindPrime failed for 7"
    , assertProperty sampleMixed
            (\n -> let g = n :+ 0
                       powers = [1..5::Int]
                   in map (gExponentiate g) powers == map (\e -> (n ^ e) :+ 0) powers)
            "gExponentiate failed on \"real\" ints"
    , assert (gExponentiate (2 :+ 3) (4::Int) == (-119::Int) :+ (-120))
            "gExponentiate failed on 1st complex int"
    , assert (gExponentiate (2 :+ 3) (5::Int) == 122 :+ (-597::Int))
            "gExponentiate failed on 2nd complex int"
    , assertProperty sampleMixedGaussInts
            (\g -> let factors = gFactorize g
                       condensedFactors = map (\(x, e) -> gExponentiate x e) factors
                       prod = foldl gMultiply (1 :+ 0) condensedFactors
                   in prod == g)
            "gFactorize, gMultiply, gExponentiate did not recover original GaussInt"
    , assert (gFactorize ((1::Int) :+ 1) == [(1 :+ 1, 1)])
            "gFactorize failed on 1 1"
    ] `using` parList rdeepseq

continuedFractionTests :: [Either String ()]
continuedFractionTests =
    [ assertProperty sampleQuadratics
        (\(m, d, q) -> abs
            ((((fromIntegral m) + sqrti d) / (fromIntegral q)) -
            (fromRational . continuedFractionToRational $ continuedFractionFromQuadratic m d q))
            < 0.00000000000001)
        "fromRational . continuedFractionToRational . continuedFractionFromQuadratic isn't an identity!"

    ] `using` parList rdeepseq

tests :: Either String [()]
tests = sequence $ concat (
    [ pythTests
    , zTests
    , zModMTests
    , arithmeticFnsTests
    , gaussianIntTests
    , continuedFractionTests
    ] `using` parList rdeepseq)

main :: IO ()
main = do
    putStrLn $ case tests of
            Right list -> (show $ length list) ++ " tests passed"
            Left str' -> str'
    return ()
