{-# LANGUAGE ScopedTypeVariables #-}
module NumberTheory (
    -- pythagorean triples
    pythSide,
    pythLeg,
    pythHyp,
    primPythHyp,
    primPythLeg,
    -- Functions in Z mod m
    canon,
    evalPoly,
    polyCong,
    exponentiate,
    rsaGenKeys,
    rsaEval,
    units,
    nilpotents,
    idempotents,
    roots,
    almostRoots,
    order,
    orders,
    expressAsRoots,
    powerCong,
    ilogBM,
    -- functions in Z
    divisors,
    factorize,
    primes,
    isPrime,
    areCoprime,
    legendre,
    kronecker,
    -- arithmetic functions
    totient,
    tau,
    sigma,
    mobius,
    littleOmega,
    bigOmega,
    -- Gaussian Integer functions
    GaussInt((:+)),
    real,
    imag,
    conjugate,
    magnitude,
    gPlus,
    gMinus,
    gMultiply,
    gDivide,
    gMod,
    gIsPrime,
    gPrimes,
    gGCD,
    gFindPrime,
    gExponentiate,
    gFactorize,
    -- assorted combinatorics
    factorial,
    fibonacci,
    permute,
    choose,
    enumerate,
    asSumOfSquares,
    -- Continued fraction functions
    ContinuedFraction(Finite, Infinite),
    continuedFractionFromDouble,
    continuedFractionFromRational,
    continuedFractionFromQuadratic,
    continuedFractionToRational,
    continuedFractionToFractional
) where

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
