{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
-- |A library for doing number-theoretic computations. This includes computations
-- in Z mod m (henceforth also written Zm), Z, Z x Zi (the Gaussian integers),
-- and some computations with continued fractions.
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
    nonUnitFactorize,
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
    (.+),
    (.-),
    (.*),
    (./),
    (.%),
    (.^),
    gIsPrime,
    gPrimes,
    gGCD,
    gFindPrime,
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
    finitePart,
    periodicPart,
    Quadratic(Quad),
    continuedFractionFromDouble,
    continuedFractionFromRational,
    continuedFractionFromQuadratic,
    continuedFractionToRational,
    continuedFractionToFloating,
    continuedFractionToQuadratic,
    reduceQuad,
    quadToFloating
) where

import           Data.Foldable                  (foldl')
import           Data.List                      ((\\), elemIndex, genericLength, nub, sort)
import qualified Data.Map             as Map    (fromListWith, toList)
import qualified Data.Numbers.Primes  as Primes (primes)
import           Data.Ratio                     ((%), denominator, numerator)
import qualified Data.Set             as Set    (fromList, Set, size, toList)
import qualified Math.NumberTheory.Primes.Factorisation as F (factorise)
import qualified Math.NumberTheory.Powers as Pow

-- |The canonical representation of x in Z mod m.
canon :: Integral a => a -> a -> a
canon x m
    | x < 0     = canon (x + m) m
    | otherwise = x `mod` m

-- square root of an integral value, for brevity elsewhere
sqrti :: Integral a => a -> Double
sqrti = (sqrt :: Double -> Double) . fromIntegral

isIntegral :: Double -> Bool
isIntegral x = (floor :: Double -> Integer) x == ceiling x

-- |List all pythagorean triples that include a given length (either as a leg
-- or hypotenuse).
pythSide :: Integral a => a -> [(a, a, a)]
pythSide s = sort $ pythLeg s ++ pythHyp s

-- |List all pythagorean triples that include a given leg length.
pythLeg :: Integral a => a -> [(a, a, a)]
pythLeg leg = sort [ (k * a, k * b, k * c)
                   | k <- divisors leg
                   , (a, b, c) <- primPythLeg $ leg `quot` k
                   ]

-- |List all primitive pythagorean triples that include a given leg length.
primPythLeg :: Integral a => a -> [(a, a, a)]
primPythLeg leg = -- (a, b, c) = (m^2-n^2, 2mn, m^2+n^2) for some integers m, n
    sort [ (a, b, c)
         | (m, n) <- findMN
         , let (a, b, c) = generatePythTriple m n
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

-- |List all pythagorean triples with a given hypotenuse.
pythHyp :: Integral a => a -> [(a, a, a)]
pythHyp hypotenuse = sort [ (k * a, k * b, k * c)
                          | k <- divisors hypotenuse
                          , (a, b, c) <- primPythHyp $ hypotenuse `quot` k
                          ]

-- |List all primitive pythagorean triples with a given hypotenuse.
primPythHyp :: Integral a => a -> [(a, a, a)]
primPythHyp hypotenuse =
    sort [ (a, b, c)
         | n <- [1 .. floor $ sqrti hypotenuse]
         , let x = sqrti (hypotenuse - n * n)
         , isIntegral x
         , let m = floor x
         , areLegalParametersForPythTriple m n
         , let (a, b, c) = generatePythTriple m n
         ]

generatePythTriple :: Integral a => a -> a -> (a, a, a)
generatePythTriple m n =
        let a = m * m - n * n
            b = 2 * m * n
            c = m * m + n * n
        in (a, b, c)

areLegalParametersForPythTriple :: Integral a => a -> a -> Bool
areLegalParametersForPythTriple m n =
    0 < n &&
    n < m &&
    gcd m n == 1 && -- m and n must be coprime
    even (m*n) -- exactly 1 of m and n is divisible by 2 (this test is sufficient since they are coprime)

-- |List all divisors of n (not just proper divisors).
divisors :: Integral a => a -> [a]
divisors n
    | n == 0    = []
    | n == 1    = [1]
    | n < 0     = divisors (-n)
    | otherwise = let divisorPairs = [nub [x, quot n x] | x <- [2 .. limit], n `mod` x == 0]
                      limit        = floor $ sqrti n
                  in sort . ([1, n] ++) $ concat divisorPairs

-- |List the prime factors of n, and their multiplicities.
factorize :: (Integral a) => a -> [(a, a)]
factorize n
    | n == 0    = []
    | n < 0     = (-1, 1) : nonUnitFactorize (-n)
    | otherwise = (1, 1) : nonUnitFactorize n

nonUnitFactorize :: (Integral a) => a -> [(a, a)]
nonUnitFactorize n
    | n == 0    = []
    | n < 0     = nonUnitFactorize (-n)
    | otherwise = let findFactors :: Integral a => a -> [a] -> [a]
                      findFactors 1 acc = sort acc
                      findFactors k acc =
                          let d = head . tail $ divisors k
                          in findFactors (quot k d) (d : acc)
                  in collapseMultiplicities $ findFactors n []

-- collapse a list of elements to (elt, multiplicity) pairs
collapseMultiplicities :: (Ord a, Num b) => [a] -> [(a, b)]
collapseMultiplicities list = Map.toList (Map.fromListWith (+) [(x, 1)| x <- list])

-- | Compute Euler's phi. This is equal to the number of integers <= n that are
-- relatively prime to n.
totient :: Integral a => a -> a
totient n
    | n <  0    = totient (-n)
    | n == 0    = 0
    | n == 1    = 1
    | otherwise = let primeList = primes n
                      offset = n ^ (genericLength primeList - (1 :: Integer))
                      diffList = map ((`subtract` n) . quot n) primeList
                    in product diffList `quot` offset

-- |List the unique prime factors of n.
primes :: Integral a => a -> [a]
primes = map fst . nonUnitFactorize


-- |Compute if n is prime.
isPrime :: Integral a => a -> Bool
isPrime n = n `elem` takeWhile (<= n) (dropWhile (< n) Primes.primes)

-- |Compute whether two integers are relatively prime to each other. That is, if
-- their GCD == 1.
areCoprime :: Integral a => a -> a -> Bool
areCoprime = ((1 ==) .) . gcd

-- |Evaluate a polynomial (in Zm) with given coefficients at a given point
-- using Horner's method.
evalPoly :: forall a. Integral a => a -> a -> [a] -> a
evalPoly m x cs = evalPolyHelper . reverse $ map (`canon` m) cs
    where
    evalPolyHelper :: [a] -> a
    evalPolyHelper []       = 0
    evalPolyHelper [c]      = c `mod` m
    evalPolyHelper (c : ct) = let val = evalPolyHelper ct
                              in (val * x + c) `mod` m

-- |Find the zeros to a given polynomial in Zm, where the coefficients are
-- given in order of descending degree.
polyCong :: Integral a => a -> [a] -> [a]
polyCong m cs = filter (\x -> evalPoly m x cs == 0) [0 .. m - 1]

-- |Raise a to the power of e in Zm.
exponentiate :: (Integral a) => a -> a -> a -> a
exponentiate a e m
    | e < 0 && a `elem` us = exponentiate a (canon (ul + e) m) m
    | e < 0                = error "a is not invertible in Z mod m"
    | e == 0               = 1
    | even e               = canon (s * s) m
    | otherwise            = canon (q * a) m
    where
    s = exponentiate a (quot e 2) m
    q = exponentiate a (e - 1) m
    us = units m
    ul = genericLength us

-- |A type to represent a public or private key.
type Key a = (a, a)
-- |Given primes p and q, generate all pairs of public/private keys derived
-- from those values.
rsaGenKeys :: Integral a => a -> a -> [(Key a, Key a)]
rsaGenKeys p q
    | not (isPrime p && isPrime q) = error "p and q must both be prime"
    | otherwise                    =
        [ ((e, n), (d, n))
        | let n = p * q
              phi = totient n
        , e <- filter (areCoprime phi) [2 .. phi - 1]
        , d <- polyCong phi [e, -1]
        ]

-- |Use the given key to encode/decode the message or ciphertext.
rsaEval :: (Integral a) => Key a -> a -> a
rsaEval (k, n) text = exponentiate text k n

-- |Compute the group of units of Zm.
units :: Integral a => a -> [a]
units n = filter (areCoprime n) [1 .. n - 1]

-- |Compute the nilpotent elements of Zm.
nilpotents :: (Integral a) => a -> [a]
nilpotents m
    | r == 0    = []
    | otherwise = [ n
                  | n <- [0 .. m - 1]
                  , let powers = map (\e -> exponentiate n e m) [1 .. r]
                  , 0 `elem` powers
                  ]
    where r = genericLength $ units m

-- |Compute the idempotent elements of Zm.
idempotents :: Integral a => a -> [a]
idempotents = flip polyCong [1, -1, 0]

-- |Compute the primitive roots of Zm.
roots :: (Integral a) => a -> [a]
roots m
    | null us   = []
    | otherwise = [ u | u <- us, order u m == genericLength us]
    where us = units m

-- |Compute the "almost roots" of Zm. An almost root is a unit, is not a
-- primitive root, and generates the whole group of units when exponentiated.
almostRoots :: forall a. (Integral a) => a -> [a]
almostRoots m = let unitCount = genericLength $ units m
                    expList = [1 .. unitCount + 1]
                    generateUnits :: a -> Set.Set a
                    generateUnits u = Set.fromList $ concat
                                        [ [k, canon (-k) m]
                                        | e <- expList
                                        , let k = exponentiate u e m
                                        ]
                in sort [ u
                        | u <- units m \\ roots m
                        , unitCount == (fromIntegral . Set.size $ generateUnits u)
                        ]

-- |Compute the order of x in Zm.
order :: (Integral a) => a -> a -> a
order x m = head [ ord
                 | ord <- [1 .. genericLength $ units m]
                 , exponentiate (canon x m) ord m == 1
                 ]

-- |Computes the orders of all units in Zm.
orders :: (Integral a) => a -> [a]
orders m = map (`order` m) $ units m

rootsOrAlmostRoots :: (Integral a) => a -> [a]
rootsOrAlmostRoots m =
    case roots m of
        [] -> almostRoots m
        rs -> rs

-- |Find powers of all the primitive roots of Zm that are equal to x.
-- Equivalently, express x as powers of roots (almost or primitive) in Zm.
expressAsRoots :: (Integral a) => a -> a -> [(a, a)]
expressAsRoots x m =
    let rs = rootsOrAlmostRoots m
    in  [ (r', e)
        | r <- rs
        , e <- [1 .. order r m]
        , let k = exponentiate r e m
        , r' <- [ r | k == x ]
             ++ [ -r | canon (-k) m == x ]
        ]

-- |Solve the power congruence for x, given e, k, m: x^e = k (mod m)
powerCong :: (Integral a) => a -> a -> a -> [a]
powerCong e k m = [ x
                  | x <- [1 .. m]
                  , exponentiate x e m == canon k m
                  ]

-- |Compute the integer log base B of k in Zm.
-- Equivalently, given 2 elements of Zm, find what powers of b produce k, if any.
ilogBM :: (Integral a) => a -> a -> a -> [a]
ilogBM b k m = let bc = canon b m
                   kc = canon k m
               in [ e
                  | e <- [1 .. order bc m]
                  , exponentiate bc e m == kc
                  ]

-- |Compute the Legendre symbol of p and q.
legendre :: (Integral a) => a -> a -> a
legendre q p
    | not $ isPrime p = error "p is not prime"
    | p == 2          = error "p must be odd"
    | otherwise = let r = exponentiate q (quot (p - 1) 2) p
                   in if r > 1 then (-1) else r

-- |Compute the Kronecker symbol (a|n).
kronecker :: (Integral a) => a -> a -> a
kronecker a n
    | n == (-1) && a < 0             = -1
    | n == (-1)                      = 1
    | n == 0 && abs a == 1           = 1
    | n == 0                         = 0
    | n == 1                         = 1
    | n == 2 && even a               = 0
    | n == 2 && abs (a `mod` 8) == 1 = 1
    | n == 2                         = -1
    | isPrime n                      = legendre a n
    | otherwise                      = kronecker a u * product [ kronecker a p ^ e | (p, e) <- nonUnitFactorize n]
    where u = if a < 0 then -1 else 1


-- |Compute tau(n), the number of divisors of n.
tau :: Integral a => a -> a
tau = genericLength . divisors

-- |Compute sigma(n), the sum of powers of divisors of n.
sigma :: Integral a => a -> a -> a
sigma k = sum . map (^ k) . divisors

-- |Compute mobius(n): (-1)^littleOmega(n) if n is square-free, 0 otherwise.
mobius :: (Integral a) => a -> a
mobius n
    | isSquareFree n = (-1) ^ littleOmega n
    | otherwise      = 0
    where
    isSquareFree :: Integral a => a -> Bool
    isSquareFree = all (odd . snd) . nonUnitFactorize

-- |Compute littleOmega(n), the number of unique prime factors.
littleOmega :: Integral a => a -> a
littleOmega = genericLength . nonUnitFactorize

-- |Compute bigOmega(n), the number of prime factors of n (including multiplicities).
bigOmega :: Integral a => a -> a
bigOmega = sum . map snd . nonUnitFactorize

---------------------------------------------------------------------------------
infix 6 :+
infixr 8 .^
infixl 7 .+, .-, .*, ./
-- |A Gaussian integer is a+bi, where a and b are both integers.
data GaussInt = Integer :+ Integer deriving (Ord, Eq)

instance Show GaussInt where
    show (a :+ b) = show a ++ op ++ b' ++ "i"
        where op = if b > 0 then "+" else "-"
              b' = if abs b /= 1 then show (abs b) else ""

-- |The real part of a Gaussian integer.
real :: GaussInt -> Integer
real (x :+ _) = x

-- |The imaginary part of a Gaussian integer.
imag :: GaussInt -> Integer
imag (_ :+ y) = y

-- |Conjugate a Gaussian integer.
conjugate :: GaussInt -> GaussInt
conjugate (r :+ i) = r :+ (-i)

-- |The square of the magnitude of a Gaussian integer.
magnitude :: GaussInt -> Integer
magnitude (x :+ y) = x * x + y * y

-- |Add two Gaussian integers together.
(.+) :: GaussInt -> GaussInt -> GaussInt
(gr :+ gi) .+ (hr :+ hi) = (gr + hr) :+ (gi + hi)

-- |Subtract one Gaussian integer from another.
(.-) :: GaussInt -> GaussInt -> GaussInt
(gr :+ gi) .- (hr :+ hi) = (gr - hr) :+ (gi - hi)

-- |Multiply two Gaussian integers.
(.*) :: GaussInt -> GaussInt -> GaussInt
(gr :+ gi) .* (hr :+ hi) = (gr * hr - hi * gi) :+ (gr * hi + gi * hr)

-- "div" truncates toward -infinity, "quot" truncates toward 0, but we need
-- something that truncates toward the nearest integer. I.e., we want to
-- truncate with "round".
divToNearest :: (Integral a, Integral b) => a -> a -> b
divToNearest x y = round ((x % 1) / (y % 1))

-- |Divide one Gaussian integer by another.
(./) :: GaussInt -> GaussInt -> GaussInt
g ./ h =
    let nr :+ ni = g .* conjugate h
        denom    = magnitude h
    in divToNearest nr denom :+ divToNearest ni denom

-- |Compute the remainder when dividing one Gaussian integer by another.
(.%) :: GaussInt -> GaussInt -> GaussInt
g .% m =
    let q = g ./ m
        p = m .* q
    in g .- p

-- |Compute whether a given Gaussian integer is prime.
gIsPrime :: GaussInt -> Bool
gIsPrime = isPrime . magnitude

-- |An infinte list of the Gaussian primes. This list is in order of ascending magnitude.
gPrimes :: [GaussInt]
gPrimes = [ a' :+ b'
            | mag <- Primes.primes
            , let radius = floor $ sqrti mag
            , a <- [0 .. radius]
            , let y = sqrti $ mag - a*a
            , isIntegral y
            , let b = floor y
            , a' <- [-a, a]
            , b' <- [-b, b]
            ]

-- |Compute the GCD of two Gaussian integers.
gGCD :: GaussInt -> GaussInt -> GaussInt
gGCD g h
    | h == 0 :+ 0 = g --done recursing
    | otherwise = gGCD h (g .% h)

-- |Find a Gaussian integer whose magnitude squared is the given prime number.
gFindPrime :: Integer -> GaussInt
gFindPrime p
    | p == 2 = 1 :+ 1
    | p `mod` 4 == 1 && isPrime p =
        let r = head $ roots p
            z = exponentiate r (quot (p - 1) 4) p
        in gGCD (p :+ 0) (z :+ 1)
    | otherwise = error "p must be prime, and congruent to 3 (mod 4)"

-- |Raise a Gaussian integer to a given power.
(.^) :: (Integral a) => GaussInt -> a -> GaussInt
a .^ e
    | e < 0     = error "Cannot exponentiate Gaussian Int to negative power"
    | e == 0    = 1 :+ 0
    | even e    = s .* s
    | otherwise = a .* a .^ (e - 1)
    where
    s = a .^ div e 2

-- |Compute the prime factorization of a Gaussian integer. This is unique up to units (+/- 1, +/- i).
gFactorize :: GaussInt -> [(GaussInt, Int)]
gFactorize g
    | g == 0 :+ 0  = [(g, 1)] -- 0 has no prime factors.
    | otherwise =
        let helper :: [(Integer, Int)] -> GaussInt -> [(GaussInt, Int)] -> [(GaussInt, Int)]
            helper [] g' fs = (g', 1) : fs    -- include the unit.
            helper ((!p, !e) : pt) g' fs
                | p `mod` 4 == 3 =
                    -- prime factors congruent to 3 mod 4 are simple.
                    let pow = div e 2
                        gp = p :+ 0
                    in helper pt (g' ./ gp .^ pow) ((gp, pow) : fs)
                | otherwise      =
                    -- general case: for every prime factor of the magnitude
                    -- squared, find a gaussian prime whose magnitude squared
                    -- is that prime. Then find out how many times the original
                    -- number is divisible by that gaussian prime and its
                    -- conjugate. The order that the prime factors are
                    -- processed doesn't really matter, but it is reversed so
                    -- that the Guassian primes will be in order of increasing
                    -- magnitude.
                    let gp = gFindPrime p
                        (!gNext, !facs) = trialDivide g' [gp, conjugate gp] []
                    in helper pt gNext (facs ++ fs)
        in helper (reverse . F.factorise $ magnitude g) g []

-- Divide a Gaussian integer by a set of (relatively prime) Gaussian integers,
-- as many times as possible, and return the final quotient as well as a count
-- of how many times each factor divided the original.
trialDivide :: GaussInt -> [GaussInt] -> [(GaussInt, Int)] -> (GaussInt, [(GaussInt, Int)])
trialDivide g [] fs = (g, fs)
trialDivide g (pf : pft) fs
    | g .% pf == 0 :+ 0 =
        let (cnt, g') = countEvenDivisions g pf
        in trialDivide g' pft ((pf, cnt) : fs)
    | otherwise       = trialDivide g pft fs

-- Divide a Gaussian integer by a possible factor, and return how many times
-- the factor divided it evenly, as well as the result of dividing the original
-- that many times.
countEvenDivisions :: GaussInt -> GaussInt -> (Int, GaussInt)
countEvenDivisions g pf = helper g 0
    where
    helper :: GaussInt -> Int -> (Int, GaussInt)
    helper g' acc
        | g' .% pf == 0:+ 0 = helper (g' ./ pf) (1 + acc)
        | otherwise         = (acc, g')

---------------------------------------------------------------------------------
--Combinatorics and other fun things

-- |Compute the factorial of a given integer.
factorial :: Integral a => a -> a
factorial n = product [1 .. n]

-- |The Fibonacci sequence.
fibonacci :: Num a => [a]
fibonacci = 0 : 1 : zipWith (+) fibonacci (tail fibonacci)

-- |Given a set of n elements, compute the number of ways to arrange k elements of it.
permute :: Integral a => a -> a -> a
permute n k = factorial n `quot` factorial (n - k)

-- |Given a set of n elements, compute the number of ways to choose r elements of it.
choose :: Integral a => a -> a -> a
choose n r = (n `permute` r) `quot` factorial r

-- |Given a list of spots, where each spot is a list of its possible values,
-- enumerate all possible assignments of values to spots.
enumerate :: [[a]] -> [[a]]
enumerate []     = [[]]
enumerate (c:cs) = [ a : as
                   | a <- c
                   , as <- enumerate cs
                   ]

-- |Given an integer n, find all ways of expressing n as the sum of two squares.
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

-- |A (simple) continued fraction can be represented as a list of coefficients.
-- This list is either finite (in the case of rational numbers), or infinite (in
-- the case of irrational numbers. If the fraction represents a quadratic number
-- (that is, a number that can be the root of some quadratic polynomial), then
-- the infinite list of coefficients consists of a finite sequence of coefficients
-- followed by a (finite) sequence of coefficients that repeats indefinitely.
-- NOTE: for performance reasons, each sequence is stored in reverse order.
data ContinuedFraction = Zero | Finite Sign [Integer] | Infinite Sign [Integer] [Integer]

data Sign = Negative | Positive

finitePart :: ContinuedFraction -> [Integer]
finitePart Zero = []
finitePart (Finite _ as) = reverse as
finitePart (Infinite _ fs _) = reverse fs

periodicPart :: ContinuedFraction -> [Integer]
periodicPart Zero = []
periodicPart (Finite _ _) = []
periodicPart (Infinite _ _ ps) = reverse ps

instance Show ContinuedFraction where
    show Zero = "0"
    show (Finite s as) = "Finite " ++ show s ++ show (reverse as)
    show (Infinite s as ps) = "Infinite " ++ show s ++ show (reverse as) ++ show (reverse ps) ++ "..."

instance Show Sign where
    show Positive = "+"
    show Negative = "-"

-- |Quadratic number datatype. (m, c, d, q) represents (m + c*sqrt(d))/q.
data Quadratic = Quad (Integer, Integer, Integer, Integer) deriving (Eq)

instance Show Quadratic where
    show (Quad (m, c, d, q)) = "(" ++ show m ++ " + " ++ show c ++ "*sqrt(" ++ show d ++ ")) / " ++ show q

negateCF :: ContinuedFraction -> ContinuedFraction
negateCF Zero = Zero
negateCF (Finite Positive as) = Finite Negative as
negateCF (Infinite Positive as ps) = Infinite Negative as ps
negateCF (Finite Negative as) = Finite Positive as
negateCF (Infinite Negative as ps) = Infinite Positive as ps

-- |Convert a Double to a (finite) continued fraction. This is inherently lossy.
continuedFractionFromDouble :: forall a. (Integral a) => Double -> a -> ContinuedFraction
continuedFractionFromDouble x precision
    | precision < 1 = Finite Positive []
    | otherwise     =
        let ts = getTs (fractionalPart x) precision
        in Finite Positive $ reverse $ integralPart x : map (integralPart . recip) (filter (/= 0) ts)
    where
    integralPart :: Double -> Integer
    integralPart n = fst $ properFraction n
    fractionalPart :: Double -> Double
    fractionalPart 0 = 0
    fractionalPart n = snd $ (properFraction :: Double -> (Integer, Double)) n
    getTs :: Integral a => Double -> a -> [Double]
    getTs y n = reverse $ tRunner [y] n
        where
        tRunner [] _ = error "improper call of tRunner. This should never happen."
        tRunner ts 0 = ts
        tRunner ts@(t : _) m
            | tn == 0   = ts
            | otherwise = tRunner (tn : ts) (m - 1)
            where tn = fractionalPart $ recip t

-- |Convert a quadratic number to its continued fraction representation.
continuedFractionFromQuadratic :: Quadratic -> ContinuedFraction
continuedFractionFromQuadratic quad
    | q == 0                    = error "Cannot divide by 0"
    | m == 0 && c == 0          = Zero
    | m < 0 && c < 0            = negateCF . continuedFractionFromQuadratic $ negateQuad quad
    | signum m * signum c == -1
    && (if c < 0 then (<) else (>)) (m * m - c * c * d) 0
                                = negateCF . continuedFractionFromQuadratic $ negateQuad quad
    | signum m * signum c == -1 = error "mismatched signs, unimplemented"
    | c == 0                    = continuedFractionFromRational (m % q)
    | Pow.isSquare d            = continuedFractionFromRational ((m + Pow.integerSquareRoot d) % q)
    | otherwise                 = let a = truncate $ (fromIntegral m + sqrti d) / fromIntegral q
                                  in helper [(m, q, a)]
    where
    Quad (m, c, d, q) = fixCoefficients . condense $ reduceQuad quad

    helper :: [(Integer, Integer, Integer)] -> ContinuedFraction
    helper [] = error "improper call to helper function. This will never happen."
    helper ts@((!mp, !qp, !ap) : _) =
        let mn = ap * qp - mp
            qn = truncate $ getNextQ mn qp d
            an = truncate ((fromIntegral mn + sqrti d) / fromIntegral qn)
            as = map third ts
        in case elemIndex (mn, qn, an) ts of
            -- We've hit the first repetition of the period
            Just idx -> Infinite Positive (drop (idx + 1) as) (take (idx + 1) as)
            -- Haven't hit the end of the period yet, keep going as usual
            Nothing  -> helper $ (mn, qn, an) : ts

getNextQ :: Integer -> Integer -> Integer -> Double
getNextQ mp qp d = fromIntegral (d - mp * mp) / fromIntegral qp

condense :: Quadratic -> Quadratic
condense (Quad (m, c, d, q)) = Quad (m, signum c, d * c * c, q)

fixCoefficients :: Quadratic -> Quadratic
fixCoefficients quad@(Quad (m, c, d, q))
    | not . isIntegral $ getNextQ m q d = Quad (m * q, c, d * q * q, q * q)
    | otherwise = quad

third :: (a, b, c) -> c
third (_, _, !x) = x

-- |Convert a continued fraction to a rational number. If the fraction is finite,
-- then this is an exact conversion. If the fraction is infinite, this conversion
-- is necessarily lossy, since the fraction does not represent a rational number.
continuedFractionToRational :: ContinuedFraction -> Rational
continuedFractionToRational f = case f of
    Zero                    -> 0
    Finite Negative _       -> negate . continuedFractionToRational $ negateCF f
    Infinite Negative _ _   -> negate . continuedFractionToRational $ negateCF f
    Finite Positive as      -> folder as
    Infinite Positive as ps -> folder ((reverse . take 35 $ cycle (reverse ps)) ++ as)
    where
    collapse :: Rational -> Integer -> Rational
    collapse !rat !ai = (ai % 1) + (1 / rat)
    folder :: [Integer] -> Rational
    folder ks = foldl' collapse (head ks % 1) (tail ks)

-- |Convert a rational number to a continued fraction. This is an exact conversion.
continuedFractionFromRational :: Rational -> ContinuedFraction
continuedFractionFromRational 0 = Zero
continuedFractionFromRational rat
    | rat < 0                 = negateCF $ continuedFractionFromRational (-rat)
    | denominator rat == 1    = Finite Positive [numerator rat]
    | numerator fracPart == 1 = Finite Positive $ reverse [intPart, denominator fracPart]
    | otherwise               =
        let Finite Positive trail = continuedFractionFromRational (1 / fracPart)
        in Finite Positive (trail ++ [intPart])
    where
    intPart = numerator rat `div` denominator rat
    fracPart = rat - (intPart % 1)

-- |Convert a continued fraction to a Floating type. This is lossy due to
-- precision in the Floating type.
continuedFractionToFloating :: (Floating b) => ContinuedFraction -> b
continuedFractionToFloating = quadToFloating . continuedFractionToQuadratic

-- |Binomial type. (a, b) represents a*x + b.
type Binomial a = (a, a)

reduceBinomials :: (Integral a) => Binomial a -> Binomial a -> (Binomial a, Binomial a)
reduceBinomials (fn, fd) (sn, sd) =
    let g = gcd fn $ gcd fd $ gcd sn sd
    in ((div fn g, div fd g), (div sn g, div sd g))

-- |Convert a continued fraction to a quadratic number.
continuedFractionToQuadratic :: ContinuedFraction -> Quadratic
continuedFractionToQuadratic f = case f of
    Zero                    -> Quad (0, 0, 0, 1)
    Finite Negative _       -> negateQuad . continuedFractionToQuadratic $ negateCF f
    Infinite Negative _ _   -> negateQuad . continuedFractionToQuadratic $ negateCF f
    Finite Positive _       -> let rat = continuedFractionToRational f
                               in reduceQuad $ Quad (numerator rat, 0, 0, denominator rat)
    Infinite Positive fs ps -> if null fs
        then let collapsePeriodicLevel :: (Integral a) => (Binomial a, Binomial a) -> a -> (Binomial a, Binomial a)
                 collapsePeriodicLevel (num@(!nx, !nu), (!dx, !du)) !p = ((p * nx + dx, p * nu + du), num)
                 ((a, b), (j, k)) = uncurry reduceBinomials $ foldl' collapsePeriodicLevel ((head ps, 1), (1, 0)) (tail ps)
                 d = a * a - 2 * a * k + 4 * b * j + k * k
                 c = 1
                 m = a - k
                 q = 2 * j
             in reduceQuad $ Quad (m, c, d, q)
        else let (Quad (m, c, d, q)) = continuedFractionToQuadratic $ Infinite Positive [] ps
                 collapseFiniteLevel :: Quadratic -> Integer -> Quadratic
                 collapseFiniteLevel (Quad (!m', !c', !d', !q')) !a = Quad (a * m' * m' + q' * m' - a * c' * c' * d', (-q') * c', d', m' * m' - c' * c' * d')
                 quad = foldl' collapseFiniteLevel (Quad (m, c, d, q)) fs
             in reduceQuad quad

negateQuad :: Quadratic -> Quadratic
negateQuad (Quad (m, c, d, q)) = Quad (-m, -c, d, q)

reduceQuad :: Quadratic -> Quadratic
reduceQuad (Quad (m, c, d, q))
    | d == 0  || c == 0 =
        --normal rational, easy case
        let common = gcd m q
            [m', q'] = map (`div` common) [m, q]
            [mf, qf] = map (if q' < 0 then negate else id) [m', q']
        in Quad (mf, 0, 0, qf)
    | d' == 1 =
        --normal rational, disguised as quadratic
        let m' = m + c'
            common = gcd m' q
            [m'', q''] = map (`div` common) [m', q]
            [mf, qf] = map (if q'' < 0 then negate else id) [m'', q'']
        in Quad (mf, 0, 0, qf)
    | otherwise =
        --general case
        let common = gcd m $ gcd c' q
            [mi, ci, qi] = map (`div` common) [m, c', q]
            [mf, cf, qf] = map (if qi < 0 then negate else id) [mi, ci, qi]
        in Quad (mf, cf, d', qf)
    where
    cd = product . map (\(!p, !e) -> p ^ div e 2) $ F.factorise d
    c' = cd * c
    d' = div d $ cd * cd

-- |Convert a quadratic number to a Floating approximation.
quadToFloating :: (Floating a) => Quadratic -> a
quadToFloating (Quad (m, c, d, q)) = (fromIntegral m + fromIntegral c * sqrt (fromIntegral d)) / fromIntegral q
