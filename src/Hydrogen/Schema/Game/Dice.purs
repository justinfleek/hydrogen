-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // schema // dice
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete dice vocabulary for games.
-- |
-- | Dice values are BOUNDED by die type. A D6 face is always 1-6.
-- | Probability is represented as exact rationals. Random number generation
-- | is NOT provided — that is a runtime concern.

module Hydrogen.Schema.Game.Dice
  ( DieType(D4, D6, D8, D10, D12, D20, D100)
  , allDieTypes, dieMax, dieName, dieShape
  , DieFace, dieFace, unwrapDieFace, allFaces
  , Die, die
  , DiceRoll, diceRoll
  , DiceNotation, diceNotation, parseDiceNotation, formatDiceNotation
  , RollResult, rollResult, rollTotal, isCriticalHit, isCriticalMiss
  , rollMin, rollMax, rollAverage
  , Probability, probability, simplifyProbability, probabilityToNumber
  , exactProbability, expectedValue
  , CrapsOutcome(CrapsNatural, CrapsCraps, CrapsPoint, CrapsPointMade, CrapsSeven)
  , crapsOutcome, isCrapsNatural, isCrapsCraps
  , isYahtzee, isFullHouse, isLargeStraight, isSmallStraight
  , isThreeOfAKind, isFourOfAKind
  ) where

import Prelude
  ( class Eq, class Ord, class Show, show, otherwise, map, mod, not, bind, negate
  , (==), (/=), (>), (>=), (<), (<=), (+), (-), (*), (/), (&&), (||), (<>)
  , compare, flip
  )
import Hydrogen.Schema.Bounded (inBoundsInt)
import Data.Array (length, filter, sortBy, zipWith, foldl, range, elem, all, index)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String.CodeUnits (toCharArray)
import Data.Int (fromString, toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // die // types
-- ═════════════════════════════════════════════════════════════════════════════

data DieType = D4 | D6 | D8 | D10 | D12 | D20 | D100

derive instance eqDieType :: Eq DieType
derive instance ordDieType :: Ord DieType

instance showDieType :: Show DieType where
  show D4 = "D4"
  show D6 = "D6"
  show D8 = "D8"
  show D10 = "D10"
  show D12 = "D12"
  show D20 = "D20"
  show D100 = "D100"

allDieTypes :: Array DieType
allDieTypes = [D4, D6, D8, D10, D12, D20, D100]

dieMax :: DieType -> Int
dieMax D4 = 4
dieMax D6 = 6
dieMax D8 = 8
dieMax D10 = 10
dieMax D12 = 12
dieMax D20 = 20
dieMax D100 = 100

dieName :: DieType -> String
dieName D4 = "four-sided die"
dieName D6 = "six-sided die"
dieName D8 = "eight-sided die"
dieName D10 = "ten-sided die"
dieName D12 = "twelve-sided die"
dieName D20 = "twenty-sided die"
dieName D100 = "percentile die"

dieShape :: DieType -> String
dieShape D4 = "tetrahedron"
dieShape D6 = "cube"
dieShape D8 = "octahedron"
dieShape D10 = "pentagonal trapezohedron"
dieShape D12 = "dodecahedron"
dieShape D20 = "icosahedron"
dieShape D100 = "percentile (two D10s)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // die // faces
-- ═════════════════════════════════════════════════════════════════════════════

newtype DieFace = DieFace Int

derive instance eqDieFace :: Eq DieFace
derive instance ordDieFace :: Ord DieFace

instance showDieFace :: Show DieFace where
  show (DieFace n) = "DieFace(" <> show n <> ")"

dieFace :: DieType -> Int -> Maybe DieFace
dieFace dt n
  | inBoundsInt 1 (dieMax dt) n = Just (DieFace n)
  | otherwise = Nothing

unwrapDieFace :: DieFace -> Int
unwrapDieFace (DieFace n) = n

allFaces :: DieType -> Array DieFace
allFaces dt = map DieFace (range 1 (dieMax dt))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // die // and // rolls
-- ═════════════════════════════════════════════════════════════════════════════

type Die = { dieType :: DieType, face :: DieFace }

die :: DieType -> Int -> Maybe Die
die dt faceVal = do
  f <- dieFace dt faceVal
  Just { dieType: dt, face: f }

type DiceRoll = Array Die

diceRoll :: DieType -> Array Int -> Maybe DiceRoll
diceRoll dt faces = traverseMaybe (die dt) faces

traverseMaybe :: forall a b. (a -> Maybe b) -> Array a -> Maybe (Array b)
traverseMaybe f arr = foldl go (Just []) arr
  where
    go Nothing _ = Nothing
    go (Just acc) a = case f a of
      Nothing -> Nothing
      Just b -> Just (acc <> [b])

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // dice // notation
-- ═════════════════════════════════════════════════════════════════════════════

type DiceNotation = { count :: Int, dieType :: DieType, modifier :: Int }

diceNotation :: Int -> DieType -> Int -> Maybe DiceNotation
diceNotation cnt dt m
  | cnt >= 1 = Just { count: cnt, dieType: dt, modifier: m }
  | otherwise = Nothing

formatDiceNotation :: DiceNotation -> String
formatDiceNotation dn =
  show dn.count <> "d" <> show (dieMax dn.dieType) <> fmtMod dn.modifier
  where
    fmtMod m | m > 0 = "+" <> show m | m < 0 = show m | otherwise = ""

parseDiceNotation :: String -> Maybe DiceNotation
parseDiceNotation s = do
  let chars = toCharArray s
  dPos <- findChar 'd' chars 0
  cnt <- if dPos == 0 then Just 1 else parseSlice chars 0 dPos
  let afterD = dPos + 1
  let modPos = findMod chars afterD
  dieSize <- case modPos of
    Nothing -> parseSlice chars afterD (length chars)
    Just mp -> parseSlice chars afterD mp
  dt <- parseDieType dieSize
  m <- case modPos of
    Nothing -> Just 0
    Just mp -> parseSlice chars mp (length chars)
  diceNotation cnt dt m

findChar :: Char -> Array Char -> Int -> Maybe Int
findChar c arr i
  | i >= length arr = Nothing
  | otherwise = case index arr i of
      Just ch -> if ch == c then Just i else findChar c arr (i + 1)
      Nothing -> Nothing

findMod :: Array Char -> Int -> Maybe Int
findMod arr i
  | i >= length arr = Nothing
  | otherwise = case index arr i of
      Just '+' -> Just i
      Just '-' -> Just i
      Just _ -> findMod arr (i + 1)
      Nothing -> Nothing

parseSlice :: Array Char -> Int -> Int -> Maybe Int
parseSlice arr start end = Int.fromString (sliceStr arr start end)

sliceStr :: Array Char -> Int -> Int -> String
sliceStr arr start end = foldl (<>) "" (map c2s (slice arr start end))

slice :: forall a. Array a -> Int -> Int -> Array a
slice arr start end = go start []
  where
    go i acc | i >= end = acc
             | otherwise = case index arr i of
                 Just x -> go (i + 1) (acc <> [x])
                 Nothing -> acc

c2s :: Char -> String
c2s '0' = "0"
c2s '1' = "1"
c2s '2' = "2"
c2s '3' = "3"
c2s '4' = "4"
c2s '5' = "5"
c2s '6' = "6"
c2s '7' = "7"
c2s '8' = "8"
c2s '9' = "9"
c2s '+' = "+"
c2s '-' = "-"
c2s _ = ""

parseDieType :: Int -> Maybe DieType
parseDieType 4 = Just D4
parseDieType 6 = Just D6
parseDieType 8 = Just D8
parseDieType 10 = Just D10
parseDieType 12 = Just D12
parseDieType 20 = Just D20
parseDieType 100 = Just D100
parseDieType _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // roll // results
-- ═════════════════════════════════════════════════════════════════════════════

type RollResult =
  { notation :: DiceNotation, faces :: Array DieFace, total :: Int
  , criticalHit :: Boolean, criticalMiss :: Boolean }

rollResult :: DiceNotation -> Array Int -> Maybe RollResult
rollResult dn faceVals
  | length faceVals /= dn.count = Nothing
  | otherwise = do
      faces <- traverseMaybe (dieFace dn.dieType) faceVals
      let faceSum = foldl (\acc (DieFace f) -> acc + f) 0 faces
      let maxVal = dieMax dn.dieType
      Just { notation: dn, faces: faces, total: faceSum + dn.modifier
           , criticalHit: all (\(DieFace f) -> f == maxVal) faces
           , criticalMiss: all (\(DieFace f) -> f == 1) faces }

rollTotal :: RollResult -> Int
rollTotal rr = rr.total

isCriticalHit :: RollResult -> Boolean
isCriticalHit rr = rr.criticalHit

isCriticalMiss :: RollResult -> Boolean
isCriticalMiss rr = rr.criticalMiss

rollMin :: DiceNotation -> Int
rollMin dn = dn.count + dn.modifier

rollMax :: DiceNotation -> Int
rollMax dn = dn.count * dieMax dn.dieType + dn.modifier

rollAverage :: DiceNotation -> Number
rollAverage dn =
  let max' = dieMax dn.dieType
      singleAvg = (1.0 + Int.toNumber max') / 2.0
  in Int.toNumber dn.count * singleAvg + Int.toNumber dn.modifier

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // probability
-- ═════════════════════════════════════════════════════════════════════════════

type Probability = { numerator :: Int, denominator :: Int }

probability :: Int -> Int -> Maybe Probability
probability num denom
  | denom <= 0 = Nothing
  | otherwise = Just (simplifyProbability { numerator: num, denominator: denom })

simplifyProbability :: Probability -> Probability
simplifyProbability p =
  let g = gcd (abs p.numerator) (abs p.denominator)
      sign = if p.denominator < 0 then -1 else 1
  in { numerator: sign * p.numerator / g, denominator: abs p.denominator / g }

probabilityToNumber :: Probability -> Number
probabilityToNumber p = Int.toNumber p.numerator / Int.toNumber p.denominator

exactProbability :: DiceNotation -> Int -> Probability
exactProbability dn target =
  let tgt = target - dn.modifier
      n = dn.count
      m = dieMax dn.dieType
  in if tgt < n || tgt > n * m
     then { numerator: 0, denominator: 1 }
     else simplifyProbability { numerator: countWays n m tgt, denominator: pow m n }

countWays :: Int -> Int -> Int -> Int
countWays n m target =
  let maxK = (target - n) / m
  in foldl (+) 0 (map (term n m target) (range 0 maxK))

term :: Int -> Int -> Int -> Int -> Int
term n m target k =
  let sign = if k `mod` 2 == 0 then 1 else -1
  in sign * binomial n k * binomial (target - m * k - 1) (n - 1)

expectedValue :: DiceNotation -> Number
expectedValue = rollAverage

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // craps
-- ═════════════════════════════════════════════════════════════════════════════

data CrapsOutcome
  = CrapsNatural | CrapsCraps | CrapsPoint Int | CrapsPointMade | CrapsSeven

derive instance eqCrapsOutcome :: Eq CrapsOutcome

instance showCrapsOutcome :: Show CrapsOutcome where
  show CrapsNatural = "CrapsNatural"
  show CrapsCraps = "CrapsCraps"
  show (CrapsPoint p) = "CrapsPoint(" <> show p <> ")"
  show CrapsPointMade = "CrapsPointMade"
  show CrapsSeven = "CrapsSeven"

crapsOutcome :: Maybe Int -> Int -> Int -> Maybe CrapsOutcome
crapsOutcome existingPoint d1 d2
  | d1 < 1 || d1 > 6 || d2 < 1 || d2 > 6 = Nothing
  | otherwise =
      let total = d1 + d2
      in case existingPoint of
        Nothing -> Just (comeOut total)
        Just pt -> Just (pointRoll pt total)

comeOut :: Int -> CrapsOutcome
comeOut t | t == 7 || t == 11 = CrapsNatural
          | t == 2 || t == 3 || t == 12 = CrapsCraps
          | otherwise = CrapsPoint t

pointRoll :: Int -> Int -> CrapsOutcome
pointRoll pt t | t == pt = CrapsPointMade | t == 7 = CrapsSeven | otherwise = CrapsPoint pt

isCrapsNatural :: Int -> Boolean
isCrapsNatural t = t == 7 || t == 11

isCrapsCraps :: Int -> Boolean
isCrapsCraps t = t == 2 || t == 3 || t == 12

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // yahtzee
-- ═════════════════════════════════════════════════════════════════════════════

isYahtzee :: Array DieFace -> Boolean
isYahtzee faces
  | length faces /= 5 = not true
  | otherwise = case index faces 0 of
      Nothing -> not true
      Just first -> all (\f -> f == first) faces

isFullHouse :: Array DieFace -> Boolean
isFullHouse faces
  | length faces /= 5 = not true
  | otherwise =
      let counts = countFaces faces
          sorted = sortBy (flip compare) counts
      in hasPattern sorted [3, 2]

isLargeStraight :: Array DieFace -> Boolean
isLargeStraight faces
  | length faces /= 5 = not true
  | otherwise =
      let sorted = sortBy compare (map unwrapDieFace faces)
      in sorted == [1, 2, 3, 4, 5] || sorted == [2, 3, 4, 5, 6]

isSmallStraight :: Array DieFace -> Boolean
isSmallStraight faces
  | length faces /= 5 = not true
  | otherwise =
      let vals = map unwrapDieFace faces
      in (has4 1 vals) || (has4 2 vals) || (has4 3 vals)
  where has4 start vs = elem start vs && elem (start+1) vs && elem (start+2) vs && elem (start+3) vs

isThreeOfAKind :: Array DieFace -> Boolean
isThreeOfAKind faces
  | length faces /= 5 = not true
  | otherwise = foldl (\a c -> a || c >= 3) (not true) (countFaces faces)

isFourOfAKind :: Array DieFace -> Boolean
isFourOfAKind faces
  | length faces /= 5 = not true
  | otherwise = foldl (\a c -> a || c >= 4) (not true) (countFaces faces)

countFaces :: Array DieFace -> Array Int
countFaces faces = map (\v -> length (filter (\(DieFace f) -> f == v) faces)) (range 1 6)

hasPattern :: Array Int -> Array Int -> Boolean
hasPattern counts pattern =
  let nz = filter (\c -> c > 0) counts
  in length nz == length pattern && foldl (&&) true (zipWith (==) nz pattern)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // math // util
-- ═════════════════════════════════════════════════════════════════════════════

gcd :: Int -> Int -> Int
gcd a 0 = a
gcd a b = gcd b (a `mod` b)

abs :: Int -> Int
abs n = if n < 0 then -n else n

pow :: Int -> Int -> Int
pow _ 0 = 1
pow base exp' = base * pow base (exp' - 1)

binomial :: Int -> Int -> Int
binomial n k
  | k < 0 || k > n = 0
  | k == 0 || k == n = 1
  | otherwise = binomial (n - 1) (k - 1) + binomial (n - 1) k
