-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // schema // game // betting
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Complete betting vocabulary for casino games.
-- | All monetary amounts in cents. Supports American, Decimal, Fractional odds.

module Hydrogen.Schema.Game.Betting
  ( Cents(Cents), cents, centsFromDollars, centsToNumber, formatCents, parseCents
  , addCents, subtractCents, multiplyCents, zeroCents
  , Odds(AmericanOdds, DecimalOdds, FractionalOdds)
  , americanOdds, decimalOdds, fractionalOdds
  , toDecimalOdds, toAmericanOdds, toFractionalOdds, impliedProbability
  , BetType(..), Wager, wager, wagerAmount, wagerType
  , BetResult(Win, Loss, Push, PartialWin)
  , Bankroll, bankroll, updateBankroll, bankrollBalance, sessionProfit, canAffordBet
  , calculatePayout, rouletteOdds, roulettePayout, crapsOdds, crapsPayout
  , houseEdge, trueOdds, kellyBet, kellyFractional
  , centsBounds, wagerBounds
  ) where

import Prelude
  ( class Eq, class Ord, class Show, show, otherwise, negate, mod, div
  , (+), (-), (*), (/), (<), (>), (>=), (==), (/=), (&&), (||), (<>), ($) )
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber, floor) as Int
import Data.String (length) as String
import Data.String.CodeUnits (toCharArray) as StringCU
import Data.Array (index) as Array
import Data.Foldable (foldl)
import Hydrogen.Schema.Bounded (IntBounds, intBounds, clampInt, BoundsBehavior(Clamps))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // monetary
-- ═══════════════════════════════════════════════════════════════════════════════
newtype Cents = Cents Int
derive instance eqCents :: Eq Cents
derive instance ordCents :: Ord Cents
instance showCents :: Show Cents where show (Cents c) = "(Cents " <> show c <> ")"

cents :: Int -> Cents
cents n = Cents (clampInt 0 2000000000 n)

centsFromDollars :: Int -> Cents
centsFromDollars d = cents (d * 100)

centsToNumber :: Cents -> Number
centsToNumber (Cents c) = Int.toNumber c

addCents :: Cents -> Cents -> Cents
addCents (Cents a) (Cents b) = cents (a + b)

subtractCents :: Cents -> Cents -> Cents
subtractCents (Cents a) (Cents b) = cents (a - b)

multiplyCents :: Int -> Cents -> Cents
multiplyCents f (Cents c) = cents (f * c)

zeroCents :: Cents
zeroCents = Cents 0

-- | Absolute value for Int
absInt :: Int -> Int
absInt n = if n < 0 then negate n else n

formatCents :: Cents -> String
formatCents (Cents c) =
  let neg = c < 0
      absC = absInt c
      d = absC `div` 100
      cp = absC `mod` 100
      cs = if cp < 10 then "0" <> show cp else show cp
  in (if neg then "-" else "") <> "$" <> show d <> "." <> cs

parseCents :: String -> Maybe Cents
parseCents str =
  let cleaned = filterDigits str
      len = String.length cleaned
  in if len == 0 then Nothing
     else if hasChar '.' str then parseDecimal cleaned else parseDollars cleaned

filterDigits :: String -> String
filterDigits str = foldl (\a c -> if isDigit c then a <> toStr c else a) "" (StringCU.toCharArray str)

hasChar :: Char -> String -> Boolean
hasChar t s = arrayHas t (StringCU.toCharArray s) 0

arrayHas :: Char -> Array Char -> Int -> Boolean
arrayHas t arr i = case Array.index arr i of
  Nothing -> false
  Just c -> if c == t then true else arrayHas t arr (i + 1)

isDigit :: Char -> Boolean
isDigit c = c == '0' || c == '1' || c == '2' || c == '3' || c == '4' 
         || c == '5' || c == '6' || c == '7' || c == '8' || c == '9'

toStr :: Char -> String
toStr '0' = "0"
toStr '1' = "1"
toStr '2' = "2"
toStr '3' = "3"
toStr '4' = "4"
toStr '5' = "5"
toStr '6' = "6"
toStr '7' = "7"
toStr '8' = "8"
toStr '9' = "9"
toStr _ = ""

parseDollars :: String -> Maybe Cents
parseDollars s = case strToInt s of
  Nothing -> Nothing
  Just n -> Just (cents (n * 100))

parseDecimal :: String -> Maybe Cents
parseDecimal s = case strToInt s of
  Nothing -> Nothing
  Just n -> Just (cents n)

strToInt :: String -> Maybe Int
strToInt s = strToIntH (StringCU.toCharArray s) 0 0

strToIntH :: Array Char -> Int -> Int -> Maybe Int
strToIntH chars i acc = case Array.index chars i of
  Nothing -> if i == 0 then Nothing else Just acc
  Just c -> case charDigit c of
    Nothing -> Nothing
    Just d -> strToIntH chars (i + 1) (acc * 10 + d)

charDigit :: Char -> Maybe Int
charDigit '0' = Just 0
charDigit '1' = Just 1
charDigit '2' = Just 2
charDigit '3' = Just 3
charDigit '4' = Just 4
charDigit '5' = Just 5
charDigit '6' = Just 6
charDigit '7' = Just 7
charDigit '8' = Just 8
charDigit '9' = Just 9
charDigit _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                          // odds
-- ═══════════════════════════════════════════════════════════════════════════════
data Odds = AmericanOdds Int | DecimalOdds Number | FractionalOdds Int Int
derive instance eqOdds :: Eq Odds
instance showOdds :: Show Odds where
  show (AmericanOdds n) = if n >= 0 then "+" <> show n else show n
  show (DecimalOdds n) = show n
  show (FractionalOdds num denom) = show num <> "/" <> show denom

americanOdds :: Int -> Odds
americanOdds n =
  let cl = clampInt (-100000) 100000 n
      adj = if cl > (-100) && cl < 100 then if cl >= 0 then 100 else (-100) else cl
  in AmericanOdds adj

decimalOdds :: Number -> Odds
decimalOdds n = DecimalOdds (if n < 1.01 then 1.01 else if n > 10001.0 then 10001.0 else n)

fractionalOdds :: Int -> Int -> Odds
fractionalOdds num denom =
  FractionalOdds (clampInt 1 10000 num) (clampInt 1 10000 denom)

toDecimalOdds :: Odds -> Number
toDecimalOdds (DecimalOdds d) = d
toDecimalOdds (AmericanOdds n) =
  if n >= 100 then (Int.toNumber n / 100.0) + 1.0
  else (100.0 / Int.toNumber (absInt n)) + 1.0
toDecimalOdds (FractionalOdds num denom) = (Int.toNumber num / Int.toNumber denom) + 1.0

toAmericanOdds :: Odds -> Int
toAmericanOdds (AmericanOdds n) = n
toAmericanOdds (DecimalOdds d) =
  if d >= 2.0 then Int.floor ((d - 1.0) * 100.0) else negate (Int.floor (100.0 / (d - 1.0)))
toAmericanOdds (FractionalOdds num denom) =
  if num >= denom then (num * 100) `div` denom else negate ((denom * 100) `div` num)

toFractionalOdds :: Odds -> { numerator :: Int, denominator :: Int }
toFractionalOdds (FractionalOdds num denom) = { numerator: num, denominator: denom }
toFractionalOdds odds =
  let dec = toDecimalOdds odds - 1.0
      num = Int.floor (dec * 100.0)
      g = gcd num 100
  in { numerator: num `div` g, denominator: 100 `div` g }

gcd :: Int -> Int -> Int
gcd a b = if b == 0 then absInt a else gcd b (a `mod` b)

impliedProbability :: Odds -> Number
impliedProbability odds = (1.0 / toDecimalOdds odds) * 100.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // bet types
-- ═══════════════════════════════════════════════════════════════════════════════
data BetType
  = RouletteStraight Int | RouletteSplit Int Int | RouletteStreet Int
  | RouletteCorner Int | RouletteLine Int | RouletteDozen Int | RouletteColumn Int
  | RouletteRed | RouletteBlack | RouletteOdd | RouletteEven | RouletteLow | RouletteHigh
  | CrapsPassLine | CrapsDontPass | CrapsCome | CrapsDontCome | CrapsField
  | CrapsPlace Int | CrapsHardway Int | CrapsAny7 | CrapsAnyCraps
  | BlackjackInsurance | BlackjackEvenMoney | BlackjackDouble | BlackjackSplit
  | CustomBet String Odds

derive instance eqBetType :: Eq BetType
instance showBetType :: Show BetType where
  show (RouletteStraight n) = "Straight " <> show n
  show (RouletteSplit a b) = "Split " <> show a <> "/" <> show b
  show (RouletteStreet n) = "Street " <> show n
  show (RouletteCorner n) = "Corner " <> show n
  show (RouletteLine n) = "Line " <> show n
  show (RouletteDozen n) = "Dozen " <> show n
  show (RouletteColumn n) = "Column " <> show n
  show RouletteRed = "Red"
  show RouletteBlack = "Black"
  show RouletteOdd = "Odd"
  show RouletteEven = "Even"
  show RouletteLow = "Low (1-18)"
  show RouletteHigh = "High (19-36)"
  show CrapsPassLine = "Pass Line"
  show CrapsDontPass = "Don't Pass"
  show CrapsCome = "Come"
  show CrapsDontCome = "Don't Come"
  show CrapsField = "Field"
  show (CrapsPlace n) = "Place " <> show n
  show (CrapsHardway n) = "Hardway " <> show n
  show CrapsAny7 = "Any 7"
  show CrapsAnyCraps = "Any Craps"
  show BlackjackInsurance = "Insurance"
  show BlackjackEvenMoney = "Even Money"
  show BlackjackDouble = "Double Down"
  show BlackjackSplit = "Split"
  show (CustomBet name _) = name

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // wager & bet result
-- ═══════════════════════════════════════════════════════════════════════════════
type Wager = { amount :: Cents, betType :: BetType }

wager :: Cents -> BetType -> Wager
wager amt bet = { amount: if amt < Cents 100 then Cents 100 else amt, betType: bet }

wagerAmount :: Wager -> Cents
wagerAmount w = w.amount

wagerType :: Wager -> BetType
wagerType w = w.betType

data BetResult = Win Cents | Loss | Push | PartialWin Cents
derive instance eqBetResult :: Eq BetResult
instance showBetResult :: Show BetResult where
  show (Win c) = "Win " <> formatCents c
  show Loss = "Loss"
  show Push = "Push"
  show (PartialWin c) = "Partial " <> formatCents c

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // bankroll
-- ═══════════════════════════════════════════════════════════════════════════════
type Bankroll = { balance :: Cents, sessionStart :: Cents, highWaterMark :: Cents, lowWaterMark :: Cents }

bankroll :: Cents -> Bankroll
bankroll s = { balance: s, sessionStart: s, highWaterMark: s, lowWaterMark: s }

bankrollBalance :: Bankroll -> Cents
bankrollBalance br = br.balance

sessionProfit :: Bankroll -> Cents
sessionProfit br =
  let Cents b = br.balance
      Cents s = br.sessionStart
  in Cents (b - s)

canAffordBet :: Cents -> Bankroll -> Boolean
canAffordBet (Cents a) br = let Cents b = br.balance in b >= a

updateBankroll :: Cents -> BetResult -> Bankroll -> Bankroll
updateBankroll (Cents w) result br =
  let Cents b = br.balance
      nb = case result of
        Win (Cents win) -> b + win
        Loss -> b - w
        Push -> b
        PartialWin (Cents p) -> b - w + p
      Cents hw = br.highWaterMark
      Cents lw = br.lowWaterMark
  in br { balance = Cents nb
        , highWaterMark = if nb > hw then Cents nb else br.highWaterMark
        , lowWaterMark = if nb < lw then Cents nb else br.lowWaterMark }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // payouts
-- ═══════════════════════════════════════════════════════════════════════════════
calculatePayout :: Odds -> Cents -> Cents
calculatePayout odds (Cents stake) =
  let dec = toDecimalOdds odds
      profit = Int.toNumber stake * dec - Int.toNumber stake
  in cents (Int.floor profit)

rouletteOdds :: BetType -> Odds
rouletteOdds (RouletteStraight _) = FractionalOdds 35 1
rouletteOdds (RouletteSplit _ _) = FractionalOdds 17 1
rouletteOdds (RouletteStreet _) = FractionalOdds 11 1
rouletteOdds (RouletteCorner _) = FractionalOdds 8 1
rouletteOdds (RouletteLine _) = FractionalOdds 5 1
rouletteOdds (RouletteDozen _) = FractionalOdds 2 1
rouletteOdds (RouletteColumn _) = FractionalOdds 2 1
rouletteOdds RouletteRed = FractionalOdds 1 1
rouletteOdds RouletteBlack = FractionalOdds 1 1
rouletteOdds RouletteOdd = FractionalOdds 1 1
rouletteOdds RouletteEven = FractionalOdds 1 1
rouletteOdds RouletteLow = FractionalOdds 1 1
rouletteOdds RouletteHigh = FractionalOdds 1 1
rouletteOdds _ = FractionalOdds 1 1

roulettePayout :: BetType -> Cents -> Cents
roulettePayout bet stake = calculatePayout (rouletteOdds bet) stake

crapsOdds :: BetType -> Odds
crapsOdds CrapsPassLine = FractionalOdds 1 1
crapsOdds CrapsDontPass = FractionalOdds 1 1
crapsOdds CrapsCome = FractionalOdds 1 1
crapsOdds CrapsDontCome = FractionalOdds 1 1
crapsOdds CrapsField = FractionalOdds 1 1
crapsOdds (CrapsPlace 6) = FractionalOdds 7 6
crapsOdds (CrapsPlace 8) = FractionalOdds 7 6
crapsOdds (CrapsPlace 5) = FractionalOdds 7 5
crapsOdds (CrapsPlace 9) = FractionalOdds 7 5
crapsOdds (CrapsPlace 4) = FractionalOdds 9 5
crapsOdds (CrapsPlace 10) = FractionalOdds 9 5
crapsOdds (CrapsPlace _) = FractionalOdds 1 1
crapsOdds (CrapsHardway 6) = FractionalOdds 9 1
crapsOdds (CrapsHardway 8) = FractionalOdds 9 1
crapsOdds (CrapsHardway 4) = FractionalOdds 7 1
crapsOdds (CrapsHardway 10) = FractionalOdds 7 1
crapsOdds (CrapsHardway _) = FractionalOdds 1 1
crapsOdds CrapsAny7 = FractionalOdds 4 1
crapsOdds CrapsAnyCraps = FractionalOdds 7 1
crapsOdds _ = FractionalOdds 1 1

crapsPayout :: BetType -> Cents -> Cents
crapsPayout bet stake = calculatePayout (crapsOdds bet) stake

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // house edge
-- ═══════════════════════════════════════════════════════════════════════════════
houseEdge :: BetType -> Number
houseEdge (RouletteStraight _) = 5.26
houseEdge (RouletteSplit _ _) = 5.26
houseEdge (RouletteStreet _) = 5.26
houseEdge (RouletteCorner _) = 5.26
houseEdge (RouletteLine _) = 5.26
houseEdge (RouletteDozen _) = 5.26
houseEdge (RouletteColumn _) = 5.26
houseEdge RouletteRed = 5.26
houseEdge RouletteBlack = 5.26
houseEdge RouletteOdd = 5.26
houseEdge RouletteEven = 5.26
houseEdge RouletteLow = 5.26
houseEdge RouletteHigh = 5.26
houseEdge CrapsPassLine = 1.41
houseEdge CrapsDontPass = 1.36
houseEdge CrapsCome = 1.41
houseEdge CrapsDontCome = 1.36
houseEdge CrapsField = 5.56
houseEdge (CrapsPlace 6) = 1.52
houseEdge (CrapsPlace 8) = 1.52
houseEdge (CrapsPlace 5) = 4.0
houseEdge (CrapsPlace 9) = 4.0
houseEdge (CrapsPlace 4) = 6.67
houseEdge (CrapsPlace 10) = 6.67
houseEdge (CrapsPlace _) = 5.0
houseEdge (CrapsHardway 6) = 9.09
houseEdge (CrapsHardway 8) = 9.09
houseEdge (CrapsHardway 4) = 11.11
houseEdge (CrapsHardway 10) = 11.11
houseEdge (CrapsHardway _) = 10.0
houseEdge CrapsAny7 = 16.67
houseEdge CrapsAnyCraps = 11.11
houseEdge BlackjackInsurance = 7.47
houseEdge BlackjackEvenMoney = 0.0
houseEdge BlackjackDouble = 0.0
houseEdge BlackjackSplit = 0.0
houseEdge (CustomBet _ odds) = 100.0 - impliedProbability odds

trueOdds :: BetType -> Odds
trueOdds (RouletteStraight _) = FractionalOdds 37 1
trueOdds (RouletteSplit _ _) = FractionalOdds 18 1
trueOdds (RouletteStreet _) = FractionalOdds 35 3
trueOdds (RouletteCorner _) = FractionalOdds 17 2
trueOdds (RouletteLine _) = FractionalOdds 16 3
trueOdds (RouletteDozen _) = FractionalOdds 13 6
trueOdds (RouletteColumn _) = FractionalOdds 13 6
trueOdds RouletteRed = FractionalOdds 20 18
trueOdds RouletteBlack = FractionalOdds 20 18
trueOdds RouletteOdd = FractionalOdds 20 18
trueOdds RouletteEven = FractionalOdds 20 18
trueOdds RouletteLow = FractionalOdds 20 18
trueOdds RouletteHigh = FractionalOdds 20 18
trueOdds CrapsPassLine = FractionalOdds 251 244
trueOdds CrapsDontPass = FractionalOdds 244 251
trueOdds CrapsCome = FractionalOdds 251 244
trueOdds CrapsDontCome = FractionalOdds 244 251
trueOdds CrapsField = FractionalOdds 5 4
trueOdds (CrapsPlace 6) = FractionalOdds 6 5
trueOdds (CrapsPlace 8) = FractionalOdds 6 5
trueOdds (CrapsPlace 5) = FractionalOdds 3 2
trueOdds (CrapsPlace 9) = FractionalOdds 3 2
trueOdds (CrapsPlace 4) = FractionalOdds 2 1
trueOdds (CrapsPlace 10) = FractionalOdds 2 1
trueOdds (CrapsPlace _) = FractionalOdds 1 1
trueOdds (CrapsHardway 6) = FractionalOdds 10 1
trueOdds (CrapsHardway 8) = FractionalOdds 10 1
trueOdds (CrapsHardway 4) = FractionalOdds 8 1
trueOdds (CrapsHardway 10) = FractionalOdds 8 1
trueOdds (CrapsHardway _) = FractionalOdds 1 1
trueOdds CrapsAny7 = FractionalOdds 5 1
trueOdds CrapsAnyCraps = FractionalOdds 8 1
trueOdds BlackjackInsurance = FractionalOdds 9 4
trueOdds BlackjackEvenMoney = FractionalOdds 1 1
trueOdds BlackjackDouble = FractionalOdds 1 1
trueOdds BlackjackSplit = FractionalOdds 1 1
trueOdds (CustomBet _ odds) = odds

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // bet sizing
-- ═══════════════════════════════════════════════════════════════════════════════
kellyBet :: Odds -> Number -> Cents -> Cents
kellyBet odds edge (Cents br) =
  let b = toDecimalOdds odds - 1.0
      p = (edge + 1.0) / (b + 1.0)
      q = 1.0 - p
      kf = if b > 0.0 then (b * p - q) / b else 0.0
      sf = if kf < 0.0 then 0.0 else if kf > 1.0 then 1.0 else kf
  in cents (Int.floor (Int.toNumber br * sf))

kellyFractional :: Number -> Odds -> Number -> Cents -> Cents
kellyFractional frac odds edge br =
  let Cents full = kellyBet odds edge br
  in cents (Int.floor (Int.toNumber full * frac))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // bounds
-- ═══════════════════════════════════════════════════════════════════════════════
centsBounds :: IntBounds
centsBounds = intBounds 0 2000000000 Clamps "cents" "Monetary amount in cents (0 to $20M)"

wagerBounds :: IntBounds
wagerBounds = intBounds 100 100000000 Clamps "wager" "Wager amount ($1 min to $1M max)"
