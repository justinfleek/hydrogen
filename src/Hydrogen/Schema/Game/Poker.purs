-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // schema // game
--                                                                      // poker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Complete poker hand evaluation, rankings, comparisons, and odds.
-- | Pure functions over Card vocabulary. All operations total.

module Hydrogen.Schema.Game.Poker
  ( HandRank(RoyalFlush, StraightFlush, FourOfAKind, FullHouse, Flush,
             Straight, ThreeOfAKind, TwoPair, OnePair, HighCard)
  , handRankValue, formatHandRank
  , EvaluatedHand, evaluateHand, bestFiveCards, compareHands
  , isFlush, isStraight, hasNOfAKind, countRank, countSuit
  , PokerVariant(TexasHoldem, Omaha, OmahaHiLo, SevenCardStud, FiveCardDraw, Razz)
  , HandState(Folded, Active, AllIn)
  , PotOdds, calculatePotOdds, isProfitableCall
  , EquityResult, countOuts, startingHandStrength
  ) where

import Prelude
  ( class Eq, class Ord, class Show, show, compare, otherwise, map, not
  , (==), (/=), (+), (-), (*), (/), (>), (<), (>=), (<=), (&&), (||), (<>)
  , Ordering(LT, EQ, GT)
  )
import Prim (Boolean, Int, Number, Array, String)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (length, filter, sortBy, take, head, reverse, index, null, drop, snoc)
import Data.Ord (comparing)
import Data.Int (toNumber) as Int
import Hydrogen.Schema.Game.Card
  ( Suit(Clubs, Diamonds, Hearts, Spades)
  , Rank(Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten, Jack, Queen, King, Ace)
  , Card, allRanks, rankValue
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // hand // rankings
-- ═══════════════════════════════════════════════════════════════════════════════

data HandRank
  = RoyalFlush | StraightFlush | FourOfAKind | FullHouse | Flush
  | Straight | ThreeOfAKind | TwoPair | OnePair | HighCard

derive instance eqHandRank :: Eq HandRank
instance ordHandRank :: Ord HandRank where
  compare a b = compare (handRankValue a) (handRankValue b)

instance showHandRank :: Show HandRank where
  show RoyalFlush = "RoyalFlush"
  show StraightFlush = "StraightFlush"
  show FourOfAKind = "FourOfAKind"
  show FullHouse = "FullHouse"
  show Flush = "Flush"
  show Straight = "Straight"
  show ThreeOfAKind = "ThreeOfAKind"
  show TwoPair = "TwoPair"
  show OnePair = "OnePair"
  show HighCard = "HighCard"

handRankValue :: HandRank -> Int
handRankValue RoyalFlush = 10
handRankValue StraightFlush = 9
handRankValue FourOfAKind = 8
handRankValue FullHouse = 7
handRankValue Flush = 6
handRankValue Straight = 5
handRankValue ThreeOfAKind = 4
handRankValue TwoPair = 3
handRankValue OnePair = 2
handRankValue HighCard = 1

formatHandRank :: HandRank -> String
formatHandRank RoyalFlush = "Royal Flush"
formatHandRank StraightFlush = "Straight Flush"
formatHandRank FourOfAKind = "Four of a Kind"
formatHandRank FullHouse = "Full House"
formatHandRank Flush = "Flush"
formatHandRank Straight = "Straight"
formatHandRank ThreeOfAKind = "Three of a Kind"
formatHandRank TwoPair = "Two Pair"
formatHandRank OnePair = "One Pair"
formatHandRank HighCard = "High Card"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // evaluated // hands
-- ═══════════════════════════════════════════════════════════════════════════════

type EvaluatedHand =
  { rank :: HandRank, primaryRanks :: Array Rank, kickers :: Array Rank }

compareHands :: EvaluatedHand -> EvaluatedHand -> Ordering
compareHands h1 h2 = case compare h1.rank h2.rank of
  EQ -> case compareRankArrays h1.primaryRanks h2.primaryRanks of
    EQ -> compareRankArrays h1.kickers h2.kickers
    other -> other
  other -> other

compareRankArrays :: Array Rank -> Array Rank -> Ordering
compareRankArrays arr1 arr2 = case index arr1 0 of
  Nothing -> EQ
  Just r1 -> case index arr2 0 of
    Nothing -> EQ
    Just r2 -> case compare (rankValue r1) (rankValue r2) of
      EQ -> compareRankArrays (drop 1 arr1) (drop 1 arr2)
      other -> other

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // detection // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

isFlush :: Array Card -> Boolean
isFlush cards = case head cards of
  Nothing -> false
  Just first -> length (filter (\c -> c.suit == first.suit) cards) >= 5

isStraight :: Array Card -> Boolean
isStraight cards = isConsecutive (map (\c -> c.rank) cards) || isWheel cards

isWheel :: Array Card -> Boolean
isWheel cards = let rs = map (\c -> c.rank) cards
  in hasRank Ace rs && hasRank Two rs && hasRank Three rs && hasRank Four rs && hasRank Five rs

isConsecutive :: Array Rank -> Boolean
isConsecutive ranks =
  let sorted = sortBy (comparing rankValue) (uniqueRanks ranks)
  in length sorted >= 5 && checkConsec 0 sorted

checkConsec :: Int -> Array Rank -> Boolean
checkConsec i arr = if i >= length arr - 1 then true else
  case index arr i of
    Nothing -> true
    Just r1 -> case index arr (i + 1) of
      Nothing -> true
      Just r2 -> if rankValue r2 - rankValue r1 == 1 then checkConsec (i + 1) arr else false

hasNOfAKind :: Int -> Array Card -> Boolean
hasNOfAKind n cards = findNOfAKind n allRanks cards /= Nothing

findNOfAKind :: Int -> Array Rank -> Array Card -> Maybe Rank
findNOfAKind n ranks cards = case head ranks of
  Nothing -> Nothing
  Just r -> if countRank r cards == n then Just r else findNOfAKind n (drop 1 ranks) cards

countRank :: Rank -> Array Card -> Int
countRank r cards = length (filter (\c -> c.rank == r) cards)

countSuit :: Suit -> Array Card -> Int
countSuit s cards = length (filter (\c -> c.suit == s) cards)

hasRank :: Rank -> Array Rank -> Boolean
hasRank r rs = not (null (filter (\x -> x == r) rs))

uniqueRanks :: Array Rank -> Array Rank
uniqueRanks = uniqueRanksAcc []

uniqueRanksAcc :: Array Rank -> Array Rank -> Array Rank
uniqueRanksAcc acc ranks = case head ranks of
  Nothing -> acc
  Just r -> if hasRank r acc then uniqueRanksAcc acc (drop 1 ranks)
            else uniqueRanksAcc (snoc acc r) (drop 1 ranks)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // hand // evaluation
-- ═══════════════════════════════════════════════════════════════════════════════

evaluateHand :: Array Card -> EvaluatedHand
evaluateHand cards = evaluateFive (bestFiveCards cards)

bestFiveCards :: Array Card -> Array Card
bestFiveCards cards = if length cards <= 5 then cards else findBestFive cards

findBestFive :: Array Card -> Array Card
findBestFive cards =
  let combos = combinations5 cards
      evaled = map (\c -> { cs: c, ev: evaluateFive c }) combos
      sorted = reverse (sortBy (comparing (\e -> e.ev)) evaled)
  in case head sorted of
    Nothing -> take 5 cards
    Just best -> best.cs

evaluateFive :: Array Card -> EvaluatedHand
evaluateFive cards
  | checkRoyal cards = mkRoyal
  | checkStraightFlush cards = mkStraightFlush cards
  | hasNOfAKind 4 cards = mkFourKind cards
  | checkFullHouse cards = mkFullHouse cards
  | isFlush cards = mkFlush cards
  | isStraight cards = mkStraight cards
  | hasNOfAKind 3 cards = mkThreeKind cards
  | checkTwoPair cards = mkTwoPair cards
  | hasNOfAKind 2 cards = mkOnePair cards
  | otherwise = mkHighCard cards

checkRoyal :: Array Card -> Boolean
checkRoyal cards = isFlush cards && hasRank Ace rs && hasRank King rs && hasRank Queen rs && hasRank Jack rs && hasRank Ten rs
  where rs = map (\c -> c.rank) cards

checkStraightFlush :: Array Card -> Boolean
checkStraightFlush cards = isFlush cards && isStraight cards

checkFullHouse :: Array Card -> Boolean
checkFullHouse cards = case findNOfAKind 3 allRanks cards of
  Nothing -> false
  Just tr -> hasNOfAKind 2 (filter (\c -> c.rank /= tr) cards)

checkTwoPair :: Array Card -> Boolean
checkTwoPair cards = case findNOfAKind 2 (reverse allRanks) cards of
  Nothing -> false
  Just p1 -> hasNOfAKind 2 (filter (\c -> c.rank /= p1) cards)

mkRoyal :: EvaluatedHand
mkRoyal = { rank: RoyalFlush, primaryRanks: [Ace, King, Queen, Jack, Ten], kickers: [] }

mkStraightFlush :: Array Card -> EvaluatedHand
mkStraightFlush cards = { rank: StraightFlush, primaryRanks: [getStraightHigh cards], kickers: [] }

mkFourKind :: Array Card -> EvaluatedHand
mkFourKind cards = case findNOfAKind 4 allRanks cards of
  Nothing -> mkHighCard cards
  Just qr -> { rank: FourOfAKind, primaryRanks: [qr], kickers: [highestExcluding [qr] cards] }

mkFullHouse :: Array Card -> EvaluatedHand
mkFullHouse cards = case findNOfAKind 3 allRanks cards of
  Nothing -> mkHighCard cards
  Just tr -> case findNOfAKind 2 allRanks (filter (\c -> c.rank /= tr) cards) of
    Nothing -> mkHighCard cards
    Just pr -> { rank: FullHouse, primaryRanks: [tr, pr], kickers: [] }

mkFlush :: Array Card -> EvaluatedHand
mkFlush cards = { rank: Flush, primaryRanks: take 5 (map (\c -> c.rank) (sortDesc cards)), kickers: [] }

mkStraight :: Array Card -> EvaluatedHand
mkStraight cards = { rank: Straight, primaryRanks: [getStraightHigh cards], kickers: [] }

mkThreeKind :: Array Card -> EvaluatedHand
mkThreeKind cards = case findNOfAKind 3 allRanks cards of
  Nothing -> mkHighCard cards
  Just tr -> { rank: ThreeOfAKind, primaryRanks: [tr]
             , kickers: take 2 (map (\c -> c.rank) (sortDesc (filter (\c -> c.rank /= tr) cards))) }

mkTwoPair :: Array Card -> EvaluatedHand
mkTwoPair cards = case findNOfAKind 2 (reverse allRanks) cards of
  Nothing -> mkHighCard cards
  Just p1 -> case findNOfAKind 2 (reverse allRanks) (filter (\c -> c.rank /= p1) cards) of
    Nothing -> mkHighCard cards
    Just p2 -> let hi = if rankValue p1 > rankValue p2 then p1 else p2
                   lo = if rankValue p1 > rankValue p2 then p2 else p1
               in { rank: TwoPair, primaryRanks: [hi, lo]
                  , kickers: [highestExcluding [p1, p2] cards] }

mkOnePair :: Array Card -> EvaluatedHand
mkOnePair cards = case findNOfAKind 2 (reverse allRanks) cards of
  Nothing -> mkHighCard cards
  Just pr -> { rank: OnePair, primaryRanks: [pr]
             , kickers: take 3 (map (\c -> c.rank) (sortDesc (filter (\c -> c.rank /= pr) cards))) }

mkHighCard :: Array Card -> EvaluatedHand
mkHighCard cards = let sorted = sortDesc cards
  in case head sorted of
    Nothing -> { rank: HighCard, primaryRanks: [], kickers: [] }
    Just h -> { rank: HighCard, primaryRanks: [h.rank], kickers: take 4 (map (\c -> c.rank) (drop 1 sorted)) }

sortDesc :: Array Card -> Array Card
sortDesc cards = reverse (sortBy (comparing (\c -> rankValue c.rank)) cards)

getStraightHigh :: Array Card -> Rank
getStraightHigh cards = if isWheel cards then Five else case head (sortDesc cards) of
  Nothing -> Two
  Just c -> c.rank

highestExcluding :: Array Rank -> Array Card -> Rank
highestExcluding excl cards = case head (sortDesc (filter (\c -> not (hasRank c.rank excl)) cards)) of
  Nothing -> Two
  Just c -> c.rank

combinations5 :: Array Card -> Array (Array Card)
combinations5 cards
  | length cards < 5 = [cards]
  | length cards == 5 = [cards]
  | length cards == 6 = [rm 0 cards, rm 1 cards, rm 2 cards, rm 3 cards, rm 4 cards, rm 5 cards]
  | otherwise = [ rm2 0 1 cards, rm2 0 2 cards, rm2 0 3 cards, rm2 0 4 cards, rm2 0 5 cards, rm2 0 6 cards
                , rm2 1 2 cards, rm2 1 3 cards, rm2 1 4 cards, rm2 1 5 cards, rm2 1 6 cards
                , rm2 2 3 cards, rm2 2 4 cards, rm2 2 5 cards, rm2 2 6 cards
                , rm2 3 4 cards, rm2 3 5 cards, rm2 3 6 cards, rm2 4 5 cards, rm2 4 6 cards, rm2 5 6 cards ]

rm :: Int -> Array Card -> Array Card
rm idx arr = rmAcc 0 idx [] arr

rmAcc :: Int -> Int -> Array Card -> Array Card -> Array Card
rmAcc i t acc arr = case head arr of
  Nothing -> acc
  Just x -> if i == t then rmAcc (i+1) t acc (drop 1 arr) else rmAcc (i+1) t (snoc acc x) (drop 1 arr)

rm2 :: Int -> Int -> Array Card -> Array Card
rm2 i1 i2 arr = rm2Acc 0 i1 i2 [] arr

rm2Acc :: Int -> Int -> Int -> Array Card -> Array Card -> Array Card
rm2Acc i t1 t2 acc arr = case head arr of
  Nothing -> acc
  Just x -> if i == t1 || i == t2 then rm2Acc (i+1) t1 t2 acc (drop 1 arr) else rm2Acc (i+1) t1 t2 (snoc acc x) (drop 1 arr)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // variants // state
-- ═══════════════════════════════════════════════════════════════════════════════

data PokerVariant = TexasHoldem | Omaha | OmahaHiLo | SevenCardStud | FiveCardDraw | Razz

derive instance eqPokerVariant :: Eq PokerVariant
derive instance ordPokerVariant :: Ord PokerVariant

instance showPokerVariant :: Show PokerVariant where
  show TexasHoldem = "Texas Hold'em"
  show Omaha = "Omaha"
  show OmahaHiLo = "Omaha Hi-Lo"
  show SevenCardStud = "Seven Card Stud"
  show FiveCardDraw = "Five Card Draw"
  show Razz = "Razz"

data HandState = Folded | Active (Array Card) | AllIn (Array Card)

derive instance eqHandState :: Eq HandState

instance showHandState :: Show HandState where
  show Folded = "Folded"
  show (Active cards) = "Active(" <> show (length cards) <> " cards)"
  show (AllIn cards) = "AllIn(" <> show (length cards) <> " cards)"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // odds // outs
-- ═══════════════════════════════════════════════════════════════════════════════

type PotOdds = { pot :: Int, toCall :: Int }

calculatePotOdds :: PotOdds -> Number
calculatePotOdds odds = if odds.toCall <= 0 then 0.0 else toNumber odds.pot / toNumber odds.toCall

isProfitableCall :: PotOdds -> Number -> Boolean
isProfitableCall odds winProb = winProb >= toNumber odds.toCall / toNumber (odds.pot + odds.toCall)

type EquityResult = { winPercent :: Number, tiePercent :: Number, losePercent :: Number }

countOuts :: Array Card -> Array Card -> Int
countOuts hole board = countImproving (evaluateHand (hole <> board)) (hole <> board) (filterOut (hole <> board) deck52)

countImproving :: EvaluatedHand -> Array Card -> Array Card -> Int
countImproving curr hand remaining = countImpAcc curr hand remaining 0

countImpAcc :: EvaluatedHand -> Array Card -> Array Card -> Int -> Int
countImpAcc curr hand rem acc = case head rem of
  Nothing -> acc
  Just c -> let newEv = evaluateHand (snoc hand c)
                better = compareHands newEv curr == GT
            in countImpAcc curr hand (drop 1 rem) (if better then acc + 1 else acc)

filterOut :: Array Card -> Array Card -> Array Card
filterOut known deck = filter (\c -> not (cardIn c known)) deck

cardIn :: Card -> Array Card -> Boolean
cardIn c arr = not (null (filter (\x -> x.rank == c.rank && x.suit == c.suit) arr))

deck52 :: Array Card
deck52 = [ {rank: Two, suit: Clubs}, {rank: Two, suit: Diamonds}, {rank: Two, suit: Hearts}, {rank: Two, suit: Spades}
  , {rank: Three, suit: Clubs}, {rank: Three, suit: Diamonds}, {rank: Three, suit: Hearts}, {rank: Three, suit: Spades}
  , {rank: Four, suit: Clubs}, {rank: Four, suit: Diamonds}, {rank: Four, suit: Hearts}, {rank: Four, suit: Spades}
  , {rank: Five, suit: Clubs}, {rank: Five, suit: Diamonds}, {rank: Five, suit: Hearts}, {rank: Five, suit: Spades}
  , {rank: Six, suit: Clubs}, {rank: Six, suit: Diamonds}, {rank: Six, suit: Hearts}, {rank: Six, suit: Spades}
  , {rank: Seven, suit: Clubs}, {rank: Seven, suit: Diamonds}, {rank: Seven, suit: Hearts}, {rank: Seven, suit: Spades}
  , {rank: Eight, suit: Clubs}, {rank: Eight, suit: Diamonds}, {rank: Eight, suit: Hearts}, {rank: Eight, suit: Spades}
  , {rank: Nine, suit: Clubs}, {rank: Nine, suit: Diamonds}, {rank: Nine, suit: Hearts}, {rank: Nine, suit: Spades}
  , {rank: Ten, suit: Clubs}, {rank: Ten, suit: Diamonds}, {rank: Ten, suit: Hearts}, {rank: Ten, suit: Spades}
  , {rank: Jack, suit: Clubs}, {rank: Jack, suit: Diamonds}, {rank: Jack, suit: Hearts}, {rank: Jack, suit: Spades}
  , {rank: Queen, suit: Clubs}, {rank: Queen, suit: Diamonds}, {rank: Queen, suit: Hearts}, {rank: Queen, suit: Spades}
  , {rank: King, suit: Clubs}, {rank: King, suit: Diamonds}, {rank: King, suit: Hearts}, {rank: King, suit: Spades}
  , {rank: Ace, suit: Clubs}, {rank: Ace, suit: Diamonds}, {rank: Ace, suit: Hearts}, {rank: Ace, suit: Spades} ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // starting // hands
-- ═══════════════════════════════════════════════════════════════════════════════

startingHandStrength :: Card -> Card -> Int
startingHandStrength c1 c2 =
  let r1 = rankValue c1.rank
      r2 = rankValue c2.rank
      hi = if r1 >= r2 then r1 else r2
      lo = if r1 >= r2 then r2 else r1
      suited = c1.suit == c2.suit
      paired = c1.rank == c2.rank
  in strength hi lo suited paired

strength :: Int -> Int -> Boolean -> Boolean -> Int
strength hi lo suited paired
  | paired && hi == 14 = 1   | paired && hi == 13 = 2   | paired && hi == 12 = 3
  | hi == 14 && lo == 13 && suited = 4   | paired && hi == 11 = 5   | hi == 14 && lo == 13 = 6
  | hi == 14 && lo == 12 && suited = 7   | hi == 13 && lo == 12 && suited = 8
  | hi == 14 && lo == 11 && suited = 9   | paired && hi == 10 = 10
  | hi == 14 && lo == 12 = 11  | hi == 14 && lo == 10 && suited = 12
  | hi == 13 && lo == 11 && suited = 13  | hi == 12 && lo == 11 && suited = 14
  | hi == 13 && lo == 12 = 15  | paired && hi == 9 = 16  | hi == 14 && lo == 11 = 17
  | hi == 13 && lo == 10 && suited = 18  | hi == 11 && lo == 10 && suited = 19
  | hi == 12 && lo == 10 && suited = 20  | paired && hi == 8 = 25  | paired && hi == 7 = 35
  | paired && hi == 6 = 45  | paired && hi == 5 = 55  | paired && hi == 4 = 65
  | paired && hi == 3 = 75  | paired && hi == 2 = 85
  | suited = 50 + (14 - hi) * 5 + (hi - lo)
  | otherwise = 100 + (14 - hi) * 6 + (hi - lo) * 2

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // numeric // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number for odds calculations.
toNumber :: Int -> Number
toNumber = Int.toNumber
