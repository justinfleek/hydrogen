-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // schema // game
--                                                                       // card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Complete playing card vocabulary for standard 52-card deck.
-- | Cards are pure data. All 52 cards enumerable, all operations total.
-- | Suits follow bridge order: Clubs < Diamonds < Hearts < Spades

module Hydrogen.Schema.Game.Card
  ( -- * Suits
    Suit(Clubs, Diamonds, Hearts, Spades)
  , allSuits, suitSymbol, suitColor, compareSuits
  -- * Card Colors
  , CardColor(Red, Black)
  -- * Ranks
  , Rank(Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten, Jack, Queen, King, Ace)
  , allRanks, rankSymbol, rankValue, compareRanks, isAce, isFaceCard, isNumberCard
  -- * Cards
  , Card, card, formatCard, parseCard, compareCards
  -- * Facing
  , Facing(FaceUp, FaceDown)
  -- * Playing Cards (with facing)
  , PlayingCard, playingCard, flipCard
  -- * Deck Position
  , DeckPosition(DeckPosition)
  , deckPosition, unwrapDeckPosition, cardAtPosition, positionOfCard
  -- * Deck Operations
  , standardDeck
  -- * Hands
  , Hand
  -- * Poker Hand Rankings
  , PokerHand(HighCard, OnePair, TwoPair, ThreeOfAKind, Straight, Flush, FullHouse, FourOfAKind, StraightFlush, RoyalFlush)
  -- * Blackjack
  , BlackjackValue(Hard, Soft, Bust), blackjackValue, blackjackRankValue
  ) where

import Prelude
  ( class Eq, class Ord, class Show
  , show, compare, otherwise, map, mod, div, bind, pure
  , (==), (+), (*), (>), (<=), (>=), (&&), (<>), Ordering(EQ)
  )
import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (foldl)
import Data.String.CodeUnits (length, take, drop) as StrCU
import Hydrogen.Schema.Bounded (clampInt)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // card // color
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Card colors: Red (Diamonds, Hearts) or Black (Clubs, Spades)
data CardColor = Red | Black

derive instance eqCardColor :: Eq CardColor
derive instance ordCardColor :: Ord CardColor

instance showCardColor :: Show CardColor where
  show Red = "Red"
  show Black = "Black"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // suits
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Four suits in bridge order (lowest to highest)
data Suit = Clubs | Diamonds | Hearts | Spades

derive instance eqSuit :: Eq Suit
derive instance ordSuit :: Ord Suit

instance showSuit :: Show Suit where
  show Clubs = "Clubs"
  show Diamonds = "Diamonds"
  show Hearts = "Hearts"
  show Spades = "Spades"

-- | All four suits in bridge order
allSuits :: Array Suit
allSuits = [ Clubs, Diamonds, Hearts, Spades ]

-- | Unicode symbol: ♣♦♥♠
suitSymbol :: Suit -> String
suitSymbol Clubs = "♣"
suitSymbol Diamonds = "♦"
suitSymbol Hearts = "♥"
suitSymbol Spades = "♠"

-- | Red: Diamonds/Hearts, Black: Clubs/Spades
suitColor :: Suit -> CardColor
suitColor Clubs = Black
suitColor Diamonds = Red
suitColor Hearts = Red
suitColor Spades = Black

-- | Compare suits in bridge order
compareSuits :: Suit -> Suit -> Ordering
compareSuits = compare

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // ranks
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Card ranks Two (2) through Ace (14, high)
data Rank = Two | Three | Four | Five | Six | Seven | Eight | Nine | Ten | Jack | Queen | King | Ace

derive instance eqRank :: Eq Rank
derive instance ordRank :: Ord Rank

instance showRank :: Show Rank where
  show Two = "Two"
  show Three = "Three"
  show Four = "Four"
  show Five = "Five"
  show Six = "Six"
  show Seven = "Seven"
  show Eight = "Eight"
  show Nine = "Nine"
  show Ten = "Ten"
  show Jack = "Jack"
  show Queen = "Queen"
  show King = "King"
  show Ace = "Ace"

-- | All thirteen ranks ascending
allRanks :: Array Rank
allRanks = [ Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten, Jack, Queen, King, Ace ]

-- | Display symbol: "2"-"10", "J", "Q", "K", "A"
rankSymbol :: Rank -> String
rankSymbol Two = "2"
rankSymbol Three = "3"
rankSymbol Four = "4"
rankSymbol Five = "5"
rankSymbol Six = "6"
rankSymbol Seven = "7"
rankSymbol Eight = "8"
rankSymbol Nine = "9"
rankSymbol Ten = "10"
rankSymbol Jack = "J"
rankSymbol Queen = "Q"
rankSymbol King = "K"
rankSymbol Ace = "A"

-- | Numeric value (Ace=14, King=13, ..., Two=2)
rankValue :: Rank -> Int
rankValue Two = 2
rankValue Three = 3
rankValue Four = 4
rankValue Five = 5
rankValue Six = 6
rankValue Seven = 7
rankValue Eight = 8
rankValue Nine = 9
rankValue Ten = 10
rankValue Jack = 11
rankValue Queen = 12
rankValue King = 13
rankValue Ace = 14

compareRanks :: Rank -> Rank -> Ordering
compareRanks = compare

isAce :: Rank -> Boolean
isAce Ace = true
isAce _ = false

isFaceCard :: Rank -> Boolean
isFaceCard Jack = true
isFaceCard Queen = true
isFaceCard King = true
isFaceCard _ = false

isNumberCard :: Rank -> Boolean
isNumberCard r = rankValue r >= 2 && rankValue r <= 10

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // cards
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A playing card: rank and suit pair
type Card = { rank :: Rank, suit :: Suit }

-- | Smart constructor
card :: Rank -> Suit -> Card
card r s = { rank: r, suit: s }

-- | Format for display: "A♠", "10♥", "2♣"
formatCard :: Card -> String
formatCard c = rankSymbol c.rank <> suitSymbol c.suit

-- | Parse from string: "A♠", "10H", "2c"
parseCard :: String -> Maybe Card
parseCard s = do
  { rank: r, rest } <- parseRankPrefix s
  suit' <- parseSuit rest
  pure { rank: r, suit: suit' }

-- | Compare by rank first, then suit
compareCards :: Card -> Card -> Ordering
compareCards c1 c2 =
  case compare c1.rank c2.rank of
    EQ -> compare c1.suit c2.suit
    other -> other

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // parse // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

parseRankPrefix :: String -> Maybe { rank :: Rank, rest :: String }
parseRankPrefix s
  | stringStartsWith "10" s = Just { rank: Ten, rest: stringDrop 2 s }
  | stringStartsWith "A" s = Just { rank: Ace, rest: stringDrop 1 s }
  | stringStartsWith "K" s = Just { rank: King, rest: stringDrop 1 s }
  | stringStartsWith "Q" s = Just { rank: Queen, rest: stringDrop 1 s }
  | stringStartsWith "J" s = Just { rank: Jack, rest: stringDrop 1 s }
  | stringStartsWith "9" s = Just { rank: Nine, rest: stringDrop 1 s }
  | stringStartsWith "8" s = Just { rank: Eight, rest: stringDrop 1 s }
  | stringStartsWith "7" s = Just { rank: Seven, rest: stringDrop 1 s }
  | stringStartsWith "6" s = Just { rank: Six, rest: stringDrop 1 s }
  | stringStartsWith "5" s = Just { rank: Five, rest: stringDrop 1 s }
  | stringStartsWith "4" s = Just { rank: Four, rest: stringDrop 1 s }
  | stringStartsWith "3" s = Just { rank: Three, rest: stringDrop 1 s }
  | stringStartsWith "2" s = Just { rank: Two, rest: stringDrop 1 s }
  | otherwise = Nothing

parseSuit :: String -> Maybe Suit
parseSuit "♠" = Just Spades
parseSuit "♥" = Just Hearts
parseSuit "♦" = Just Diamonds
parseSuit "♣" = Just Clubs
parseSuit "S" = Just Spades
parseSuit "H" = Just Hearts
parseSuit "D" = Just Diamonds
parseSuit "C" = Just Clubs
parseSuit "s" = Just Spades
parseSuit "h" = Just Hearts
parseSuit "d" = Just Diamonds
parseSuit "c" = Just Clubs
parseSuit _ = Nothing

stringStartsWith :: String -> String -> Boolean
stringStartsWith prefix str = StrCU.take (StrCU.length prefix) str == prefix

stringDrop :: Int -> String -> String
stringDrop = StrCU.drop

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // facing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Card visibility state
data Facing = FaceUp | FaceDown

derive instance eqFacing :: Eq Facing
derive instance ordFacing :: Ord Facing

instance showFacing :: Show Facing where
  show FaceUp = "FaceUp"
  show FaceDown = "FaceDown"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // playing // card
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Card in play with visibility state
type PlayingCard = { card :: Card, facing :: Facing }

playingCard :: Card -> Facing -> PlayingCard
playingCard c f = { card: c, facing: f }

flipCard :: PlayingCard -> PlayingCard
flipCard pc = pc { facing = flipFacing pc.facing }

flipFacing :: Facing -> Facing
flipFacing FaceUp = FaceDown
flipFacing FaceDown = FaceUp

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // deck // position
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Deck position bounded 0-51. Encoding: rankIndex*4 + suitIndex
newtype DeckPosition = DeckPosition Int

derive instance eqDeckPosition :: Eq DeckPosition
derive instance ordDeckPosition :: Ord DeckPosition

instance showDeckPosition :: Show DeckPosition where
  show (DeckPosition n) = "DeckPosition(" <> show n <> ")"

-- | Smart constructor clamping to 0-51
deckPosition :: Int -> DeckPosition
deckPosition n = DeckPosition (clampInt 0 51 n)

unwrapDeckPosition :: DeckPosition -> Int
unwrapDeckPosition (DeckPosition n) = n

-- | Bijection: position -> card
cardAtPosition :: DeckPosition -> Card
cardAtPosition (DeckPosition n) =
  { rank: rankFromIndex (div n 4), suit: suitFromIndex (mod n 4) }

-- | Bijection: card -> position
positionOfCard :: Card -> DeckPosition
positionOfCard c = DeckPosition (rankToIndex c.rank * 4 + suitToIndex c.suit)

rankFromIndex :: Int -> Rank
rankFromIndex 0 = Two
rankFromIndex 1 = Three
rankFromIndex 2 = Four
rankFromIndex 3 = Five
rankFromIndex 4 = Six
rankFromIndex 5 = Seven
rankFromIndex 6 = Eight
rankFromIndex 7 = Nine
rankFromIndex 8 = Ten
rankFromIndex 9 = Jack
rankFromIndex 10 = Queen
rankFromIndex 11 = King
rankFromIndex _ = Ace

rankToIndex :: Rank -> Int
rankToIndex Two = 0
rankToIndex Three = 1
rankToIndex Four = 2
rankToIndex Five = 3
rankToIndex Six = 4
rankToIndex Seven = 5
rankToIndex Eight = 6
rankToIndex Nine = 7
rankToIndex Ten = 8
rankToIndex Jack = 9
rankToIndex Queen = 10
rankToIndex King = 11
rankToIndex Ace = 12

suitFromIndex :: Int -> Suit
suitFromIndex 0 = Clubs
suitFromIndex 1 = Diamonds
suitFromIndex 2 = Hearts
suitFromIndex _ = Spades

suitToIndex :: Suit -> Int
suitToIndex Clubs = 0
suitToIndex Diamonds = 1
suitToIndex Hearts = 2
suitToIndex Spades = 3

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // standard // deck
-- ═══════════════════════════════════════════════════════════════════════════════

-- | All 52 cards ordered by rank, then suit (matches DeckPosition encoding)
standardDeck :: Array Card
standardDeck = do
  r <- allRanks
  s <- allSuits
  pure { rank: r, suit: s }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // hands
-- ═══════════════════════════════════════════════════════════════════════════════

type Hand = Array Card

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // poker // hands
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Poker hand rankings (lowest to highest)
data PokerHand
  = HighCard Rank
  | OnePair Rank
  | TwoPair Rank Rank       -- High pair, low pair
  | ThreeOfAKind Rank
  | Straight Rank           -- High card
  | Flush Suit
  | FullHouse Rank Rank     -- Triplet, pair
  | FourOfAKind Rank
  | StraightFlush Rank Suit
  | RoyalFlush Suit

derive instance eqPokerHand :: Eq PokerHand

instance showPokerHand :: Show PokerHand where
  show (HighCard r) = "HighCard(" <> show r <> ")"
  show (OnePair r) = "OnePair(" <> show r <> ")"
  show (TwoPair h l) = "TwoPair(" <> show h <> ", " <> show l <> ")"
  show (ThreeOfAKind r) = "ThreeOfAKind(" <> show r <> ")"
  show (Straight r) = "Straight(" <> show r <> ")"
  show (Flush s) = "Flush(" <> show s <> ")"
  show (FullHouse t p) = "FullHouse(" <> show t <> ", " <> show p <> ")"
  show (FourOfAKind r) = "FourOfAKind(" <> show r <> ")"
  show (StraightFlush r s) = "StraightFlush(" <> show r <> ", " <> show s <> ")"
  show (RoyalFlush s) = "RoyalFlush(" <> show s <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // blackjack
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Blackjack hand value: Hard (no usable ace), Soft (ace as 11), Bust (>21)
data BlackjackValue = Hard Int | Soft Int | Bust

derive instance eqBlackjackValue :: Eq BlackjackValue

instance showBlackjackValue :: Show BlackjackValue where
  show (Hard n) = "Hard(" <> show n <> ")"
  show (Soft n) = "Soft(" <> show n <> ")"
  show Bust = "Bust"

-- | Calculate blackjack value (2-10 face, J/Q/K=10, A=1 or 11)
blackjackValue :: Array Card -> BlackjackValue
blackjackValue cards =
  let
    values = map (\c -> blackjackRankValue c.rank) cards
    baseTotal = sumArray values
    aceCount = countAces cards
  in
    findBestTotal baseTotal aceCount

-- | Blackjack rank value (Ace=1 base, upgraded by hand calculator)
blackjackRankValue :: Rank -> Int
blackjackRankValue Two = 2
blackjackRankValue Three = 3
blackjackRankValue Four = 4
blackjackRankValue Five = 5
blackjackRankValue Six = 6
blackjackRankValue Seven = 7
blackjackRankValue Eight = 8
blackjackRankValue Nine = 9
blackjackRankValue Ten = 10
blackjackRankValue Jack = 10
blackjackRankValue Queen = 10
blackjackRankValue King = 10
blackjackRankValue Ace = 1

countAces :: Array Card -> Int
countAces cards = countMatching (\c -> isAce c.rank) cards

countMatching :: forall a. (a -> Boolean) -> Array a -> Int
countMatching pred arr = foldl (\acc x -> if pred x then acc + 1 else acc) 0 arr

sumArray :: Array Int -> Int
sumArray = foldl (+) 0

findBestTotal :: Int -> Int -> BlackjackValue
findBestTotal baseTotal aces
  | aces > 0 && baseTotal + 10 <= 21 = Soft (baseTotal + 10)
  | baseTotal <= 21 = Hard baseTotal
  | otherwise = Bust
