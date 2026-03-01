-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // schema // game
--                                                                      // slots
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Complete slot machine vocabulary for casino-style slot games.
-- | Reels are pure data. Symbols enumerable. Paylines deterministic.
-- | All bounds enforced: WindowSize 1-5, ReelCount 3-7, RTP 0.85-0.99

module Hydrogen.Schema.Game.Slots
  ( -- * Symbols
    SlotSymbol
      ( Cherry, Lemon, Orange, Plum, Bell
      , Bar, DoubleBar, TripleBar
      , Seven, SevenRed, SevenBlue
      , Diamond, Wild, Scatter, Bonus
      )
  , allSymbols, symbolValue, isWild, isScatter, isBonus, formatSymbol
  -- * Symbol Matching
  , symbolMatches
  -- * Reel Configuration
  , ReelStrip
  -- * Window Size (1-5 visible rows)
  , WindowSize(WindowSize)
  , windowSize, unwrapWindowSize
  -- * Reel Count (3-7 reels)
  , ReelCount(ReelCount)
  , reelCount, unwrapReelCount
  -- * Payline Definitions
  , PaylinePosition
  , Payline
  , PaylinePattern(Horizontal, VShape, InvertedV, Zigzag, Custom)
  , standardPaylines, patternToPayline
  -- * Slot Configuration
  , SlotConfig
  , slotConfig
  -- * Win Detection
  , WinLine
  , checkPayline, findWins
  -- * Spin Results
  , SpinResult
  , calculatePayout
  -- * Volatility
  , Volatility(Low, Medium, High, VeryHigh)
  , volatilityMultiplier
  -- * RTP Calculation
  , theoreticalRTP
  ) where

import Prelude
  ( class Eq, class Ord, class Show
  , show, compare, otherwise, map, negate
  , (==), (+), (-), (*), (/), (>), (<), (>=), (<=), (&&), (||), (<>)
  )
import Prim (Boolean, Int, Number, Array, String)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (length, index, filter, foldl, concat, range, zipWith)
import Data.Int as Data.Int
import Hydrogen.Schema.Bounded (clampInt, clampNumber)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // slot // symbol
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Standard slot machine symbols from classic to modern
-- | Ordered by traditional value (lowest to highest)
data SlotSymbol
  = Cherry          -- ^ Classic fruit: lowest value
  | Lemon           -- ^ Classic fruit
  | Orange          -- ^ Classic fruit
  | Plum            -- ^ Classic fruit
  | Bell            -- ^ Liberty bell: mid value
  | Bar             -- ^ Single bar
  | DoubleBar       -- ^ Double bar
  | TripleBar       -- ^ Triple bar
  | Seven           -- ^ Lucky seven: high value
  | SevenRed        -- ^ Red seven variant
  | SevenBlue       -- ^ Blue seven variant
  | Diamond         -- ^ Premium symbol
  | Wild            -- ^ Substitutes for any non-special symbol
  | Scatter         -- ^ Triggers bonus regardless of payline position
  | Bonus           -- ^ Triggers bonus game feature

derive instance eqSlotSymbol :: Eq SlotSymbol
derive instance ordSlotSymbol :: Ord SlotSymbol

instance showSlotSymbol :: Show SlotSymbol where
  show Cherry = "Cherry"
  show Lemon = "Lemon"
  show Orange = "Orange"
  show Plum = "Plum"
  show Bell = "Bell"
  show Bar = "Bar"
  show DoubleBar = "DoubleBar"
  show TripleBar = "TripleBar"
  show Seven = "Seven"
  show SevenRed = "SevenRed"
  show SevenBlue = "SevenBlue"
  show Diamond = "Diamond"
  show Wild = "Wild"
  show Scatter = "Scatter"
  show Bonus = "Bonus"

-- | All symbols in value order (excluding special symbols)
allSymbols :: Array SlotSymbol
allSymbols =
  [ Cherry, Lemon, Orange, Plum, Bell
  , Bar, DoubleBar, TripleBar
  , Seven, SevenRed, SevenBlue
  , Diamond, Wild, Scatter, Bonus
  ]

-- | Base payout value for matching symbols (credits per symbol)
-- | Used as multiplier: 3 cherries = symbolValue Cherry * 3
symbolValue :: SlotSymbol -> Int
symbolValue Cherry = 2
symbolValue Lemon = 3
symbolValue Orange = 4
symbolValue Plum = 5
symbolValue Bell = 10
symbolValue Bar = 15
symbolValue DoubleBar = 25
symbolValue TripleBar = 40
symbolValue Seven = 50
symbolValue SevenRed = 75
symbolValue SevenBlue = 100
symbolValue Diamond = 150
symbolValue Wild = 0       -- Wild has no standalone value
symbolValue Scatter = 5    -- Scatter pays any position
symbolValue Bonus = 0      -- Bonus triggers feature, no direct pay

-- | Wild symbols substitute for regular symbols
isWild :: SlotSymbol -> Boolean
isWild Wild = true
isWild _ = false

-- | Scatter symbols pay regardless of payline
isScatter :: SlotSymbol -> Boolean
isScatter Scatter = true
isScatter _ = false

-- | Bonus symbols trigger bonus games
isBonus :: SlotSymbol -> Boolean
isBonus Bonus = true
isBonus _ = false

-- | Display symbol with Unicode representation
formatSymbol :: SlotSymbol -> String
formatSymbol Cherry = "🍒"
formatSymbol Lemon = "🍋"
formatSymbol Orange = "🍊"
formatSymbol Plum = "🍇"
formatSymbol Bell = "🔔"
formatSymbol Bar = "▬"
formatSymbol DoubleBar = "▬▬"
formatSymbol TripleBar = "▬▬▬"
formatSymbol Seven = "7️"
formatSymbol SevenRed = "7♦"
formatSymbol SevenBlue = "7♠"
formatSymbol Diamond = "💎"
formatSymbol Wild = "★"
formatSymbol Scatter = "✦"
formatSymbol Bonus = "🎰"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // symbol // matching
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if two symbols match for win purposes
-- | Wild matches any non-special symbol
-- | Scatter and Bonus only match themselves
symbolMatches :: SlotSymbol -> SlotSymbol -> Boolean
symbolMatches s1 s2
  | s1 == s2 = true
  | isScatter s1 || isScatter s2 = false  -- Scatters don't substitute
  | isBonus s1 || isBonus s2 = false      -- Bonuses don't substitute
  | isWild s1 || isWild s2 = true         -- Wild matches anything else
  | otherwise = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // reel // strip
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A reel strip is the complete sequence of symbols on one reel
-- | The array wraps: after last symbol comes first
type ReelStrip = Array SlotSymbol

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // window // size
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Number of visible symbol positions per reel
-- | Bounded 1-5: 1 (single line), 3 (classic), 5 (video slots)
newtype WindowSize = WindowSize Int

derive instance eqWindowSize :: Eq WindowSize
derive instance ordWindowSize :: Ord WindowSize

instance showWindowSize :: Show WindowSize where
  show (WindowSize n) = "WindowSize " <> show n

-- | Smart constructor: clamps to valid range 1-5
windowSize :: Int -> WindowSize
windowSize n = WindowSize (clampInt 1 5 n)

-- | Extract raw value
unwrapWindowSize :: WindowSize -> Int
unwrapWindowSize (WindowSize n) = n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // reel // count
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Number of reels in the slot machine
-- | Bounded 3-7: 3 (classic), 5 (standard video), 7 (megaways)
newtype ReelCount = ReelCount Int

derive instance eqReelCount :: Eq ReelCount
derive instance ordReelCount :: Ord ReelCount

instance showReelCount :: Show ReelCount where
  show (ReelCount n) = "ReelCount " <> show n

-- | Smart constructor: clamps to valid range 3-7
reelCount :: Int -> ReelCount
reelCount n = ReelCount (clampInt 3 7 n)

-- | Extract raw value
unwrapReelCount :: ReelCount -> Int
unwrapReelCount (ReelCount n) = n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // payline
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Position on the visible grid: which reel and which row
type PaylinePosition = { reel :: Int, row :: Int }

-- | A payline is a sequence of positions to check for matches
-- | Positions must cover each reel exactly once, left to right
type Payline = Array PaylinePosition

-- | Common payline patterns used in slot machines
data PaylinePattern
  = Horizontal Int              -- ^ Straight line at row index (0-indexed)
  | VShape                      -- ^ V pattern: top-middle-bottom-middle-top
  | InvertedV                   -- ^ Inverted V: bottom-middle-top-middle-bottom
  | Zigzag                      -- ^ Alternating top-bottom
  | Custom (Array PaylinePosition)  -- ^ Arbitrary positions

derive instance eqPaylinePattern :: Eq PaylinePattern

instance showPaylinePattern :: Show PaylinePattern where
  show (Horizontal row) = "Horizontal " <> show row
  show VShape = "VShape"
  show InvertedV = "InvertedV"
  show Zigzag = "Zigzag"
  show (Custom positions) = "Custom " <> show (length positions) <> " positions"

-- | Convert a pattern to concrete payline positions
-- | Requires reel count and window size for bounds
patternToPayline :: ReelCount -> WindowSize -> PaylinePattern -> Payline
patternToPayline (ReelCount reels) (WindowSize rows) pattern =
  case pattern of
    Horizontal row ->
      let clampedRow = clampInt 0 (rows - 1) row
      in map (\r -> { reel: r, row: clampedRow }) (range 0 (reels - 1))

    VShape ->
      generateVShape reels rows

    InvertedV ->
      generateInvertedV reels rows

    Zigzag ->
      generateZigzag reels rows

    Custom positions ->
      -- Clamp all positions to valid bounds
      map (clampPosition reels rows) positions

-- | Helper: clamp a position to valid grid bounds
clampPosition :: Int -> Int -> PaylinePosition -> PaylinePosition
clampPosition reels rows pos =
  { reel: clampInt 0 (reels - 1) pos.reel
  , row: clampInt 0 (rows - 1) pos.row
  }

-- | Generate V-shape pattern for given dimensions
generateVShape :: Int -> Int -> Payline
generateVShape reels rows =
  let
    midReel = reels / 2
    topRow = 0
    bottomRow = rows - 1
  in
    map (\r -> { reel: r, row: vShapeRow r midReel topRow bottomRow }) (range 0 (reels - 1))

-- | Calculate row for V-shape at given reel
vShapeRow :: Int -> Int -> Int -> Int -> Int
vShapeRow reel midReel topRow bottomRow
  | reel <= midReel = topRow + reel
  | otherwise = bottomRow - (reel - midReel)

-- | Generate inverted V-shape pattern
generateInvertedV :: Int -> Int -> Payline
generateInvertedV reels rows =
  let
    midReel = reels / 2
    topRow = 0
    bottomRow = rows - 1
  in
    map (\r -> { reel: r, row: invertedVRow r midReel topRow bottomRow }) (range 0 (reels - 1))

-- | Calculate row for inverted V-shape at given reel
invertedVRow :: Int -> Int -> Int -> Int -> Int
invertedVRow reel midReel topRow bottomRow
  | reel <= midReel = bottomRow - reel
  | otherwise = topRow + (reel - midReel)

-- | Generate zigzag pattern
generateZigzag :: Int -> Int -> Payline
generateZigzag reels rows =
  let
    topRow = 0
    bottomRow = rows - 1
  in
    map (\r -> { reel: r, row: zigzagRow r topRow bottomRow }) (range 0 (reels - 1))

-- | Calculate row for zigzag at given reel (alternates top/bottom)
zigzagRow :: Int -> Int -> Int -> Int
zigzagRow reel topRow bottomRow
  | modTwo reel == 0 = topRow
  | otherwise = bottomRow

-- | Simple mod 2 for zigzag calculation
modTwo :: Int -> Int
modTwo n
  | n < 0 = modTwo (negate n)
  | n < 2 = n
  | otherwise = modTwo (n - 2)

-- | Generate standard paylines for a given configuration
-- | Returns common patterns: horizontal lines, V shapes, zigzags
standardPaylines :: ReelCount -> WindowSize -> Array Payline
standardPaylines rc@(ReelCount reels) ws@(WindowSize rows) =
  let
    -- All horizontal lines
    horizontals = map (\row -> patternToPayline rc ws (Horizontal row)) (range 0 (rows - 1))

    -- V patterns (only if enough rows)
    vPatterns =
      if rows >= 3
        then [ patternToPayline rc ws VShape, patternToPayline rc ws InvertedV ]
        else []

    -- Zigzag (only if multiple rows)
    zigzags =
      if rows >= 2
        then [ patternToPayline rc ws Zigzag ]
        else []
  in
    concat [ horizontals, vPatterns, zigzags ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // slot // config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete slot machine configuration
type SlotConfig =
  { reelCount :: ReelCount
  , windowSize :: WindowSize
  , reels :: Array ReelStrip      -- One strip per reel
  , paylines :: Array Payline
  , rtp :: Number                 -- Return to player (0.85-0.99)
  }

-- | Smart constructor for SlotConfig with validation
-- | Ensures RTP is bounded and reel count matches strips
slotConfig
  :: ReelCount
  -> WindowSize
  -> Array ReelStrip
  -> Array Payline
  -> Number
  -> SlotConfig
slotConfig rc ws strips plines targetRTP =
  { reelCount: rc
  , windowSize: ws
  , reels: strips
  , paylines: plines
  , rtp: clampNumber 0.85 0.99 targetRTP
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // win // line
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A winning combination on a payline
type WinLine =
  { payline :: Int                -- Index of the winning payline
  , symbols :: Array SlotSymbol   -- Matched symbols
  , matchCount :: Int             -- How many symbols matched
  , payout :: Int                 -- Credits won
  }

-- | Check a single payline for wins against visible grid
-- | Returns Just WinLine if matching symbols found, Nothing otherwise
checkPayline :: Array (Array SlotSymbol) -> Int -> Payline -> Maybe WinLine
checkPayline visible paylineIndex positions =
  let
    -- Extract symbols at payline positions
    symbols = extractSymbols visible positions

    -- Count matching symbols from left
    matchResult = countMatches symbols
  in
    if matchResult.count >= 3
      then Just
        { payline: paylineIndex
        , symbols: matchResult.matched
        , matchCount: matchResult.count
        , payout: calculateLinePayout matchResult.baseSymbol matchResult.count
        }
      else Nothing

-- | Extract symbols from grid at given positions
extractSymbols :: Array (Array SlotSymbol) -> Payline -> Array SlotSymbol
extractSymbols visible positions =
  foldl (\acc pos -> appendSymbol acc visible pos) [] positions

-- | Append symbol at position to array
appendSymbol :: Array SlotSymbol -> Array (Array SlotSymbol) -> PaylinePosition -> Array SlotSymbol
appendSymbol acc visible pos =
  case index visible pos.reel of
    Nothing -> acc
    Just column ->
      case index column pos.row of
        Nothing -> acc
        Just symbol -> appendToArray acc symbol

-- | Append element to array (helper)
appendToArray :: forall a. Array a -> a -> Array a
appendToArray arr x = concat [ arr, [ x ] ]

-- | Count matching symbols from left, handling wilds
-- | Returns the count, matched symbols, and base symbol for payout
countMatches :: Array SlotSymbol -> { count :: Int, matched :: Array SlotSymbol, baseSymbol :: SlotSymbol }
countMatches symbols =
  case index symbols 0 of
    Nothing -> { count: 0, matched: [], baseSymbol: Cherry }
    Just first ->
      let
        result = foldl (matchFolder first) { count: 0, matched: [], continuing: true } symbols
      in
        { count: result.count
        , matched: result.matched
        , baseSymbol: findBaseSymbol first result.matched
        }

-- | Folder function for counting matches
matchFolder
  :: SlotSymbol
  -> { count :: Int, matched :: Array SlotSymbol, continuing :: Boolean }
  -> SlotSymbol
  -> { count :: Int, matched :: Array SlotSymbol, continuing :: Boolean }
matchFolder baseSymbol acc current
  | acc.continuing && symbolMatches baseSymbol current =
      { count: acc.count + 1
      , matched: appendToArray acc.matched current
      , continuing: true
      }
  | otherwise =
      { count: acc.count
      , matched: acc.matched
      , continuing: false
      }

-- | Find the base symbol for payout (first non-wild)
findBaseSymbol :: SlotSymbol -> Array SlotSymbol -> SlotSymbol
findBaseSymbol defaultSym symbols =
  case filter (\s -> isWild s == false) symbols of
    [] -> defaultSym
    nonWilds ->
      case index nonWilds 0 of
        Nothing -> defaultSym
        Just s -> s

-- | Calculate payout for a matching line
-- | Payout = symbolValue * matchCount * matchCountMultiplier
calculateLinePayout :: SlotSymbol -> Int -> Int
calculateLinePayout symbol count =
  symbolValue symbol * count * matchMultiplier count

-- | Multiplier based on match count (3=1x, 4=2x, 5=5x)
matchMultiplier :: Int -> Int
matchMultiplier 3 = 1
matchMultiplier 4 = 2
matchMultiplier 5 = 5
matchMultiplier 6 = 10
matchMultiplier 7 = 25
matchMultiplier _ = 0

-- | Find all wins in a spin result
findWins :: Array (Array SlotSymbol) -> Array Payline -> Array WinLine
findWins visible paylines =
  foldl (\acc indexedPayline -> checkAndAppend acc visible indexedPayline) [] (indexPaylines paylines)

-- | Index paylines for processing
indexPaylines :: Array Payline -> Array { idx :: Int, payline :: Payline }
indexPaylines paylines =
  zipWith (\idx pl -> { idx: idx, payline: pl }) (range 0 (length paylines - 1)) paylines

-- | Check payline and append win if found
checkAndAppend :: Array WinLine -> Array (Array SlotSymbol) -> { idx :: Int, payline :: Payline } -> Array WinLine
checkAndAppend acc visible indexed =
  case checkPayline visible indexed.idx indexed.payline of
    Nothing -> acc
    Just win -> appendToArray acc win

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // spin // result
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete result of a slot spin
type SpinResult =
  { visible :: Array (Array SlotSymbol)   -- What's showing on grid
  , stops :: Array Int                    -- Reel stop positions
  , wins :: Array WinLine                 -- All winning lines
  , totalWin :: Int                       -- Total credits won
  }

-- | Calculate total payout for a spin result
calculatePayout :: SlotConfig -> SpinResult -> Int
calculatePayout _ result =
  foldl (\acc win -> acc + win.payout) 0 result.wins

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // volatility
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Slot machine volatility classification
-- | Affects win frequency vs win size tradeoff
data Volatility
  = Low        -- ^ Frequent small wins
  | Medium     -- ^ Balanced
  | High       -- ^ Rare big wins
  | VeryHigh   -- ^ Very rare huge wins

derive instance eqVolatility :: Eq Volatility
derive instance ordVolatility :: Ord Volatility

instance showVolatility :: Show Volatility where
  show Low = "Low"
  show Medium = "Medium"
  show High = "High"
  show VeryHigh = "VeryHigh"

-- | Multiplier for volatility-adjusted payouts
-- | Higher volatility = higher max multiplier
volatilityMultiplier :: Volatility -> Number
volatilityMultiplier Low = 1.0
volatilityMultiplier Medium = 2.5
volatilityMultiplier High = 5.0
volatilityMultiplier VeryHigh = 10.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // rtp
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate theoretical Return to Player percentage
-- | This is a simplified approximation based on symbol distribution
-- | Real RTP requires full probability analysis of all possible outcomes
theoreticalRTP :: SlotConfig -> Number
theoreticalRTP config =
  let
    -- Base RTP from configuration
    baseRTP = config.rtp

    -- Adjustment based on reel count (more reels = harder to win)
    reelAdjustment = 1.0 - (intToNumber (unwrapReelCount config.reelCount) * 0.01)

    -- Adjustment based on paylines (more paylines = more chances)
    paylineBonus = intToNumber (length config.paylines) * 0.001
  in
    clampNumber 0.85 0.99 (baseRTP * reelAdjustment + paylineBonus)

-- | Convert Int to Number (pure implementation)
intToNumber :: Int -> Number
intToNumber = Data.Int.toNumber


