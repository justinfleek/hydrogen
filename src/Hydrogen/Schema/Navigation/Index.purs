-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // navigation // index
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Index - bounded position within a finite sequence.
-- |
-- | The foundational atom for any sequential navigation: carousels, tabs,
-- | accordions, steppers, playlists, galleries, pagination.
-- |
-- | ## Boundary Behavior
-- |
-- | When navigating past boundaries, two behaviors are possible:
-- |
-- | - **Clamp**: Stop at edges (0 or count-1)
-- | - **Wrap**: Loop around (going past end returns to start)
-- |
-- | The behavior is encoded in the type, making intentions explicit.
-- |
-- | ## Design Philosophy
-- |
-- | An index alone is meaningless — it requires a count (the sequence length).
-- | Together they form an `IndexedPosition` molecule that guarantees:
-- |
-- | - Index is always valid (0 <= index < count)
-- | - Navigation operations maintain validity
-- | - No array bounds exceptions possible
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, Ring)
-- | - Hydrogen.Schema.Bounded (clampInt)
-- |
-- | ## Dependents
-- | - Navigation.Pagination (uses IndexedPosition)
-- | - Component.Carousel (slide position)
-- | - Component.Tabs (active tab)
-- | - Component.Stepper (current step)
-- | - Component.Accordion (expanded panels)

module Hydrogen.Schema.Navigation.Index
  ( -- * Boundary Behavior
    BoundaryBehavior(Clamp, Wrap)
  , isClamp
  , isWrap
  
  -- * Count (Sequence Length)
  , Count(Count)
  , count
  , unwrapCount
  , countBounds
  , isEmpty
  , isSingleton
  
  -- * Index (Position)
  , Index(Index)
  , index
  , indexFromValidated
  , unwrapIndex
  , indexBounds
  , isFirst
  , isLast
  
  -- * Indexed Position (Molecule)
  , IndexedPosition
  , indexedPosition
  , position
  , total
  , behavior
  , atFirst
  , atLast
  , canGoNext
  , canGoPrev
  
  -- * Navigation Operations
  , next
  , prev
  , goTo
  , goToFirst
  , goToLast
  , advance
  , retreat
  
  -- * Computed Properties
  , progressRatio
  , remaining
  , distanceToEnd
  , distanceToStart
  
  -- * Range Operations
  , indexAtPercent
  , isInRange
  , isAtOrAfter
  , isAtOrBefore
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , mod
  , (-)
  , (+)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Int (toNumber, floor)
import Hydrogen.Schema.Bounded (IntBounds, intBounds, clampInt, BoundsBehavior(Clamps)) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // boundary behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | How to handle navigation past sequence boundaries
-- |
-- | - `Clamp`: Stop at edges — cannot go below 0 or above count-1
-- | - `Wrap`: Loop around — going past end returns to start, and vice versa
data BoundaryBehavior
  = Clamp
  | Wrap

derive instance eqBoundaryBehavior :: Eq BoundaryBehavior
derive instance ordBoundaryBehavior :: Ord BoundaryBehavior

instance showBoundaryBehavior :: Show BoundaryBehavior where
  show Clamp = "clamp"
  show Wrap = "wrap"

-- | Is behavior clamping?
isClamp :: BoundaryBehavior -> Boolean
isClamp Clamp = true
isClamp Wrap = false

-- | Is behavior wrapping?
isWrap :: BoundaryBehavior -> Boolean
isWrap Wrap = true
isWrap Clamp = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of items in a sequence [0, 10000]
-- |
-- | Upper bound prevents unbounded sequences that could cause performance issues.
-- | For larger datasets, use pagination or virtualization.
newtype Count = Count Int

derive instance eqCount :: Eq Count
derive instance ordCount :: Ord Count

instance showCount :: Show Count where
  show (Count n) = show n <> " items"

-- | Create a count value (clamps to [0, 10000])
count :: Int -> Count
count n = Count (Bounded.clampInt 0 10000 n)

-- | Extract raw count value
unwrapCount :: Count -> Int
unwrapCount (Count n) = n

-- | Bounds for Count
countBounds :: Bounded.IntBounds
countBounds = Bounded.intBounds 0 10000 Bounded.Clamps "count" "Number of items in sequence (0-10000)"

-- | Is the sequence empty?
isEmpty :: Count -> Boolean
isEmpty (Count n) = n == 0

-- | Does the sequence have exactly one item?
isSingleton :: Count -> Boolean
isSingleton (Count n) = n == 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero-based index into a sequence [0, 9999]
-- |
-- | An index alone is not meaningful — it must be paired with a Count
-- | to form an IndexedPosition that guarantees validity.
newtype Index = Index Int

derive instance eqIndex :: Eq Index
derive instance ordIndex :: Ord Index

instance showIndex :: Show Index where
  show (Index n) = "index " <> show n

-- | Create an index (clamps to [0, 9999])
-- |
-- | Note: This does not guarantee the index is valid for a given sequence.
-- | Use `indexedPosition` to create a validated position.
index :: Int -> Index
index n = Index (Bounded.clampInt 0 9999 n)

-- | Create an index from a pre-validated value.
-- |
-- | Use when the value has already been validated (e.g., from IndexedPosition
-- | operations that maintain invariants). Prefer `index` for user input.
-- |
-- | ## Why Not "unsafe"
-- |
-- | The name "unsafeX" implies undefined behavior or crashes. This function
-- | doesn't crash — it just skips redundant validation. The name "fromValidated"
-- | makes the contract clear: caller guarantees validity.
indexFromValidated :: Int -> Index
indexFromValidated = Index

-- | Extract raw index value
unwrapIndex :: Index -> Int
unwrapIndex (Index n) = n

-- | Bounds for Index
indexBounds :: Bounded.IntBounds
indexBounds = Bounded.intBounds 0 9999 Bounded.Clamps "index" "Zero-based position in sequence (0-9999)"

-- | Is this index 0?
isFirst :: Index -> Boolean
isFirst (Index n) = n == 0

-- | Is this index count-1?
-- |
-- | Requires the count to determine.
isLast :: Index -> Count -> Boolean
isLast (Index idx) (Count cnt) = cnt > 0 && idx == cnt - 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // indexed position
-- ═════════════════════════════════════════════════════════════════════════════

-- | A valid position within a sequence
-- |
-- | This molecule guarantees:
-- | - 0 <= index < count (when count > 0)
-- | - index == 0 (when count == 0, empty sequence)
-- | - Navigation operations maintain these invariants
type IndexedPosition =
  { index :: Index
  , count :: Count
  , behavior :: BoundaryBehavior
  }

-- | Create an indexed position, validating the index against the count
-- |
-- | If index >= count, it is clamped or wrapped based on behavior.
-- | If count == 0, index is always 0.
indexedPosition :: Int -> Int -> BoundaryBehavior -> IndexedPosition
indexedPosition idx cnt bhv =
  let
    validCount = Bounded.clampInt 0 10000 cnt
    validIndex = 
      if validCount == 0 
        then 0
        else case bhv of
          Clamp -> Bounded.clampInt 0 (validCount - 1) idx
          Wrap -> wrapIndex idx validCount
  in
    { index: Index validIndex
    , count: Count validCount
    , behavior: bhv
    }

-- | Get current index
position :: IndexedPosition -> Int
position ip = unwrapIndex ip.index

-- | Get total count
total :: IndexedPosition -> Int
total ip = unwrapCount ip.count

-- | Get boundary behavior
behavior :: IndexedPosition -> BoundaryBehavior
behavior ip = ip.behavior

-- | Is at first position?
atFirst :: IndexedPosition -> Boolean
atFirst ip = position ip == 0

-- | Is at last position?
atLast :: IndexedPosition -> Boolean
atLast ip = 
  let cnt = total ip
  in cnt > 0 && position ip == cnt - 1

-- | Can navigate to next item?
-- |
-- | Always true for Wrap behavior (unless empty).
-- | For Clamp, only true if not at last position.
canGoNext :: IndexedPosition -> Boolean
canGoNext ip = case ip.behavior of
  Wrap -> total ip > 0
  Clamp -> total ip > 0 && position ip < total ip - 1

-- | Can navigate to previous item?
-- |
-- | Always true for Wrap behavior (unless empty).
-- | For Clamp, only true if not at first position.
canGoPrev :: IndexedPosition -> Boolean
canGoPrev ip = case ip.behavior of
  Wrap -> total ip > 0
  Clamp -> position ip > 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // navigation operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Move to next position
next :: IndexedPosition -> IndexedPosition
next ip = advance 1 ip

-- | Move to previous position
prev :: IndexedPosition -> IndexedPosition
prev ip = retreat 1 ip

-- | Go to specific index
goTo :: Int -> IndexedPosition -> IndexedPosition
goTo targetIdx ip = 
  indexedPosition targetIdx (total ip) ip.behavior

-- | Go to first position
goToFirst :: IndexedPosition -> IndexedPosition
goToFirst ip = goTo 0 ip

-- | Go to last position
goToLast :: IndexedPosition -> IndexedPosition
goToLast ip = goTo (total ip - 1) ip

-- | Advance by n positions (can be negative)
advance :: Int -> IndexedPosition -> IndexedPosition
advance n ip =
  let
    current = position ip
    cnt = total ip
  in
    if cnt == 0 
      then ip
      else indexedPosition (current + n) cnt ip.behavior

-- | Retreat by n positions (same as advance with negative n)
retreat :: Int -> IndexedPosition -> IndexedPosition
retreat n = advance (negate n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress through sequence as ratio (0.0 to 1.0)
-- |
-- | Returns 0.0 for empty sequences.
-- | Returns 1.0 when at last position.
progressRatio :: IndexedPosition -> Number
progressRatio ip =
  let cnt = total ip
  in if cnt <= 1 
    then 0.0
    else toNumber (position ip) / toNumber (cnt - 1)

-- | Number of items remaining after current position
remaining :: IndexedPosition -> Int
remaining ip = 
  let cnt = total ip
      idx = position ip
  in if cnt == 0 then 0 else cnt - idx - 1

-- | Distance to end (same as remaining)
distanceToEnd :: IndexedPosition -> Int
distanceToEnd = remaining

-- | Distance to start (same as current index)
distanceToStart :: IndexedPosition -> Int
distanceToStart = position

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // range operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get index at given percentage through the sequence.
-- |
-- | ```purescript
-- | indexAtPercent 0.0 (indexedPosition 0 10 Clamp)   -- 0
-- | indexAtPercent 0.5 (indexedPosition 0 10 Clamp)   -- 5
-- | indexAtPercent 1.0 (indexedPosition 0 10 Clamp)   -- 9
-- | indexAtPercent 0.33 (indexedPosition 0 100 Clamp) -- 33
-- | ```
-- |
-- | Percentage is clamped to [0.0, 1.0].
-- | Returns 0 for empty sequences.
-- | NaN and Infinity return 0 (safe fallback from Data.Int.floor).
indexAtPercent :: Number -> IndexedPosition -> Int
indexAtPercent percent ip =
  let
    cnt = total ip
    -- Clamp percentage to valid range
    clampedPercent = if percent < 0.0 then 0.0 
                     else if percent > 1.0 then 1.0 
                     else percent
  in
    if cnt <= 0 
      then 0
      else 
        -- Multiply last valid index by percentage
        let lastIdx = cnt - 1
            scaled = toNumber lastIdx * clampedPercent
            -- floor handles NaN/Infinity safely (returns 0)
        in Bounded.clampInt 0 lastIdx (floor scaled)

-- | Is current position within an inclusive range?
-- |
-- | ```purescript
-- | isInRange 2 5 (indexedPosition 3 10 Clamp)  -- true (3 is in [2,5])
-- | isInRange 2 5 (indexedPosition 1 10 Clamp)  -- false (1 is not in [2,5])
-- | isInRange 2 5 (indexedPosition 6 10 Clamp)  -- false (6 is not in [2,5])
-- | ```
isInRange :: Int -> Int -> IndexedPosition -> Boolean
isInRange minIdx maxIdx ip =
  let idx = position ip
  in idx >= minIdx && idx <= maxIdx

-- | Is current position at or after a target index?
-- |
-- | Useful for progress indicators: "have we reached step N yet?"
isAtOrAfter :: Int -> IndexedPosition -> Boolean
isAtOrAfter target ip = position ip >= target

-- | Is current position at or before a target index?
-- |
-- | Useful for guards: "are we still before the dangerous section?"
isAtOrBefore :: Int -> IndexedPosition -> Boolean
isAtOrBefore target ip = position ip <= target

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wrap index to valid range [0, count)
-- |
-- | Handles negative indices correctly:
-- | wrapIndex (-1) 5 = 4
-- | wrapIndex 5 5 = 0
-- | wrapIndex 7 5 = 2
wrapIndex :: Int -> Int -> Int
wrapIndex idx cnt
  | cnt <= 0 = 0
  | otherwise = 
      let m = idx `mod` cnt
      in if m < 0 then m + cnt else m
