-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // dimension // virtual
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Virtual — Types for virtual scroll and windowing implementations.
-- |
-- | **WHY VIRTUAL?**
-- | Virtual scrolling renders only visible items in long lists, enabling
-- | performant handling of thousands of items. This module provides pure
-- | PureScript types for virtual scroll calculations, eliminating JavaScript
-- | FFI for windowing logic.
-- |
-- | **Key Concepts:**
-- | - **VirtualScrollState**: Current scroll position and visible range
-- | - **ItemRange**: Which items are currently visible
-- | - **Overscan**: Extra items rendered above/below for smooth scrolling
-- |
-- | **Use Cases:**
-- | - Infinite scroll lists
-- | - Data tables with thousands of rows
-- | - File explorers
-- | - Chat message histories
-- | - Timeline views
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Dimension.Device (Pixel)
-- | - Hydrogen.Schema.Navigation.Index (Index, Count)
-- |
-- | ## Dependents
-- | - Component.VirtualList
-- | - Component.DataTable
-- | - Hook.UseVirtualScroll

module Hydrogen.Schema.Dimension.Virtual
  ( -- * Scroll State
    VirtualScrollState(VirtualScrollState)
  , virtualScrollState
  , virtualScrollStateFromRecord
  
  -- * State Accessors
  , scrollOffset
  , containerHeight
  , totalHeight
  , visibleRange
  , overscan
  
  -- * Item Range
  , ItemRange(ItemRange)
  , itemRange
  , rangeStart
  , rangeEnd
  , rangeCount
  , inRange
  
  -- * Item Measurement
  , ItemSize(FixedSize, VariableSize, EstimatedSize)
  , fixedItemSize
  , variableItemSize
  , estimatedItemSize
  , getItemSize
  
  -- * Scroll Direction
  , ScrollDirection(ScrollUp, ScrollDown, ScrollNone)
  , detectScrollDirection
  
  -- * Calculations
  , calculateVisibleRange
  , calculateTotalHeight
  , calculateItemOffset
  , calculateScrollProgress
  
  -- * Operations
  , scrollToIndex
  , scrollToTop
  , scrollToBottom
  , updateScrollOffset
  
  -- * Predicates
  , isAtTop
  , isAtBottom
  , isItemVisible
  , needsUpdate
  
  -- * Configuration
  , VirtualScrollConfig
  , virtualScrollConfig
  , defaultVirtualScrollConfig
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Int (toNumber, floor)
import Hydrogen.Schema.Dimension.Device (Pixel(Pixel), unwrapPixel)
import Hydrogen.Schema.Navigation.Index (Index(Index), Count, unwrapIndex, unwrapCount)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // item range
-- ═════════════════════════════════════════════════════════════════════════════

-- | ItemRange represents a contiguous range of item indices.
-- |
-- | - start: First visible item index (inclusive)
-- | - end: Last visible item index (exclusive)
data ItemRange = ItemRange
  { start :: Index
  , end :: Index
  }

derive instance eqItemRange :: Eq ItemRange
derive instance ordItemRange :: Ord ItemRange

instance showItemRange :: Show ItemRange where
  show (ItemRange r) = 
    "ItemRange(" <> show (unwrapIndex r.start) <> 
    ".." <> show (unwrapIndex r.end) <> ")"

-- | Create an ItemRange.
itemRange :: Index -> Index -> ItemRange
itemRange s e = ItemRange { start: s, end: e }

-- | Get range start index.
rangeStart :: ItemRange -> Index
rangeStart (ItemRange r) = r.start

-- | Get range end index.
rangeEnd :: ItemRange -> Index
rangeEnd (ItemRange r) = r.end

-- | Get number of items in range.
rangeCount :: ItemRange -> Int
rangeCount (ItemRange r) = unwrapIndex r.end - unwrapIndex r.start

-- | Check if an index is within the range.
inRange :: Index -> ItemRange -> Boolean
inRange idx (ItemRange r) =
  unwrapIndex idx >= unwrapIndex r.start && 
  unwrapIndex idx < unwrapIndex r.end

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // item size type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Item size specification for virtual scroll calculations.
-- |
-- | - FixedSize: All items have the same height (fastest)
-- | - VariableSize: Function to get height for each item
-- | - EstimatedSize: Average height with measurement cache
data ItemSize
  = FixedSize Pixel
    -- ^ All items have uniform height
  | VariableSize (Int -> Pixel)
    -- ^ Function returning height for item at index
  | EstimatedSize Pixel
    -- ^ Estimated average height (refined during scroll)

instance eqItemSize :: Eq ItemSize where
  eq (FixedSize a) (FixedSize b) = a == b
  eq (EstimatedSize a) (EstimatedSize b) = a == b
  eq _ _ = false

instance showItemSize :: Show ItemSize where
  show (FixedSize p) = "FixedSize(" <> show p <> ")"
  show (VariableSize _) = "VariableSize(fn)"
  show (EstimatedSize p) = "EstimatedSize(" <> show p <> ")"

-- | Create a fixed item size.
fixedItemSize :: Pixel -> ItemSize
fixedItemSize = FixedSize

-- | Create a variable item size with size function.
variableItemSize :: (Int -> Pixel) -> ItemSize
variableItemSize = VariableSize

-- | Create an estimated item size.
estimatedItemSize :: Pixel -> ItemSize
estimatedItemSize = EstimatedSize

-- | Get the size for a specific item index.
getItemSize :: Int -> ItemSize -> Pixel
getItemSize _ (FixedSize p) = p
getItemSize idx (VariableSize f) = f idx
getItemSize _ (EstimatedSize p) = p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // scroll direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of scroll movement.
data ScrollDirection
  = ScrollUp      -- ^ Scrolling toward top (offset decreasing)
  | ScrollDown    -- ^ Scrolling toward bottom (offset increasing)
  | ScrollNone    -- ^ No scroll change

derive instance eqScrollDirection :: Eq ScrollDirection
derive instance ordScrollDirection :: Ord ScrollDirection

instance showScrollDirection :: Show ScrollDirection where
  show ScrollUp = "up"
  show ScrollDown = "down"
  show ScrollNone = "none"

-- | Detect scroll direction from offset change.
detectScrollDirection :: Pixel -> Pixel -> ScrollDirection
detectScrollDirection oldOffset newOffset
  | unwrapPixel newOffset > unwrapPixel oldOffset = ScrollDown
  | unwrapPixel newOffset < unwrapPixel oldOffset = ScrollUp
  | otherwise = ScrollNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // virtual scroll state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete state for a virtual scrolling container.
-- |
-- | This captures everything needed to render the visible window.
data VirtualScrollState = VirtualScrollState
  { scrollOffset :: Pixel
    -- ^ Current scroll position from top
  , containerHeight :: Pixel
    -- ^ Visible container height
  , totalHeight :: Pixel
    -- ^ Total scrollable height
  , visibleRange :: ItemRange
    -- ^ Currently visible item indices
  , overscan :: Int
    -- ^ Extra items rendered above/below
  , itemCount :: Count
    -- ^ Total number of items
  , itemSize :: ItemSize
    -- ^ Item size specification
  }

derive instance eqVirtualScrollState :: Eq VirtualScrollState

instance showVirtualScrollState :: Show VirtualScrollState where
  show (VirtualScrollState s) = 
    "VirtualScrollState(offset:" <> show s.scrollOffset <> 
    ", visible:" <> show s.visibleRange <> ")"

-- | Create a VirtualScrollState.
virtualScrollState 
  :: Pixel 
  -> Pixel 
  -> Pixel 
  -> ItemRange 
  -> Int 
  -> Count
  -> ItemSize
  -> VirtualScrollState
virtualScrollState offset container total range os cnt size =
  VirtualScrollState
    { scrollOffset: offset
    , containerHeight: container
    , totalHeight: total
    , visibleRange: range
    , overscan: maxInt 0 os
    , itemCount: cnt
    , itemSize: size
    }

-- | Create from a record.
virtualScrollStateFromRecord
  :: { scrollOffset :: Pixel
     , containerHeight :: Pixel
     , totalHeight :: Pixel
     , visibleRange :: ItemRange
     , overscan :: Int
     , itemCount :: Count
     , itemSize :: ItemSize
     }
  -> VirtualScrollState
virtualScrollStateFromRecord = VirtualScrollState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // state accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current scroll offset.
scrollOffset :: VirtualScrollState -> Pixel
scrollOffset (VirtualScrollState s) = s.scrollOffset

-- | Get container height.
containerHeight :: VirtualScrollState -> Pixel
containerHeight (VirtualScrollState s) = s.containerHeight

-- | Get total scrollable height.
totalHeight :: VirtualScrollState -> Pixel
totalHeight (VirtualScrollState s) = s.totalHeight

-- | Get visible item range.
visibleRange :: VirtualScrollState -> ItemRange
visibleRange (VirtualScrollState s) = s.visibleRange

-- | Get overscan count.
overscan :: VirtualScrollState -> Int
overscan (VirtualScrollState s) = s.overscan

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate which items are visible for given scroll state.
-- |
-- | Includes overscan items above and below the visible area.
calculateVisibleRange 
  :: Pixel        -- ^ Scroll offset
  -> Pixel        -- ^ Container height  
  -> ItemSize     -- ^ Item size spec
  -> Count        -- ^ Total item count
  -> Int          -- ^ Overscan count
  -> ItemRange
calculateVisibleRange offset height itemSz cnt os =
  case itemSz of
    FixedSize itemH ->
      let 
        itemHeight = unwrapPixel itemH
        offsetVal = unwrapPixel offset
        heightVal = unwrapPixel height
        totalItems = unwrapCount cnt
        
        startIdx = maxInt 0 (floor (offsetVal / itemHeight) - os)
        endIdx = minInt totalItems (floor ((offsetVal + heightVal) / itemHeight) + 1 + os)
      in ItemRange { start: Index startIdx, end: Index endIdx }
    
    VariableSize _ ->
      -- For variable sizes, use estimated calculation
      -- Real implementation would use measured heights
      calculateVisibleRange offset height (EstimatedSize (Pixel 50.0)) cnt os
    
    EstimatedSize estH ->
      let
        avgHeight = unwrapPixel estH
        offsetVal = unwrapPixel offset
        heightVal = unwrapPixel height
        totalItems = unwrapCount cnt
        
        startIdx = maxInt 0 (floor (offsetVal / avgHeight) - os)
        endIdx = minInt totalItems (floor ((offsetVal + heightVal) / avgHeight) + 1 + os)
      in ItemRange { start: Index startIdx, end: Index endIdx }

-- | Calculate total scrollable height.
calculateTotalHeight :: ItemSize -> Count -> Pixel
calculateTotalHeight itemSz cnt =
  case itemSz of
    FixedSize itemH -> 
      Pixel (unwrapPixel itemH * toNumber (unwrapCount cnt))
    
    VariableSize f ->
      -- Sum all item heights (expensive for large lists)
      Pixel (sumHeights f (unwrapCount cnt) 0 0.0)
    
    EstimatedSize estH ->
      Pixel (unwrapPixel estH * toNumber (unwrapCount cnt))

-- | Calculate pixel offset for an item.
calculateItemOffset :: Int -> ItemSize -> Pixel
calculateItemOffset idx itemSz =
  case itemSz of
    FixedSize itemH -> 
      Pixel (unwrapPixel itemH * toNumber idx)
    
    VariableSize f ->
      -- Sum heights of items before this one
      Pixel (sumHeights f idx 0 0.0)
    
    EstimatedSize estH ->
      Pixel (unwrapPixel estH * toNumber idx)

-- | Calculate scroll progress (0.0 to 1.0).
calculateScrollProgress :: VirtualScrollState -> Number
calculateScrollProgress (VirtualScrollState s) =
  let 
    maxScroll = unwrapPixel s.totalHeight - unwrapPixel s.containerHeight
  in if maxScroll <= 0.0 
    then 0.0 
    else clamp01 (unwrapPixel s.scrollOffset / maxScroll)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create scroll state to show a specific item.
scrollToIndex :: Int -> VirtualScrollState -> VirtualScrollState
scrollToIndex idx (VirtualScrollState s) =
  let 
    offset = calculateItemOffset idx s.itemSize
    newRange = calculateVisibleRange offset s.containerHeight s.itemSize s.itemCount s.overscan
  in VirtualScrollState s 
    { scrollOffset = offset
    , visibleRange = newRange
    }

-- | Scroll to top.
scrollToTop :: VirtualScrollState -> VirtualScrollState
scrollToTop = scrollToIndex 0

-- | Scroll to bottom.
scrollToBottom :: VirtualScrollState -> VirtualScrollState
scrollToBottom (VirtualScrollState s) =
  scrollToIndex (unwrapCount s.itemCount - 1) (VirtualScrollState s)

-- | Update scroll offset and recalculate visible range.
updateScrollOffset :: Pixel -> VirtualScrollState -> VirtualScrollState
updateScrollOffset newOffset (VirtualScrollState s) =
  let 
    clampedOffset = clampPixel (Pixel 0.0) (Pixel (unwrapPixel s.totalHeight - unwrapPixel s.containerHeight)) newOffset
    newRange = calculateVisibleRange clampedOffset s.containerHeight s.itemSize s.itemCount s.overscan
  in VirtualScrollState s
    { scrollOffset = clampedOffset
    , visibleRange = newRange
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is scroll at the top?
isAtTop :: VirtualScrollState -> Boolean
isAtTop (VirtualScrollState s) = unwrapPixel s.scrollOffset <= 0.0

-- | Is scroll at the bottom?
isAtBottom :: VirtualScrollState -> Boolean
isAtBottom (VirtualScrollState s) =
  let maxScroll = unwrapPixel s.totalHeight - unwrapPixel s.containerHeight
  in unwrapPixel s.scrollOffset >= maxScroll

-- | Is a specific item currently visible?
isItemVisible :: Int -> VirtualScrollState -> Boolean
isItemVisible idx state = inRange (Index idx) (visibleRange state)

-- | Does the visible range need to be recalculated?
-- |
-- | Returns true if scroll has moved outside the overscan buffer.
needsUpdate :: Pixel -> VirtualScrollState -> Boolean
needsUpdate newOffset (VirtualScrollState s) =
  let
    currentStart = unwrapIndex (rangeStart s.visibleRange)
    currentEnd = unwrapIndex (rangeEnd s.visibleRange)
    newRange = calculateVisibleRange newOffset s.containerHeight s.itemSize s.itemCount 0
    newStart = unwrapIndex (rangeStart newRange)
    newEnd = unwrapIndex (rangeEnd newRange)
  in newStart < currentStart || newEnd > currentEnd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for virtual scroll behavior.
type VirtualScrollConfig =
  { itemSize :: ItemSize
  , overscan :: Int
  , scrollThreshold :: Pixel
  , enableSmooth :: Boolean
  }

-- | Create a virtual scroll configuration.
virtualScrollConfig 
  :: ItemSize 
  -> Int 
  -> Pixel 
  -> Boolean 
  -> VirtualScrollConfig
virtualScrollConfig size os thresh smooth =
  { itemSize: size
  , overscan: maxInt 0 os
  , scrollThreshold: thresh
  , enableSmooth: smooth
  }

-- | Default configuration: 50px items, 3 overscan, 100px threshold.
defaultVirtualScrollConfig :: VirtualScrollConfig
defaultVirtualScrollConfig =
  { itemSize: FixedSize (Pixel 50.0)
  , overscan: 3
  , scrollThreshold: Pixel 100.0
  , enableSmooth: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum heights for variable-sized items.
sumHeights :: (Int -> Pixel) -> Int -> Int -> Number -> Number
sumHeights f total current acc
  | current >= total = acc
  | otherwise = sumHeights f total (current + 1) (acc + unwrapPixel (f current))

-- | Maximum of two integers.
maxInt :: Int -> Int -> Int
maxInt a b
  | a >= b = a
  | otherwise = b

-- | Minimum of two integers.
minInt :: Int -> Int -> Int
minInt a b
  | a <= b = a
  | otherwise = b

-- | Clamp number to 0.0-1.0.
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Clamp Pixel to range.
clampPixel :: Pixel -> Pixel -> Pixel -> Pixel
clampPixel (Pixel minV) (Pixel maxV) (Pixel v)
  | v < minV = Pixel minV
  | v > maxV = Pixel maxV
  | otherwise = Pixel v
