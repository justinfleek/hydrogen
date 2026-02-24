-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // virtual-scroll
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Virtual scroll - render only visible items for massive performance
-- |
-- | High-performance virtualized lists supporting 100k+ items at 60fps.
-- | Supports fixed height, variable height (measured), grid mode, and
-- | horizontal scrolling.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Interaction.VirtualScroll as VirtualScroll
-- |
-- | -- Fixed height items (fastest)
-- | VirtualScroll.virtualList
-- |   [ VirtualScroll.itemCount 10000
-- |   , VirtualScroll.itemHeight (VirtualScroll.Fixed 48)
-- |   , VirtualScroll.containerHeight 400
-- |   , VirtualScroll.overscan 5
-- |   , VirtualScroll.onScroll HandleScroll
-- |   ]
-- |   (\index -> HH.div_ [ HH.text $ "Item " <> show index ])
-- |
-- | -- Variable height items (measured)
-- | VirtualScroll.virtualList
-- |   [ VirtualScroll.itemCount 10000
-- |   , VirtualScroll.itemHeight (VirtualScroll.Variable getItemHeight)
-- |   , VirtualScroll.containerHeight 400
-- |   ]
-- |   renderItem
-- |
-- | -- Grid mode
-- | VirtualScroll.virtualGrid
-- |   [ VirtualScroll.rowCount 1000
-- |   , VirtualScroll.columnCount 10
-- |   , VirtualScroll.cellWidth 100
-- |   , VirtualScroll.cellHeight 100
-- |   ]
-- |   (\row col -> renderCell row col)
-- | ```
module Hydrogen.Interaction.VirtualScroll
  ( -- * Components
    virtualList
  , virtualGrid
    -- * Types
  , VirtualScrollState
  , ItemHeight(Fixed, Variable, Dynamic)
  , ScrollDirection(Vertical, Horizontal, Both)
  , VisibleRange
    -- * Props
  , VirtualScrollProps
  , VirtualScrollProp
  , itemCount
  , itemHeight
  , containerHeight
  , containerWidth
  , overscan
  , horizontal
  , onScroll
  , onVisibleRangeChange
  , scrollToIndex
  , className
    -- * Grid Props
  , VirtualGridProps
  , VirtualGridProp
  , rowCount
  , columnCount
  , cellWidth
  , cellHeight
  , stickyRows
  , stickyColumns
  , gridOnScroll
  , gridClassName
    -- * Calculation
  , calculateVisibleRange
  , calculateScrollPosition
  , getEstimatedTotalHeight
  , getEstimatedTotalWidth
    -- * Imperative API (FFI)
  , VirtualScrollRef
  , createVirtualScrollRef
  , scrollTo
  , scrollToItem
  , getScrollOffset
  , measureItem
  ) where

import Prelude

import Data.Array (foldl, range, length)
import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Item height configuration
data ItemHeight
  = Fixed Number           -- ^ All items have same height (fastest)
  | Variable (Int -> Number) -- ^ Function to get height for each index
  | Dynamic                -- ^ Measure items as they render (flexible, slower)

-- | Scroll direction
data ScrollDirection
  = Vertical
  | Horizontal
  | Both

derive instance eqScrollDirection :: Eq ScrollDirection

-- | Range of visible items
type VisibleRange =
  { startIndex :: Int
  , endIndex :: Int
  , overscanStart :: Int
  , overscanEnd :: Int
  }

-- | Internal scroll state
type VirtualScrollState =
  { scrollOffset :: Number
  , scrollOffsetY :: Number
  , scrollOffsetX :: Number
  , measuredHeights :: Array Number
  , measuredWidths :: Array Number
  , estimatedItemSize :: Number
  }

-- | Reference to virtual scroll instance for imperative operations
newtype VirtualScrollRef = VirtualScrollRef
  { scrollOffset :: Ref Number
  , measuredHeights :: Ref (Array Number)
  , containerRef :: Ref (Maybe ScrollContainerRaw)
  }

-- | Raw DOM scroll container
foreign import data ScrollContainerRaw :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // list props
-- ═══════════════════════════════════════════════════════════════════════════════

type VirtualScrollProps i =
  { itemCount :: Int
  , itemHeight :: ItemHeight
  , containerHeight :: Number
  , containerWidth :: Number
  , overscan :: Int
  , horizontal :: Boolean
  , scrollToIndex :: Maybe Int
  , onScroll :: Maybe (Number -> i)
  , onVisibleRangeChange :: Maybe (VisibleRange -> i)
  , className :: String
  , estimatedItemSize :: Number
  }

type VirtualScrollProp i = VirtualScrollProps i -> VirtualScrollProps i

defaultProps :: forall i. VirtualScrollProps i
defaultProps =
  { itemCount: 0
  , itemHeight: Fixed 40.0
  , containerHeight: 400.0
  , containerWidth: 400.0
  , overscan: 3
  , horizontal: false
  , scrollToIndex: Nothing
  , onScroll: Nothing
  , onVisibleRangeChange: Nothing
  , className: ""
  , estimatedItemSize: 40.0
  }

-- | Set total number of items
itemCount :: forall i. Int -> VirtualScrollProp i
itemCount n props = props { itemCount = n }

-- | Set item height mode
itemHeight :: forall i. ItemHeight -> VirtualScrollProp i
itemHeight h props = props { itemHeight = h }

-- | Set container height in pixels
containerHeight :: forall i. Number -> VirtualScrollProp i
containerHeight h props = props { containerHeight = h }

-- | Set container width in pixels (for horizontal scrolling)
containerWidth :: forall i. Number -> VirtualScrollProp i
containerWidth w props = props { containerWidth = w }

-- | Set overscan count (extra items to render above/below viewport)
overscan :: forall i. Int -> VirtualScrollProp i
overscan n props = props { overscan = n }

-- | Enable horizontal scrolling
horizontal :: forall i. Boolean -> VirtualScrollProp i
horizontal h props = props { horizontal = h }

-- | Scroll to specific index
scrollToIndex :: forall i. Int -> VirtualScrollProp i
scrollToIndex idx props = props { scrollToIndex = Just idx }

-- | Callback when scroll position changes
onScroll :: forall i. (Number -> i) -> VirtualScrollProp i
onScroll handler props = props { onScroll = Just handler }

-- | Callback when visible range changes
onVisibleRangeChange :: forall i. (VisibleRange -> i) -> VirtualScrollProp i
onVisibleRangeChange handler props = props { onVisibleRangeChange = Just handler }

-- | Add custom class
className :: forall i. String -> VirtualScrollProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // grid props
-- ═══════════════════════════════════════════════════════════════════════════════

type VirtualGridProps i =
  { rowCount :: Int
  , columnCount :: Int
  , cellWidth :: Number
  , cellHeight :: Number
  , containerHeight :: Number
  , containerWidth :: Number
  , overscanRows :: Int
  , overscanColumns :: Int
  , stickyRows :: Int
  , stickyColumns :: Int
  , onScroll :: Maybe ({ x :: Number, y :: Number } -> i)
  , className :: String
  }

type VirtualGridProp i = VirtualGridProps i -> VirtualGridProps i

defaultGridProps :: forall i. VirtualGridProps i
defaultGridProps =
  { rowCount: 0
  , columnCount: 0
  , cellWidth: 100.0
  , cellHeight: 40.0
  , containerHeight: 400.0
  , containerWidth: 600.0
  , overscanRows: 2
  , overscanColumns: 2
  , stickyRows: 0
  , stickyColumns: 0
  , onScroll: Nothing
  , className: ""
  }

-- | Set row count
rowCount :: forall i. Int -> VirtualGridProp i
rowCount n props = props { rowCount = n }

-- | Set column count
columnCount :: forall i. Int -> VirtualGridProp i
columnCount n props = props { columnCount = n }

-- | Set cell width
cellWidth :: forall i. Number -> VirtualGridProp i
cellWidth w props = props { cellWidth = w }

-- | Set cell height
cellHeight :: forall i. Number -> VirtualGridProp i
cellHeight h props = props { cellHeight = h }

-- | Set number of sticky (frozen) header rows
stickyRows :: forall i. Int -> VirtualGridProp i
stickyRows n props = props { stickyRows = n }

-- | Set number of sticky (frozen) header columns
stickyColumns :: forall i. Int -> VirtualGridProp i
stickyColumns n props = props { stickyColumns = n }

-- | Callback when grid scrolls
gridOnScroll :: forall i. ({ x :: Number, y :: Number } -> i) -> VirtualGridProp i
gridOnScroll handler props = props { onScroll = Just handler }

-- | Add custom class to grid
gridClassName :: forall i. String -> VirtualGridProp i
gridClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // calculations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate which items are visible given scroll offset
calculateVisibleRange
  :: { scrollOffset :: Number
     , containerSize :: Number
     , itemCount :: Int
     , itemHeight :: ItemHeight
     , overscan :: Int
     , estimatedItemSize :: Number
     }
  -> VisibleRange
calculateVisibleRange opts =
  let
    getItemOffset :: Int -> Number
    getItemOffset idx = case opts.itemHeight of
      Fixed h -> toNumber idx * h
      Variable f -> sumHeights f 0 idx
      Dynamic -> toNumber idx * opts.estimatedItemSize

    getItemSize :: Int -> Number
    getItemSize idx = case opts.itemHeight of
      Fixed h -> h
      Variable f -> f idx
      Dynamic -> opts.estimatedItemSize

    -- Binary search for start index
    findStartIndex :: Int -> Int -> Int
    findStartIndex low high
      | low >= high = low
      | otherwise =
          let mid = (low + high) / 2
              offset = getItemOffset mid
          in if offset < opts.scrollOffset
             then findStartIndex (mid + 1) high
             else findStartIndex low mid

    -- Find end index by scanning forward
    findEndIndex :: Int -> Number -> Int
    findEndIndex idx accOffset
      | idx >= opts.itemCount = opts.itemCount - 1
      | accOffset > opts.scrollOffset + opts.containerSize = idx
      | otherwise = findEndIndex (idx + 1) (accOffset + getItemSize idx)

    rawStart = findStartIndex 0 opts.itemCount
    rawEnd = findEndIndex rawStart (getItemOffset rawStart)
    
    startIndex = max 0 rawStart
    endIndex = min (opts.itemCount - 1) rawEnd
    overscanStart = max 0 (startIndex - opts.overscan)
    overscanEnd = min (opts.itemCount - 1) (endIndex + opts.overscan)
  in
    { startIndex, endIndex, overscanStart, overscanEnd }

-- | Sum heights for variable height calculation
sumHeights :: (Int -> Number) -> Int -> Int -> Number
sumHeights f start end
  | start >= end = 0.0
  | otherwise = f start + sumHeights f (start + 1) end

-- | Calculate scroll position for a given index
calculateScrollPosition
  :: { index :: Int
     , itemHeight :: ItemHeight
     , estimatedItemSize :: Number
     }
  -> Number
calculateScrollPosition opts = case opts.itemHeight of
  Fixed h -> toNumber opts.index * h
  Variable f -> sumHeights f 0 opts.index
  Dynamic -> toNumber opts.index * opts.estimatedItemSize

-- | Get estimated total height of all items
getEstimatedTotalHeight
  :: { itemCount :: Int
     , itemHeight :: ItemHeight
     , estimatedItemSize :: Number
     }
  -> Number
getEstimatedTotalHeight opts = case opts.itemHeight of
  Fixed h -> toNumber opts.itemCount * h
  Variable f -> sumHeights f 0 opts.itemCount
  Dynamic -> toNumber opts.itemCount * opts.estimatedItemSize

-- | Get estimated total width (for horizontal scrolling)
getEstimatedTotalWidth
  :: { itemCount :: Int
     , itemWidth :: Number
     }
  -> Number
getEstimatedTotalWidth opts = toNumber opts.itemCount * opts.itemWidth

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Virtualized list component
-- |
-- | Renders only visible items plus overscan buffer for 60fps scrolling
-- | with any number of items.
virtualList
  :: forall w i
   . Array (VirtualScrollProp i)
  -> (Int -> HH.HTML w i)  -- ^ Render function for each item
  -> Number                -- ^ Current scroll offset (from state)
  -> HH.HTML w i
virtualList propMods renderItem scrollOffset =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    totalHeight = getEstimatedTotalHeight
      { itemCount: props.itemCount
      , itemHeight: props.itemHeight
      , estimatedItemSize: props.estimatedItemSize
      }
    
    visibleRange = calculateVisibleRange
      { scrollOffset
      , containerSize: if props.horizontal then props.containerWidth else props.containerHeight
      , itemCount: props.itemCount
      , itemHeight: props.itemHeight
      , overscan: props.overscan
      , estimatedItemSize: props.estimatedItemSize
      }
    
    -- Generate visible items with positioning
    visibleItems = map (\idx ->
      let
        offset = calculateScrollPosition
          { index: idx
          , itemHeight: props.itemHeight
          , estimatedItemSize: props.estimatedItemSize
          }
        height = case props.itemHeight of
          Fixed h -> h
          Variable f -> f idx
          Dynamic -> props.estimatedItemSize
        style = if props.horizontal
          then "position: absolute; left: " <> show offset <> "px; width: " <> show height <> "px; height: 100%;"
          else "position: absolute; top: " <> show offset <> "px; height: " <> show height <> "px; width: 100%;"
      in
        HH.div
          [ HP.style style
          , HP.attr (HH.AttrName "data-index") (show idx)
          ]
          [ renderItem idx ]
    ) (range visibleRange.overscanStart visibleRange.overscanEnd)
    
    containerStyle = 
      "position: relative; overflow: auto; will-change: transform;" <>
      (if props.horizontal
       then " width: " <> show props.containerWidth <> "px; height: 100%;"
       else " height: " <> show props.containerHeight <> "px; width: 100%;")
    
    innerStyle =
      "position: relative;" <>
      (if props.horizontal
       then " width: " <> show totalHeight <> "px; height: 100%;"
       else " height: " <> show totalHeight <> "px; width: 100%;")
  in
    HH.div
      [ cls [ "virtual-scroll-container", props.className ]
      , HP.style containerStyle
      ]
      [ HH.div
          [ cls [ "virtual-scroll-inner" ]
          , HP.style innerStyle
          ]
          visibleItems
      ]

-- | Virtualized grid component
-- |
-- | Virtualizes both rows AND columns for massive data grids.
-- | Supports sticky headers and frozen columns.
virtualGrid
  :: forall w i
   . Array (VirtualGridProp i)
  -> (Int -> Int -> HH.HTML w i)  -- ^ Render function (row, col)
  -> { scrollX :: Number, scrollY :: Number }  -- ^ Current scroll position
  -> HH.HTML w i
virtualGrid propMods renderCell scrollPos =
  let
    props = foldl (\p f -> f p) defaultGridProps propMods
    
    totalHeight = toNumber props.rowCount * props.cellHeight
    totalWidth = toNumber props.columnCount * props.cellWidth
    
    -- Calculate visible row range
    rowRange = calculateVisibleRange
      { scrollOffset: scrollPos.scrollY
      , containerSize: props.containerHeight
      , itemCount: props.rowCount
      , itemHeight: Fixed props.cellHeight
      , overscan: props.overscanRows
      , estimatedItemSize: props.cellHeight
      }
    
    -- Calculate visible column range
    colRange = calculateVisibleRange
      { scrollOffset: scrollPos.scrollX
      , containerSize: props.containerWidth
      , itemCount: props.columnCount
      , itemHeight: Fixed props.cellWidth
      , overscan: props.overscanColumns
      , estimatedItemSize: props.cellWidth
      }
    
    -- Generate visible cells
    visibleCells = do
      rowIdx <- range rowRange.overscanStart rowRange.overscanEnd
      colIdx <- range colRange.overscanStart colRange.overscanEnd
      let
        top = toNumber rowIdx * props.cellHeight
        left = toNumber colIdx * props.cellWidth
        isSticky = rowIdx < props.stickyRows || colIdx < props.stickyColumns
        zIndex = if isSticky then "z-index: 10;" else ""
        position = if rowIdx < props.stickyRows && colIdx < props.stickyColumns
          then "position: sticky; top: 0; left: 0;"
          else if rowIdx < props.stickyRows
          then "position: sticky; top: 0;"
          else if colIdx < props.stickyColumns
          then "position: sticky; left: 0;"
          else "position: absolute;"
        style = position <> 
          " top: " <> show top <> "px;" <>
          " left: " <> show left <> "px;" <>
          " width: " <> show props.cellWidth <> "px;" <>
          " height: " <> show props.cellHeight <> "px;" <>
          zIndex
      pure $ HH.div
        [ HP.style style
        , HP.attr (HH.AttrName "data-row") (show rowIdx)
        , HP.attr (HH.AttrName "data-col") (show colIdx)
        ]
        [ renderCell rowIdx colIdx ]
    
    containerStyle = 
      "position: relative; overflow: auto; will-change: transform;" <>
      " width: " <> show props.containerWidth <> "px;" <>
      " height: " <> show props.containerHeight <> "px;"
    
    innerStyle =
      "position: relative;" <>
      " width: " <> show totalWidth <> "px;" <>
      " height: " <> show totalHeight <> "px;"
  in
    HH.div
      [ cls [ "virtual-grid-container", props.className ]
      , HP.style containerStyle
      ]
      [ HH.div
          [ cls [ "virtual-grid-inner" ]
          , HP.style innerStyle
          ]
          visibleCells
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // imperative api
-- ═══════════════════════════════════════════════════════════════════════════════

-- FFI imports
foreign import scrollToImpl :: ScrollContainerRaw -> Number -> Effect Unit
foreign import getScrollOffsetImpl :: ScrollContainerRaw -> Effect Number
foreign import measureElementImpl :: ScrollContainerRaw -> Int -> Effect Number

-- | Create a virtual scroll ref for imperative operations
createVirtualScrollRef :: Effect VirtualScrollRef
createVirtualScrollRef = do
  scrollOffset <- Ref.new 0.0
  measuredHeights <- Ref.new []
  containerRef <- Ref.new Nothing
  pure $ VirtualScrollRef { scrollOffset, measuredHeights, containerRef }

-- | Scroll to a specific pixel offset
scrollTo :: VirtualScrollRef -> Number -> Effect Unit
scrollTo (VirtualScrollRef ref) offset = do
  Ref.write offset ref.scrollOffset
  maybeContainer <- Ref.read ref.containerRef
  case maybeContainer of
    Just container -> scrollToImpl container offset
    Nothing -> pure unit

-- | Scroll to bring a specific item index into view
scrollToItem
  :: VirtualScrollRef
  -> { index :: Int
     , itemHeight :: ItemHeight
     , estimatedItemSize :: Number
     , align :: String  -- "start" | "center" | "end" | "auto"
     }
  -> Effect Unit
scrollToItem ref opts = do
  let offset = calculateScrollPosition
        { index: opts.index
        , itemHeight: opts.itemHeight
        , estimatedItemSize: opts.estimatedItemSize
        }
  scrollTo ref offset

-- | Get current scroll offset
getScrollOffset :: VirtualScrollRef -> Effect Number
getScrollOffset (VirtualScrollRef ref) = Ref.read ref.scrollOffset

-- | Measure an item's actual height (for Dynamic mode)
measureItem :: VirtualScrollRef -> Int -> Effect Number
measureItem (VirtualScrollRef ref) index = do
  maybeContainer <- Ref.read ref.containerRef
  case maybeContainer of
    Just container -> do
      height <- measureElementImpl container index
      -- Cache the measurement
      heights <- Ref.read ref.measuredHeights
      let newHeights = updateAt index height heights
      Ref.write newHeights ref.measuredHeights
      pure height
    Nothing -> pure 0.0
  where
  updateAt :: Int -> Number -> Array Number -> Array Number
  updateAt idx val arr =
    let
      padded = if length arr > idx
               then arr
               else arr <> Array.replicate (idx - length arr + 1) 0.0
    in fromMaybe padded (Array.updateAt idx val padded)
