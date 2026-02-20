-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // scroll-area
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Custom scrollbars with shadow indicators
-- |
-- | Styled scrollbars with auto-hide, drag support, and scroll shadows
-- | to indicate more content. Full touch support.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Interaction.ScrollArea as ScrollArea
-- |
-- | -- Basic scroll area
-- | ScrollArea.scrollArea
-- |   [ ScrollArea.height 400
-- |   , ScrollArea.autoHide true
-- |   ]
-- |   [ HH.div_ longContent ]
-- |
-- | -- With horizontal scrollbar
-- | ScrollArea.scrollArea
-- |   [ ScrollArea.height 200
-- |   , ScrollArea.horizontal true
-- |   ]
-- |   [ HH.div [ HP.style "width: 2000px" ] wideContent ]
-- |
-- | -- With scroll shadows
-- | ScrollArea.scrollArea
-- |   [ ScrollArea.height 300
-- |   , ScrollArea.shadows true
-- |   ]
-- |   [ HH.div_ content ]
-- | ```
module Hydrogen.Interaction.ScrollArea
  ( -- * Components
    scrollArea
  , scrollbar
  , scrollbarThumb
  , scrollShadows
    -- * Types
  , ScrollAreaState
  , ScrollbarOrientation(..)
    -- * Props
  , ScrollAreaProps
  , ScrollAreaProp
  , height
  , maxHeight
  , width
  , maxWidth
  , horizontal
  , vertical
  , autoHide
  , hideDelay
  , shadows
  , shadowSize
  , scrollbarWidth
  , onScroll
  , className
    -- * Scrollbar Props
  , ScrollbarProps
  , ScrollbarProp
  , orientation
  , thumbMinSize
  , thumbClassName
    -- * Imperative API
  , ScrollAreaRef
  , createScrollAreaRef
  , scrollTo
  , scrollToElement
  , scrollToTop
  , scrollToBottom
  , scrollToLeft
  , scrollToRight
  , getScrollPosition
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scrollbar orientation
data ScrollbarOrientation
  = Vertical
  | Horizontal

derive instance eqScrollbarOrientation :: Eq ScrollbarOrientation

instance showScrollbarOrientation :: Show ScrollbarOrientation where
  show Vertical = "vertical"
  show Horizontal = "horizontal"

-- | Internal scroll state
type ScrollAreaState =
  { scrollTop :: Number
  , scrollLeft :: Number
  , scrollHeight :: Number
  , scrollWidth :: Number
  , clientHeight :: Number
  , clientWidth :: Number
  , showVertical :: Boolean
  , showHorizontal :: Boolean
  , isDragging :: Boolean
  , isHovering :: Boolean
  }

-- | Reference for imperative operations
newtype ScrollAreaRef = ScrollAreaRef
  { containerRef :: Ref (Maybe ScrollAreaContainerRaw)
  , state :: Ref ScrollAreaState
  , hideTimeout :: Ref (Maybe TimeoutId)
  }

foreign import data ScrollAreaContainerRaw :: Type
foreign import data TimeoutId :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type ScrollAreaProps i =
  { height :: Maybe Number
  , maxHeight :: Maybe Number
  , width :: Maybe Number
  , maxWidth :: Maybe Number
  , horizontal :: Boolean
  , vertical :: Boolean
  , autoHide :: Boolean
  , hideDelay :: Number
  , shadows :: Boolean
  , shadowSize :: Number
  , scrollbarWidth :: Number
  , onScroll :: Maybe ({ x :: Number, y :: Number } -> i)
  , className :: String
  }

type ScrollAreaProp i = ScrollAreaProps i -> ScrollAreaProps i

defaultProps :: forall i. ScrollAreaProps i
defaultProps =
  { height: Nothing
  , maxHeight: Nothing
  , width: Nothing
  , maxWidth: Nothing
  , horizontal: false
  , vertical: true
  , autoHide: true
  , hideDelay: 1000.0
  , shadows: false
  , shadowSize: 8.0
  , scrollbarWidth: 8.0
  , onScroll: Nothing
  , className: ""
  }

-- | Set fixed height
height :: forall i. Number -> ScrollAreaProp i
height h props = props { height = Just h }

-- | Set max height (scroll when exceeded)
maxHeight :: forall i. Number -> ScrollAreaProp i
maxHeight h props = props { maxHeight = Just h }

-- | Set fixed width
width :: forall i. Number -> ScrollAreaProp i
width w props = props { width = Just w }

-- | Set max width
maxWidth :: forall i. Number -> ScrollAreaProp i
maxWidth w props = props { maxWidth = Just w }

-- | Enable horizontal scrolling
horizontal :: forall i. Boolean -> ScrollAreaProp i
horizontal h props = props { horizontal = h }

-- | Enable vertical scrolling (default: true)
vertical :: forall i. Boolean -> ScrollAreaProp i
vertical v props = props { vertical = v }

-- | Auto-hide scrollbars when not scrolling
autoHide :: forall i. Boolean -> ScrollAreaProp i
autoHide a props = props { autoHide = a }

-- | Delay before hiding scrollbars (ms)
hideDelay :: forall i. Number -> ScrollAreaProp i
hideDelay d props = props { hideDelay = d }

-- | Show scroll shadows at edges
shadows :: forall i. Boolean -> ScrollAreaProp i
shadows s props = props { shadows = s }

-- | Shadow size in pixels
shadowSize :: forall i. Number -> ScrollAreaProp i
shadowSize s props = props { shadowSize = s }

-- | Scrollbar width in pixels
scrollbarWidth :: forall i. Number -> ScrollAreaProp i
scrollbarWidth w props = props { scrollbarWidth = w }

-- | Callback when scrolled
onScroll :: forall i. ({ x :: Number, y :: Number } -> i) -> ScrollAreaProp i
onScroll handler props = props { onScroll = Just handler }

-- | Add custom class
className :: forall i. String -> ScrollAreaProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // scrollbar props
-- ═══════════════════════════════════════════════════════════════════════════════

type ScrollbarProps =
  { orientation :: ScrollbarOrientation
  , thumbMinSize :: Number
  , visible :: Boolean
  , thumbPosition :: Number   -- 0-1
  , thumbSize :: Number       -- 0-1
  , className :: String
  , thumbClassName :: String
  }

type ScrollbarProp = ScrollbarProps -> ScrollbarProps

defaultScrollbarProps :: ScrollbarProps
defaultScrollbarProps =
  { orientation: Vertical
  , thumbMinSize: 20.0
  , visible: true
  , thumbPosition: 0.0
  , thumbSize: 0.2
  , className: ""
  , thumbClassName: ""
  }

-- | Set scrollbar orientation
orientation :: ScrollbarOrientation -> ScrollbarProp
orientation o props = props { orientation = o }

-- | Minimum thumb size in pixels
thumbMinSize :: Number -> ScrollbarProp
thumbMinSize s props = props { thumbMinSize = s }

-- | Custom thumb class
thumbClassName :: String -> ScrollbarProp
thumbClassName c props = props { thumbClassName = c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scroll area container with custom scrollbars
-- |
-- | Hides native scrollbars and renders custom styled ones.
-- | Supports both vertical and horizontal scrolling.
scrollArea
  :: forall w i
   . Array (ScrollAreaProp i)
  -> Array (HH.HTML w i)
  -> ScrollAreaState
  -> HH.HTML w i
scrollArea propMods children state =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Calculate container styles
    containerStyle = 
      "position: relative; overflow: hidden;" <>
      dimensionStyle "height" props.height <>
      dimensionStyle "max-height" props.maxHeight <>
      dimensionStyle "width" props.width <>
      dimensionStyle "max-width" props.maxWidth
    
    -- Viewport styles
    viewportStyle =
      "position: relative; overflow: auto; height: 100%; width: 100%;" <>
      " scrollbar-width: none; -ms-overflow-style: none;" <>
      " -webkit-overflow-scrolling: touch;"
    
    -- Calculate thumb positions
    verticalThumbPos = if state.scrollHeight > state.clientHeight
      then state.scrollTop / (state.scrollHeight - state.clientHeight)
      else 0.0
    
    verticalThumbSize = if state.scrollHeight > 0.0
      then state.clientHeight / state.scrollHeight
      else 1.0
    
    horizontalThumbPos = if state.scrollWidth > state.clientWidth
      then state.scrollLeft / (state.scrollWidth - state.clientWidth)
      else 0.0
    
    horizontalThumbSize = if state.scrollWidth > 0.0
      then state.clientWidth / state.scrollWidth
      else 1.0
    
    -- Show scrollbars
    showVert = props.vertical && state.scrollHeight > state.clientHeight
    showHoriz = props.horizontal && state.scrollWidth > state.clientWidth
    
    scrollbarVisible = not props.autoHide || state.isDragging || state.isHovering
    
    -- Scroll shadows
    shadowEls = if props.shadows
      then scrollShadows
        { scrollTop: state.scrollTop
        , scrollLeft: state.scrollLeft
        , scrollHeight: state.scrollHeight
        , scrollWidth: state.scrollWidth
        , clientHeight: state.clientHeight
        , clientWidth: state.clientWidth
        , shadowSize: props.shadowSize
        , showVertical: props.vertical
        , showHorizontal: props.horizontal
        }
      else []
  in
    HH.div
      [ cls [ "scroll-area-root group/scroll-area", props.className ]
      , HP.style containerStyle
      ]
      ( [ -- Viewport
          HH.div
            [ cls [ "scroll-area-viewport [&::-webkit-scrollbar]:hidden" ]
            , HP.style viewportStyle
            ]
            children
        
        -- Vertical scrollbar
        , if showVert
            then scrollbar
              [ orientation Vertical
              , (\p -> p { visible = scrollbarVisible })
              , (\p -> p { thumbPosition = verticalThumbPos })
              , (\p -> p { thumbSize = verticalThumbSize })
              ]
            else HH.text ""
        
        -- Horizontal scrollbar
        , if showHoriz
            then scrollbar
              [ orientation Horizontal
              , (\p -> p { visible = scrollbarVisible })
              , (\p -> p { thumbPosition = horizontalThumbPos })
              , (\p -> p { thumbSize = horizontalThumbSize })
              ]
            else HH.text ""
        
        -- Corner (when both scrollbars visible)
        , if showVert && showHoriz
            then HH.div
              [ cls [ "scroll-area-corner absolute bottom-0 right-0 bg-border" ]
              , HP.style $ "width: " <> show props.scrollbarWidth <> "px; height: " <> show props.scrollbarWidth <> "px;"
              ]
              []
            else HH.text ""
        ] <> shadowEls
      )
  where
  dimensionStyle :: String -> Maybe Number -> String
  dimensionStyle prop mVal = case mVal of
    Just v -> " " <> prop <> ": " <> show v <> "px;"
    Nothing -> ""

-- | Custom scrollbar component
scrollbar :: forall w i. Array ScrollbarProp -> HH.HTML w i
scrollbar propMods =
  let
    props = foldl (\p f -> f p) defaultScrollbarProps propMods
    
    isVertical = props.orientation == Vertical
    
    trackStyle = if isVertical
      then "position: absolute; right: 0; top: 0; bottom: 0; width: 8px;"
      else "position: absolute; bottom: 0; left: 0; right: 0; height: 8px;"
    
    visibilityClass = if props.visible
      then "opacity-100"
      else "opacity-0"
    
    -- Calculate thumb position and size
    thumbPosPercent = props.thumbPosition * 100.0
    thumbSizePercent = max (props.thumbMinSize / 100.0) props.thumbSize * 100.0
    
    thumbStyle = if isVertical
      then "position: absolute; left: 0; right: 0; top: " <> show thumbPosPercent <> "%; height: " <> show thumbSizePercent <> "%;"
      else "position: absolute; top: 0; bottom: 0; left: " <> show thumbPosPercent <> "%; width: " <> show thumbSizePercent <> "%;"
  in
    HH.div
      [ cls 
          [ "scroll-area-scrollbar transition-opacity duration-150"
          , visibilityClass
          , props.className
          ]
      , HP.style trackStyle
      , HP.attr (HH.AttrName "data-orientation") (show props.orientation)
      ]
      [ scrollbarThumb
          [ (\p -> p { className = props.thumbClassName }) ]
          thumbStyle
      ]

-- | Scrollbar thumb (draggable)
scrollbarThumb :: forall w i. Array (ScrollbarProps -> ScrollbarProps) -> String -> HH.HTML w i
scrollbarThumb propMods style =
  let
    props = foldl (\p f -> f p) defaultScrollbarProps propMods
  in
    HH.div
      [ cls 
          [ "scroll-area-thumb rounded-full bg-border hover:bg-border/80 transition-colors cursor-pointer"
          , props.thumbClassName
          ]
      , HP.style style
      ]
      []

-- | Scroll shadow indicators
-- |
-- | Shows shadows at edges when content is scrollable in that direction.
scrollShadows
  :: forall w i
   . { scrollTop :: Number
     , scrollLeft :: Number
     , scrollHeight :: Number
     , scrollWidth :: Number
     , clientHeight :: Number
     , clientWidth :: Number
     , shadowSize :: Number
     , showVertical :: Boolean
     , showHorizontal :: Boolean
     }
  -> Array (HH.HTML w i)
scrollShadows opts =
  let
    canScrollUp = opts.scrollTop > 0.0
    canScrollDown = opts.scrollTop < opts.scrollHeight - opts.clientHeight - 1.0
    canScrollLeft = opts.scrollLeft > 0.0
    canScrollRight = opts.scrollLeft < opts.scrollWidth - opts.clientWidth - 1.0
    
    shadowBase = "pointer-events-none absolute z-10 transition-opacity duration-150"
    
    topShadow = if opts.showVertical && canScrollUp
      then [ HH.div
          [ cls [ shadowBase, "inset-x-0 top-0" ]
          , HP.style $ "height: " <> show opts.shadowSize <> "px; background: linear-gradient(to bottom, rgba(0,0,0,0.1), transparent);"
          ]
          []
        ]
      else []
    
    bottomShadow = if opts.showVertical && canScrollDown
      then [ HH.div
          [ cls [ shadowBase, "inset-x-0 bottom-0" ]
          , HP.style $ "height: " <> show opts.shadowSize <> "px; background: linear-gradient(to top, rgba(0,0,0,0.1), transparent);"
          ]
          []
        ]
      else []
    
    leftShadow = if opts.showHorizontal && canScrollLeft
      then [ HH.div
          [ cls [ shadowBase, "inset-y-0 left-0" ]
          , HP.style $ "width: " <> show opts.shadowSize <> "px; background: linear-gradient(to right, rgba(0,0,0,0.1), transparent);"
          ]
          []
        ]
      else []
    
    rightShadow = if opts.showHorizontal && canScrollRight
      then [ HH.div
          [ cls [ shadowBase, "inset-y-0 right-0" ]
          , HP.style $ "width: " <> show opts.shadowSize <> "px; background: linear-gradient(to left, rgba(0,0,0,0.1), transparent);"
          ]
          []
        ]
      else []
  in
    topShadow <> bottomShadow <> leftShadow <> rightShadow

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // imperative api
-- ═══════════════════════════════════════════════════════════════════════════════

-- FFI imports
foreign import scrollToImpl :: ScrollAreaContainerRaw -> Number -> Number -> Effect Unit
foreign import scrollToElementImpl :: ScrollAreaContainerRaw -> String -> Effect Unit
foreign import getScrollPositionImpl :: ScrollAreaContainerRaw -> Effect { x :: Number, y :: Number }

-- | Create scroll area ref
createScrollAreaRef :: Effect ScrollAreaRef
createScrollAreaRef = do
  containerRef <- Ref.new Nothing
  state <- Ref.new defaultState
  hideTimeout <- Ref.new Nothing
  pure $ ScrollAreaRef { containerRef, state, hideTimeout }
  where
  defaultState =
    { scrollTop: 0.0
    , scrollLeft: 0.0
    , scrollHeight: 0.0
    , scrollWidth: 0.0
    , clientHeight: 0.0
    , clientWidth: 0.0
    , showVertical: false
    , showHorizontal: false
    , isDragging: false
    , isHovering: false
    }

-- | Scroll to specific position
scrollTo :: ScrollAreaRef -> { x :: Number, y :: Number } -> Effect Unit
scrollTo (ScrollAreaRef ref) pos = do
  maybeContainer <- Ref.read ref.containerRef
  case maybeContainer of
    Just container -> scrollToImpl container pos.x pos.y
    Nothing -> pure unit

-- | Scroll to bring element into view
scrollToElement :: ScrollAreaRef -> String -> Effect Unit
scrollToElement (ScrollAreaRef ref) selector = do
  maybeContainer <- Ref.read ref.containerRef
  case maybeContainer of
    Just container -> scrollToElementImpl container selector
    Nothing -> pure unit

-- | Scroll to top
scrollToTop :: ScrollAreaRef -> Effect Unit
scrollToTop ref = scrollTo ref { x: 0.0, y: 0.0 }

-- | Scroll to bottom
scrollToBottom :: ScrollAreaRef -> Effect Unit
scrollToBottom (ScrollAreaRef ref) = do
  maybeContainer <- Ref.read ref.containerRef
  state <- Ref.read ref.state
  case maybeContainer of
    Just container -> scrollToImpl container 0.0 (state.scrollHeight - state.clientHeight)
    Nothing -> pure unit

-- | Scroll to left
scrollToLeft :: ScrollAreaRef -> Effect Unit
scrollToLeft ref = scrollTo ref { x: 0.0, y: 0.0 }

-- | Scroll to right
scrollToRight :: ScrollAreaRef -> Effect Unit
scrollToRight (ScrollAreaRef ref) = do
  maybeContainer <- Ref.read ref.containerRef
  state <- Ref.read ref.state
  case maybeContainer of
    Just container -> scrollToImpl container (state.scrollWidth - state.clientWidth) 0.0
    Nothing -> pure unit

-- | Get current scroll position
getScrollPosition :: ScrollAreaRef -> Effect { x :: Number, y :: Number }
getScrollPosition (ScrollAreaRef ref) = do
  maybeContainer <- Ref.read ref.containerRef
  case maybeContainer of
    Just container -> getScrollPositionImpl container
    Nothing -> pure { x: 0.0, y: 0.0 }
