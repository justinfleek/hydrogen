-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // component // motion // curve // curvehandle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier Curve Handle Component
-- |
-- | A draggable control point handle for manipulating bezier curve tangents.
-- | Renders as a circular handle connected to its anchor point by a line.
-- |
-- | ## Visual
-- |
-- | ```
-- |   ○ ← Anchor point (fixed)
-- |    \
-- |     \
-- |      ● ← Handle (draggable)
-- | ```
-- |
-- | ## Features
-- |
-- | - Draggable handle with visual feedback
-- | - Connects to anchor point with tangent line
-- | - Constrained or free movement modes
-- | - Hover and active states
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Curve.CurveHandle as CurveHandle
-- |
-- | HH.slot _handle1 unit CurveHandle.component
-- |   { anchorX: 0.0, anchorY: 0.0
-- |   , handleX: 0.42, handleY: 0.0
-- |   , width: 200.0, height: 150.0
-- |   , padding: 16.0
-- |   }
-- |   HandleOutput
-- | ```
module Hydrogen.Component.Motion.Curve.CurveHandle
  ( -- * Component
    component
  
  -- * Types
  , Query(..)
  , Input
  , Output(..)
  , Slot
  
  -- * Slot Type
  , _curveHandle
  
  -- * Pure Rendering
  , renderHandle
  , renderTangentLine
  ) where

import Prelude

import Data.Maybe (Maybe(Just))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract clientX from a mouse event
foreign import getClientX :: MouseEvent -> Number

-- | Extract clientY from a mouse event
foreign import getClientY :: MouseEvent -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Component input
type Input =
  { anchorX :: Number          -- Anchor point X (normalized 0-1)
  , anchorY :: Number          -- Anchor point Y (normalized 0-1)
  , handleX :: Number          -- Handle X (normalized 0-1)
  , handleY :: Number          -- Handle Y (normalized 0-1)
  , width :: Number            -- Canvas width
  , height :: Number           -- Canvas height
  , padding :: Number          -- Canvas padding
  , handleRadius :: Number     -- Radius of handle circle
  , disabled :: Boolean
  }

-- | Component queries
data Query a
  = SetHandlePosition Number Number a
  | GetHandlePosition ({ x :: Number, y :: Number } -> a)

-- | Component output
data Output
  = HandleMoved Number Number      -- New X, Y position (normalized)
  | HandleMoving Number Number     -- Position during drag
  | DragStart
  | DragEnd

-- | Internal state
type State =
  { anchorX :: Number
  , anchorY :: Number
  , handleX :: Number
  , handleY :: Number
  , width :: Number
  , height :: Number
  , padding :: Number
  , handleRadius :: Number
  , disabled :: Boolean
  , isDragging :: Boolean
  , isHovered :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleMouseDown MouseEvent
  | HandleMouseEnter
  | HandleMouseLeave

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_curveHandle :: Proxy "curveHandle"
_curveHandle = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CurveHandle component
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

-- | Initial state from input
initialState :: Input -> State
initialState input =
  { anchorX: input.anchorX
  , anchorY: input.anchorY
  , handleX: input.handleX
  , handleY: input.handleY
  , width: input.width
  , height: input.height
  , padding: input.padding
  , handleRadius: input.handleRadius
  , disabled: input.disabled
  , isDragging: false
  , isHovered: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    p = state.padding
    innerW = state.width - 2.0 * p
    innerH = state.height - 2.0 * p
    
    toSvgX x = p + x * innerW
    toSvgY y = state.height - p - y * innerH
    
    anchorSvgX = toSvgX state.anchorX
    anchorSvgY = toSvgY state.anchorY
    handleSvgX = toSvgX state.handleX
    handleSvgY = toSvgY state.handleY
  in
    HH.element (HH.ElemName "g")
      []
      [ -- Tangent line from anchor to handle
        HH.element (HH.ElemName "line")
          [ HP.attr (HH.AttrName "x1") (show anchorSvgX)
          , HP.attr (HH.AttrName "y1") (show anchorSvgY)
          , HP.attr (HH.AttrName "x2") (show handleSvgX)
          , HP.attr (HH.AttrName "y2") (show handleSvgY)
          , HP.attr (HH.AttrName "stroke") "currentColor"
          , HP.attr (HH.AttrName "stroke-width") "1"
          , cls [ "text-muted-foreground" ]
          ]
          []
      
      -- Handle circle
      , HH.element (HH.ElemName "circle")
          [ HP.attr (HH.AttrName "cx") (show handleSvgX)
          , HP.attr (HH.AttrName "cy") (show handleSvgY)
          , HP.attr (HH.AttrName "r") (show state.handleRadius)
          , HP.attr (HH.AttrName "fill") "currentColor"
          , HP.attr (HH.AttrName "stroke") "white"
          , HP.attr (HH.AttrName "stroke-width") "2"
          , HP.attr (HH.AttrName "cursor") (if state.disabled then "not-allowed" else "grab")
          , cls [ handleColorClass state ]
          , HE.onMouseDown HandleMouseDown
          , HE.onMouseEnter (const HandleMouseEnter)
          , HE.onMouseLeave (const HandleMouseLeave)
          ]
          []
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // pure rendering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a handle circle (pure function for use in parent SVG)
renderHandle :: forall w i. 
  { x :: Number
  , y :: Number
  , radius :: Number
  , isActive :: Boolean
  , colorClass :: String
  } -> HH.HTML w i
renderHandle config =
  HH.element (HH.ElemName "circle")
    [ HP.attr (HH.AttrName "cx") (show config.x)
    , HP.attr (HH.AttrName "cy") (show config.y)
    , HP.attr (HH.AttrName "r") (show config.radius)
    , HP.attr (HH.AttrName "fill") "currentColor"
    , HP.attr (HH.AttrName "stroke") "white"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "cursor") "grab"
    , cls [ config.colorClass ]
    ]
    []

-- | Render a tangent line (pure function for use in parent SVG)
renderTangentLine :: forall w i.
  { x1 :: Number
  , y1 :: Number
  , x2 :: Number
  , y2 :: Number
  , colorClass :: String
  } -> HH.HTML w i
renderTangentLine config =
  HH.element (HH.ElemName "line")
    [ HP.attr (HH.AttrName "x1") (show config.x1)
    , HP.attr (HH.AttrName "y1") (show config.y1)
    , HP.attr (HH.AttrName "x2") (show config.x2)
    , HP.attr (HH.AttrName "y2") (show config.y2)
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "1"
    , cls [ config.colorClass ]
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

handleColorClass :: State -> String
handleColorClass state
  | state.disabled = "text-muted-foreground"
  | state.isDragging = "text-primary"
  | state.isHovered = "text-primary/80"
  | otherwise = "text-accent-foreground"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    pure unit
  
  Receive input -> do
    H.modify_ \s -> s
      { anchorX = input.anchorX
      , anchorY = input.anchorY
      , handleX = input.handleX
      , handleY = input.handleY
      , width = input.width
      , height = input.height
      , padding = input.padding
      , handleRadius = input.handleRadius
      , disabled = input.disabled
      }
  
  HandleMouseDown _ -> do
    state <- H.get
    unless state.disabled do
      H.modify_ _ { isDragging = true }
      H.raise DragStart
  
  HandleMouseEnter -> do
    H.modify_ _ { isHovered = true }
  
  HandleMouseLeave -> do
    H.modify_ _ { isHovered = false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetHandlePosition x y reply -> do
    H.modify_ _ { handleX = x, handleY = y }
    pure (Just reply)
  
  GetHandlePosition reply -> do
    state <- H.get
    pure (Just (reply { x: state.handleX, y: state.handleY }))
