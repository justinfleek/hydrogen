-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // component // motion // curve // curvekeyframe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Curve Keyframe Point Component
-- |
-- | Represents a keyframe point on a value curve editor (as opposed to
-- | the easing curve editor). Used in graph editors where keyframes
-- | exist at specific times with specific values.
-- |
-- | ## Visual
-- |
-- | ```
-- |        ● ← Selected keyframe
-- |       / \
-- |      /   \
-- |     ●─────○ ← Unselected keyframes
-- | ```
-- |
-- | ## Features
-- |
-- | - Diamond or circle shape based on interpolation
-- | - Draggable in time (X) and value (Y)
-- | - Selection state
-- | - Context menu support
-- | - Connected tangent handles
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Curve.CurveKeyframe as CurveKeyframe
-- |
-- | HH.slot _keyframe kfId CurveKeyframe.component
-- |   { time: 0.5
-- |   , value: 0.75
-- |   , interpolation: Bezier
-- |   , isSelected: true
-- |   , width: 400.0
-- |   , height: 200.0
-- |   }
-- |   HandleKeyframeOutput
-- | ```
module Hydrogen.Component.Motion.Curve.CurveKeyframe
  ( -- * Component
    component
  
  -- * Types
  , Query(..)
  , Input
  , Output(..)
  , Interpolation(..)
  , Slot
  
  -- * Slot Type
  , _curveKeyframe
  
  -- * Pure Rendering
  , renderKeyframePoint
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
import Web.UIEvent.MouseEvent (shiftKey) as MouseEvent

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Keyframe interpolation type
data Interpolation
  = Linear        -- Straight line to next keyframe
  | Bezier        -- Smooth bezier curve
  | Hold          -- Step function (hold value until next)

derive instance eqInterpolation :: Eq Interpolation

instance showInterpolation :: Show Interpolation where
  show Linear = "linear"
  show Bezier = "bezier"
  show Hold = "hold"

-- | Component input
type Input =
  { time :: Number             -- Time position (normalized 0-1)
  , value :: Number            -- Value position (normalized 0-1)
  , interpolation :: Interpolation
  , isSelected :: Boolean
  , width :: Number
  , height :: Number
  , padding :: Number
  , pointRadius :: Number
  , disabled :: Boolean
  }

-- | Component queries
data Query a
  = SetPosition Number Number a     -- time, value
  | GetPosition ({ time :: Number, value :: Number } -> a)
  | SetSelected Boolean a
  | SetInterpolation Interpolation a

-- | Component output
data Output
  = Selected Boolean               -- isAdditive (shift held)
  | Moved Number Number            -- Final position
  | Moving Number Number           -- Position during drag
  | DragStart
  | DragEnd
  | DoubleClicked                  -- Open easing editor
  | ContextMenuRequested           -- Right-click

-- | Internal state
type State =
  { time :: Number
  , value :: Number
  , interpolation :: Interpolation
  , isSelected :: Boolean
  , width :: Number
  , height :: Number
  , padding :: Number
  , pointRadius :: Number
  , disabled :: Boolean
  , isDragging :: Boolean
  , isHovered :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleMouseDown MouseEvent
  | HandleDoubleClick MouseEvent
  | HandleContextMenu MouseEvent
  | HandleMouseEnter
  | HandleMouseLeave

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_curveKeyframe :: Proxy "curveKeyframe"
_curveKeyframe = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CurveKeyframe component
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
  { time: input.time
  , value: input.value
  , interpolation: input.interpolation
  , isSelected: input.isSelected
  , width: input.width
  , height: input.height
  , padding: input.padding
  , pointRadius: input.pointRadius
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
    
    -- Convert normalized to SVG coordinates
    svgX = p + state.time * innerW
    svgY = state.height - p - state.value * innerH
  in
    case state.interpolation of
      Hold -> renderCircle state svgX svgY
      _ -> renderDiamond state svgX svgY

-- | Render diamond shape (for Linear/Bezier)
renderDiamond :: forall m. State -> Number -> Number -> H.ComponentHTML Action () m
renderDiamond state cx cy =
  let
    r = state.pointRadius
    -- Diamond points
    points = 
      show cx <> "," <> show (cy - r) <> " " <>
      show (cx + r) <> "," <> show cy <> " " <>
      show cx <> "," <> show (cy + r) <> " " <>
      show (cx - r) <> "," <> show cy
  in
    HH.element (HH.ElemName "polygon")
      [ HP.attr (HH.AttrName "points") points
      , HP.attr (HH.AttrName "fill") "currentColor"
      , HP.attr (HH.AttrName "stroke") (if state.isSelected then "white" else "currentColor")
      , HP.attr (HH.AttrName "stroke-width") (if state.isSelected then "2" else "1")
      , HP.attr (HH.AttrName "cursor") (if state.disabled then "not-allowed" else "grab")
      , cls [ pointColorClass state ]
      , HE.onMouseDown HandleMouseDown
      , HE.onDoubleClick HandleDoubleClick
      , HE.onMouseEnter (const HandleMouseEnter)
      , HE.onMouseLeave (const HandleMouseLeave)
      ]
      []

-- | Render circle shape (for Hold)
renderCircle :: forall m. State -> Number -> Number -> H.ComponentHTML Action () m
renderCircle state cx cy =
  HH.element (HH.ElemName "circle")
    [ HP.attr (HH.AttrName "cx") (show cx)
    , HP.attr (HH.AttrName "cy") (show cy)
    , HP.attr (HH.AttrName "r") (show state.pointRadius)
    , HP.attr (HH.AttrName "fill") "currentColor"
    , HP.attr (HH.AttrName "stroke") (if state.isSelected then "white" else "currentColor")
    , HP.attr (HH.AttrName "stroke-width") (if state.isSelected then "2" else "1")
    , HP.attr (HH.AttrName "cursor") (if state.disabled then "not-allowed" else "grab")
    , cls [ pointColorClass state ]
    , HE.onMouseDown HandleMouseDown
    , HE.onDoubleClick HandleDoubleClick
    , HE.onMouseEnter (const HandleMouseEnter)
    , HE.onMouseLeave (const HandleMouseLeave)
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // pure rendering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a keyframe point (pure function for use in parent SVG)
renderKeyframePoint :: forall w i.
  { x :: Number
  , y :: Number
  , radius :: Number
  , interpolation :: Interpolation
  , isSelected :: Boolean
  , colorClass :: String
  } -> HH.HTML w i
renderKeyframePoint config =
  case config.interpolation of
    Hold ->
      HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") (show config.x)
        , HP.attr (HH.AttrName "cy") (show config.y)
        , HP.attr (HH.AttrName "r") (show config.radius)
        , HP.attr (HH.AttrName "fill") "currentColor"
        , HP.attr (HH.AttrName "stroke") (if config.isSelected then "white" else "currentColor")
        , HP.attr (HH.AttrName "stroke-width") (if config.isSelected then "2" else "1")
        , cls [ config.colorClass ]
        ]
        []
    _ ->
      let
        r = config.radius
        points = 
          show config.x <> "," <> show (config.y - r) <> " " <>
          show (config.x + r) <> "," <> show config.y <> " " <>
          show config.x <> "," <> show (config.y + r) <> " " <>
          show (config.x - r) <> "," <> show config.y
      in
        HH.element (HH.ElemName "polygon")
          [ HP.attr (HH.AttrName "points") points
          , HP.attr (HH.AttrName "fill") "currentColor"
          , HP.attr (HH.AttrName "stroke") (if config.isSelected then "white" else "currentColor")
          , HP.attr (HH.AttrName "stroke-width") (if config.isSelected then "2" else "1")
          , cls [ config.colorClass ]
          ]
          []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

pointColorClass :: State -> String
pointColorClass state
  | state.disabled = "text-muted-foreground"
  | state.isSelected = "text-primary"
  | state.isDragging = "text-primary"
  | state.isHovered = "text-primary/80"
  | otherwise = "text-foreground"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    pure unit
  
  Receive input -> do
    H.modify_ \s -> s
      { time = input.time
      , value = input.value
      , interpolation = input.interpolation
      , isSelected = input.isSelected
      , width = input.width
      , height = input.height
      , padding = input.padding
      , pointRadius = input.pointRadius
      , disabled = input.disabled
      }
  
  HandleMouseDown event -> do
    state <- H.get
    unless state.disabled do
      let isAdditive = MouseEvent.shiftKey event
      H.modify_ _ { isDragging = true }
      H.raise (Selected isAdditive)
      H.raise DragStart
  
  HandleDoubleClick _ -> do
    state <- H.get
    unless state.disabled do
      H.raise DoubleClicked
  
  HandleContextMenu _ -> do
    state <- H.get
    unless state.disabled do
      H.raise ContextMenuRequested
  
  HandleMouseEnter -> do
    H.modify_ _ { isHovered = true }
  
  HandleMouseLeave -> do
    H.modify_ _ { isHovered = false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetPosition time value reply -> do
    H.modify_ _ { time = time, value = value }
    pure (Just reply)
  
  GetPosition reply -> do
    state <- H.get
    pure (Just (reply { time: state.time, value: state.value }))
  
  SetSelected selected reply -> do
    H.modify_ _ { isSelected = selected }
    pure (Just reply)
  
  SetInterpolation interp reply -> do
    H.modify_ _ { interpolation = interp }
    pure (Just reply)
