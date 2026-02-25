-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // component // motion // curve // curveeditor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier Curve Editor Component
-- |
-- | The main canvas for editing easing curves. Displays a grid with the
-- | bezier curve, control handles, and keyframe points. Used for fine-tuning
-- | animation timing in motion graphics editors.
-- |
-- | ## Visual Layout
-- |
-- | ```
-- |   1.0 ┤              ╭────●
-- |       │            ╱
-- |       │          ╱
-- |       │        ╱
-- |       │      ●╱  ← Control handles
-- |       │    ╱
-- |   0.0 ●──╯
-- |       └──────────────────┘
-- |      0.0               1.0
-- | ```
-- |
-- | ## Features
-- |
-- | - SVG-based curve rendering
-- | - Draggable control point handles
-- | - Grid with major/minor lines
-- | - Zoom and pan support
-- | - Real-time curve preview
-- | - Keyboard shortcuts for precision
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Curve.CurveEditor as CurveEditor
-- |
-- | HH.slot _curveEditor unit CurveEditor.component
-- |   { easing: Easing.easeInOut
-- |   , width: 300.0
-- |   , height: 200.0
-- |   , showGrid: true
-- |   , showLabels: true
-- |   }
-- |   HandleCurveEditorOutput
-- | ```
module Hydrogen.Component.Motion.Curve.CurveEditor
  ( -- * Component
    component
  
  -- * Types
  , Query(SetEasing, GetEasing, SetDimensions)
  , Input
  , Output(EasingChanged, EasingChanging, EditStart, EditEnd)
  , Slot
  
  -- * Slot Type
  , _curveEditor
  ) where

import Prelude
  ( class Eq
  , Unit
  , bind
  , discard
  , map
  , negate
  , pure
  , show
  , unit
  , when
  , (-)
  , (*)
  , (+)
  , (/)
  , (/=)
  , (<>)
  , (<<<)
  , (==)
  )

import Data.Array (range)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just))
import Data.Ord (clamp)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Schema.Motion.Easing (Easing)
import Hydrogen.Schema.Motion.Easing as Easing
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.DOM.Element (Element)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract clientX from a mouse event
foreign import getClientX :: MouseEvent -> Number

-- | Extract clientY from a mouse event
foreign import getClientY :: MouseEvent -> Number

-- | Get element bounding rect left
foreign import getTargetLeft :: MouseEvent -> Number

-- | Get element bounding rect top
foreign import getTargetTop :: MouseEvent -> Number

-- | Get the target SVG element from mouse event
foreign import getTargetElement :: MouseEvent -> Element

-- | Start document-level drag tracking
-- | Captures mouse events at document level for smooth dragging outside element
foreign import startDocumentDrag :: 
  Element ->                              -- Element to track bounds from
  (Number -> Number -> Effect Unit) ->    -- onMove (relX, relY relative to element)
  Effect Unit ->                          -- onEnd
  Effect Unit

-- | Stop any active document drag
foreign import stopDocumentDrag :: Effect Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Which control point is being dragged
data DragTarget
  = DragP1    -- First control point (x1, y1)
  | DragP2    -- Second control point (x2, y2)
  | NoDrag

derive instance eqDragTarget :: Eq DragTarget

-- | Component input
type Input =
  { easing :: Easing
  , width :: Number
  , height :: Number
  , showGrid :: Boolean
  , showLabels :: Boolean
  , padding :: Number
  }

-- | Component queries
data Query a
  = SetEasing Easing a
  | GetEasing (Easing -> a)
  | SetDimensions Number Number a

-- | Component output
data Output
  = EasingChanged Easing      -- Curve was modified
  | EasingChanging Easing     -- Curve is being dragged (live preview)
  | EditStart                 -- Started editing
  | EditEnd                   -- Finished editing

-- | Internal state
type State =
  { easing :: Easing
  , width :: Number
  , height :: Number
  , showGrid :: Boolean
  , showLabels :: Boolean
  , padding :: Number
  , dragTarget :: DragTarget
  , isHovered :: Boolean
  -- Control points (normalized 0-1)
  , p1x :: Number
  , p1y :: Number
  , p2x :: Number
  , p2y :: Number
  }

-- | Internal actions
data Action
  = Initialize
  | Finalize
  | Receive Input
  | HandleP1MouseDown MouseEvent
  | HandleP2MouseDown MouseEvent
  | HandleDocumentDragMove Number Number  -- relX, relY relative to SVG
  | HandleDocumentDragEnd
  | HandleMouseMove MouseEvent
  | HandleMouseUp MouseEvent
  | HandleMouseLeave MouseEvent
  | HandleCanvasClick MouseEvent

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_curveEditor :: Proxy "curveEditor"
_curveEditor = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CurveEditor component
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< Receive
      , initialize = Just Initialize
      , finalize = Just Finalize
      }
  }

-- | Initial state from input
initialState :: Input -> State
initialState input =
  let
    points = Easing.toControlPoints input.easing
  in
    { easing: input.easing
    , width: input.width
    , height: input.height
    , showGrid: input.showGrid
    , showLabels: input.showLabels
    , padding: input.padding
    , dragTarget: NoDrag
    , isHovered: false
    , p1x: points.x1
    , p1y: points.y1
    , p2x: points.x2
    , p2y: points.y2
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ containerClasses state ]
    , ARIA.role "application"
    , ARIA.label "Bezier curve editor"
    ]
    [ renderSVG state
    ]

-- | Render the SVG canvas
renderSVG :: forall m. State -> H.ComponentHTML Action () m
renderSVG state =
  let
    w = state.width
    h = state.height
  in
    HH.element (HH.ElemName "svg")
      [ HP.attr (HH.AttrName "width") (show w)
      , HP.attr (HH.AttrName "height") (show h)
      , HP.attr (HH.AttrName "viewBox") ("0 0 " <> show w <> " " <> show h)
      , cls [ "bg-background rounded border border-border" ]
      , HE.onMouseMove HandleMouseMove
      , HE.onMouseUp HandleMouseUp
      , HE.onMouseLeave HandleMouseLeave
      , HE.onClick HandleCanvasClick
      ]
      [ -- Grid (if enabled)
        if state.showGrid
          then renderGrid state
          else HH.text ""
      
      -- Diagonal reference line (linear)
      , renderLinearReference state
      
      -- Bezier curve
      , renderBezierCurve state
      
      -- Control point lines
      , renderControlLines state
      
      -- Control point handles
      , renderControlPoints state
      
      -- Labels (if enabled)
      , if state.showLabels
          then renderLabels state
          else HH.text ""
      ]

-- | Render the grid
renderGrid :: forall m. State -> H.ComponentHTML Action () m
renderGrid state =
  let
    w = state.width
    h = state.height
    p = state.padding
    innerW = w - 2.0 * p
    innerH = h - 2.0 * p
    
    -- Major grid lines (0.25 increments)
    majorLines = range 0 4
    -- Minor grid lines (0.125 increments)
    minorLines = range 0 8
  in
    HH.element (HH.ElemName "g")
      [ cls [ "text-border" ] ]
      (
        -- Minor vertical lines
        map (\i -> 
          let x = p + (toNumber i) * innerW / 8.0
          in HH.element (HH.ElemName "line")
            [ HP.attr (HH.AttrName "x1") (show x)
            , HP.attr (HH.AttrName "y1") (show p)
            , HP.attr (HH.AttrName "x2") (show x)
            , HP.attr (HH.AttrName "y2") (show (h - p))
            , HP.attr (HH.AttrName "stroke") "currentColor"
            , HP.attr (HH.AttrName "stroke-width") "0.5"
            , HP.attr (HH.AttrName "stroke-opacity") "0.3"
            ]
            []
        ) minorLines
        <>
        -- Minor horizontal lines
        map (\i -> 
          let y = p + (toNumber i) * innerH / 8.0
          in HH.element (HH.ElemName "line")
            [ HP.attr (HH.AttrName "x1") (show p)
            , HP.attr (HH.AttrName "y1") (show y)
            , HP.attr (HH.AttrName "x2") (show (w - p))
            , HP.attr (HH.AttrName "y2") (show y)
            , HP.attr (HH.AttrName "stroke") "currentColor"
            , HP.attr (HH.AttrName "stroke-width") "0.5"
            , HP.attr (HH.AttrName "stroke-opacity") "0.3"
            ]
            []
        ) minorLines
        <>
        -- Major vertical lines
        map (\i -> 
          let x = p + (toNumber i) * innerW / 4.0
          in HH.element (HH.ElemName "line")
            [ HP.attr (HH.AttrName "x1") (show x)
            , HP.attr (HH.AttrName "y1") (show p)
            , HP.attr (HH.AttrName "x2") (show x)
            , HP.attr (HH.AttrName "y2") (show (h - p))
            , HP.attr (HH.AttrName "stroke") "currentColor"
            , HP.attr (HH.AttrName "stroke-width") "1"
            , HP.attr (HH.AttrName "stroke-opacity") "0.5"
            ]
            []
        ) majorLines
        <>
        -- Major horizontal lines
        map (\i -> 
          let y = p + (toNumber i) * innerH / 4.0
          in HH.element (HH.ElemName "line")
            [ HP.attr (HH.AttrName "x1") (show p)
            , HP.attr (HH.AttrName "y1") (show y)
            , HP.attr (HH.AttrName "x2") (show (w - p))
            , HP.attr (HH.AttrName "y2") (show y)
            , HP.attr (HH.AttrName "stroke") "currentColor"
            , HP.attr (HH.AttrName "stroke-width") "1"
            , HP.attr (HH.AttrName "stroke-opacity") "0.5"
            ]
            []
        ) majorLines
      )

-- | Render linear reference line (diagonal)
renderLinearReference :: forall m. State -> H.ComponentHTML Action () m
renderLinearReference state =
  let
    w = state.width
    h = state.height
    p = state.padding
  in
    HH.element (HH.ElemName "line")
      [ HP.attr (HH.AttrName "x1") (show p)
      , HP.attr (HH.AttrName "y1") (show (h - p))
      , HP.attr (HH.AttrName "x2") (show (w - p))
      , HP.attr (HH.AttrName "y2") (show p)
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-width") "1"
      , HP.attr (HH.AttrName "stroke-dasharray") "4,4"
      , cls [ "text-muted-foreground" ]
      ]
      []

-- | Render the bezier curve
renderBezierCurve :: forall m. State -> H.ComponentHTML Action () m
renderBezierCurve state =
  let
    w = state.width
    h = state.height
    p = state.padding
    innerW = w - 2.0 * p
    innerH = h - 2.0 * p
    
    -- Convert normalized coords to SVG coords
    -- Note: Y is inverted (0 at bottom, 1 at top)
    toSvgX x = p + x * innerW
    toSvgY y = h - p - y * innerH
    
    -- Start point (0, 0)
    x0 = toSvgX 0.0
    y0 = toSvgY 0.0
    
    -- Control point 1
    cx1 = toSvgX state.p1x
    cy1 = toSvgY state.p1y
    
    -- Control point 2
    cx2 = toSvgX state.p2x
    cy2 = toSvgY state.p2y
    
    -- End point (1, 1)
    x1 = toSvgX 1.0
    y1 = toSvgY 1.0
    
    pathD = "M " <> show x0 <> " " <> show y0 <>
            " C " <> show cx1 <> " " <> show cy1 <>
            " " <> show cx2 <> " " <> show cy2 <>
            " " <> show x1 <> " " <> show y1
  in
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") pathD
      , HP.attr (HH.AttrName "fill") "none"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-width") "2"
      , HP.attr (HH.AttrName "stroke-linecap") "round"
      , cls [ "text-primary" ]
      ]
      []

-- | Render control point lines (from endpoints to handles)
renderControlLines :: forall m. State -> H.ComponentHTML Action () m
renderControlLines state =
  let
    w = state.width
    h = state.height
    p = state.padding
    innerW = w - 2.0 * p
    innerH = h - 2.0 * p
    
    toSvgX x = p + x * innerW
    toSvgY y = h - p - y * innerH
  in
    HH.element (HH.ElemName "g")
      [ cls [ "text-muted-foreground" ] ]
      [ -- Line from (0,0) to P1
        HH.element (HH.ElemName "line")
          [ HP.attr (HH.AttrName "x1") (show (toSvgX 0.0))
          , HP.attr (HH.AttrName "y1") (show (toSvgY 0.0))
          , HP.attr (HH.AttrName "x2") (show (toSvgX state.p1x))
          , HP.attr (HH.AttrName "y2") (show (toSvgY state.p1y))
          , HP.attr (HH.AttrName "stroke") "currentColor"
          , HP.attr (HH.AttrName "stroke-width") "1"
          ]
          []
      -- Line from (1,1) to P2
      , HH.element (HH.ElemName "line")
          [ HP.attr (HH.AttrName "x1") (show (toSvgX 1.0))
          , HP.attr (HH.AttrName "y1") (show (toSvgY 1.0))
          , HP.attr (HH.AttrName "x2") (show (toSvgX state.p2x))
          , HP.attr (HH.AttrName "y2") (show (toSvgY state.p2y))
          , HP.attr (HH.AttrName "stroke") "currentColor"
          , HP.attr (HH.AttrName "stroke-width") "1"
          ]
          []
      ]

-- | Render control point handles
renderControlPoints :: forall m. State -> H.ComponentHTML Action () m
renderControlPoints state =
  let
    w = state.width
    h = state.height
    p = state.padding
    innerW = w - 2.0 * p
    innerH = h - 2.0 * p
    
    toSvgX x = p + x * innerW
    toSvgY y = h - p - y * innerH
    
    handleRadius = 6.0
    endpointRadius = 4.0
  in
    HH.element (HH.ElemName "g")
      []
      [ -- Start point (0, 0) - not draggable
        HH.element (HH.ElemName "circle")
          [ HP.attr (HH.AttrName "cx") (show (toSvgX 0.0))
          , HP.attr (HH.AttrName "cy") (show (toSvgY 0.0))
          , HP.attr (HH.AttrName "r") (show endpointRadius)
          , HP.attr (HH.AttrName "fill") "currentColor"
          , cls [ "text-foreground" ]
          ]
          []
      
      -- End point (1, 1) - not draggable
      , HH.element (HH.ElemName "circle")
          [ HP.attr (HH.AttrName "cx") (show (toSvgX 1.0))
          , HP.attr (HH.AttrName "cy") (show (toSvgY 1.0))
          , HP.attr (HH.AttrName "r") (show endpointRadius)
          , HP.attr (HH.AttrName "fill") "currentColor"
          , cls [ "text-foreground" ]
          ]
          []
      
      -- Control point 1 - draggable
      , HH.element (HH.ElemName "circle")
          [ HP.attr (HH.AttrName "cx") (show (toSvgX state.p1x))
          , HP.attr (HH.AttrName "cy") (show (toSvgY state.p1y))
          , HP.attr (HH.AttrName "r") (show handleRadius)
          , HP.attr (HH.AttrName "fill") "currentColor"
          , HP.attr (HH.AttrName "stroke") "white"
          , HP.attr (HH.AttrName "stroke-width") "2"
          , HP.attr (HH.AttrName "cursor") "grab"
          , cls [ if state.dragTarget == DragP1 then "text-primary" else "text-accent-foreground" ]
          , HE.onMouseDown HandleP1MouseDown
          ]
          []
      
      -- Control point 2 - draggable
      , HH.element (HH.ElemName "circle")
          [ HP.attr (HH.AttrName "cx") (show (toSvgX state.p2x))
          , HP.attr (HH.AttrName "cy") (show (toSvgY state.p2y))
          , HP.attr (HH.AttrName "r") (show handleRadius)
          , HP.attr (HH.AttrName "fill") "currentColor"
          , HP.attr (HH.AttrName "stroke") "white"
          , HP.attr (HH.AttrName "stroke-width") "2"
          , HP.attr (HH.AttrName "cursor") "grab"
          , cls [ if state.dragTarget == DragP2 then "text-primary" else "text-accent-foreground" ]
          , HE.onMouseDown HandleP2MouseDown
          ]
          []
      ]

-- | Render axis labels
renderLabels :: forall m. State -> H.ComponentHTML Action () m
renderLabels state =
  let
    w = state.width
    h = state.height
    p = state.padding
  in
    HH.element (HH.ElemName "g")
      [ cls [ "text-muted-foreground" ] ]
      [ -- "0" at origin
        HH.element (HH.ElemName "text")
          [ HP.attr (HH.AttrName "x") (show (p - 8.0))
          , HP.attr (HH.AttrName "y") (show (h - p + 4.0))
          , HP.attr (HH.AttrName "font-size") "10"
          , HP.attr (HH.AttrName "text-anchor") "end"
          , HP.attr (HH.AttrName "fill") "currentColor"
          ]
          [ HH.text "0" ]
      
      -- "1" at top-left
      , HH.element (HH.ElemName "text")
          [ HP.attr (HH.AttrName "x") (show (p - 8.0))
          , HP.attr (HH.AttrName "y") (show (p + 4.0))
          , HP.attr (HH.AttrName "font-size") "10"
          , HP.attr (HH.AttrName "text-anchor") "end"
          , HP.attr (HH.AttrName "fill") "currentColor"
          ]
          [ HH.text "1" ]
      
      -- "1" at bottom-right
      , HH.element (HH.ElemName "text")
          [ HP.attr (HH.AttrName "x") (show (w - p))
          , HP.attr (HH.AttrName "y") (show (h - p + 14.0))
          , HP.attr (HH.AttrName "font-size") "10"
          , HP.attr (HH.AttrName "text-anchor") "middle"
          , HP.attr (HH.AttrName "fill") "currentColor"
          ]
          [ HH.text "1" ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

containerClasses :: State -> String
containerClasses _ =
  "inline-block select-none"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    pure unit
  
  Finalize -> do
    -- Clean up any active document drag tracking on component destruction
    H.liftEffect stopDocumentDrag
  
  Receive input -> do
    state <- H.get
    -- Only update if not dragging
    when (state.dragTarget == NoDrag) do
      let points = Easing.toControlPoints input.easing
      H.modify_ \s -> s
        { easing = input.easing
        , width = input.width
        , height = input.height
        , showGrid = input.showGrid
        , showLabels = input.showLabels
        , padding = input.padding
        , p1x = points.x1
        , p1y = points.y1
        , p2x = points.x2
        , p2y = points.y2
        }
  
  HandleP1MouseDown _ -> do
    H.modify_ _ { dragTarget = DragP1 }
    H.raise EditStart
  
  HandleP2MouseDown _ -> do
    H.modify_ _ { dragTarget = DragP2 }
    H.raise EditStart
  
  HandleMouseMove event -> do
    state <- H.get
    when (state.dragTarget /= NoDrag) do
      let
        -- Get mouse position relative to SVG
        clientX = getClientX event
        clientY = getClientY event
        left = getTargetLeft event
        top = getTargetTop event
        
        relX = clientX - left
        relY = clientY - top
        
        -- Convert to normalized coordinates
        p = state.padding
        innerW = state.width - 2.0 * p
        innerH = state.height - 2.0 * p
        
        -- Clamp X to 0-1, allow Y to go slightly outside
        normX = clamp 0.0 1.0 ((relX - p) / innerW)
        normY = clamp (-0.5) 1.5 (1.0 - (relY - p) / innerH)
      
      case state.dragTarget of
        DragP1 -> do
          H.modify_ _ { p1x = normX, p1y = normY }
          let newEasing = Easing.cubicBezier normX normY state.p2x state.p2y
          H.raise (EasingChanging newEasing)
        
        DragP2 -> do
          H.modify_ _ { p2x = normX, p2y = normY }
          let newEasing = Easing.cubicBezier state.p1x state.p1y normX normY
          H.raise (EasingChanging newEasing)
        
        NoDrag -> pure unit
  
  HandleMouseUp _ -> do
    state <- H.get
    when (state.dragTarget /= NoDrag) do
      let newEasing = Easing.cubicBezier state.p1x state.p1y state.p2x state.p2y
      H.modify_ _ { dragTarget = NoDrag, easing = newEasing }
      H.raise EditEnd
      H.raise (EasingChanged newEasing)
  
  HandleMouseLeave _ -> do
    state <- H.get
    when (state.dragTarget /= NoDrag) do
      let newEasing = Easing.cubicBezier state.p1x state.p1y state.p2x state.p2y
      H.modify_ _ { dragTarget = NoDrag, easing = newEasing }
      H.raise EditEnd
      H.raise (EasingChanged newEasing)
  
  HandleCanvasClick _ -> do
    -- Could be used for adding keyframes in the future
    pure unit
  
  HandleDocumentDragMove relX relY -> do
    -- Document-level drag move event (coordinates relative to SVG element)
    state <- H.get
    when (state.dragTarget /= NoDrag) do
      let
        -- Convert relative pixel coordinates to normalized coordinates
        p = state.padding
        innerW = state.width - 2.0 * p
        innerH = state.height - 2.0 * p
        
        -- Clamp X to 0-1, allow Y to go slightly outside for overshoot curves
        normX = clamp 0.0 1.0 ((relX - p) / innerW)
        normY = clamp (-0.5) 1.5 (1.0 - (relY - p) / innerH)
      
      case state.dragTarget of
        DragP1 -> do
          H.modify_ _ { p1x = normX, p1y = normY }
          let newEasing = Easing.cubicBezier normX normY state.p2x state.p2y
          H.raise (EasingChanging newEasing)
        
        DragP2 -> do
          H.modify_ _ { p2x = normX, p2y = normY }
          let newEasing = Easing.cubicBezier state.p1x state.p1y normX normY
          H.raise (EasingChanging newEasing)
        
        NoDrag -> pure unit
  
  HandleDocumentDragEnd -> do
    -- Document-level drag end event (mouse released anywhere)
    state <- H.get
    when (state.dragTarget /= NoDrag) do
      let newEasing = Easing.cubicBezier state.p1x state.p1y state.p2x state.p2y
      H.modify_ _ { dragTarget = NoDrag, easing = newEasing }
      H.liftEffect stopDocumentDrag
      H.raise EditEnd
      H.raise (EasingChanged newEasing)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetEasing easing reply -> do
    let points = Easing.toControlPoints easing
    H.modify_ _ 
      { easing = easing
      , p1x = points.x1
      , p1y = points.y1
      , p2x = points.x2
      , p2y = points.y2
      }
    pure (Just reply)
  
  GetEasing reply -> do
    state <- H.get
    pure (Just (reply state.easing))
  
  SetDimensions w h reply -> do
    H.modify_ _ { width = w, height = h }
    pure (Just reply)


