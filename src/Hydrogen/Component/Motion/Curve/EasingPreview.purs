-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // component // motion // curve // easingpreview
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing Preview - Inline bezier curve visualization
-- |
-- | A compact visual representation of an easing curve, used inline in
-- | property panels, keyframe editors, and easing pickers.
-- |
-- | ## Features
-- |
-- | - Mini SVG curve display
-- | - Hover to show larger preview tooltip
-- | - Click to edit (raises output)
-- | - Displays easing name on hover
-- | - Schema-based styling with transitions
-- |
-- | ## Visual Structure
-- |
-- | ```
-- | ┌────────┐
-- | │   ╭──╮ │  <- Bezier curve preview
-- | │ ╭─╯   │ │
-- | │╭╯     │ │
-- | └────────┘
-- |   ease-out   <- Label on hover
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Curve.EasingPreview as EasingPreview
-- | import Hydrogen.Schema.Motion.Easing as Easing
-- |
-- | HH.slot _easingPreview unit EasingPreview.component
-- |   { easing: Easing.easeOutCubic
-- |   , size: EasingPreview.Medium
-- |   , showLabel: true
-- |   }
-- |   HandleEasingPreviewOutput
-- | ```
module Hydrogen.Component.Motion.Curve.EasingPreview
  ( -- * Component
    component
  
  -- * Types
  , Query(..)
  , Input
  , Output(..)
  , Size(..)
  , Slot
  
  -- * Slot Type
  , _easingPreview
  ) where

import Prelude

import Data.Maybe (Maybe(Just))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Schema.Motion.Easing (Easing)
import Hydrogen.Schema.Motion.Easing as Easing
import Hydrogen.Style.Css as Css
import Hydrogen.Style.Motion as Motion
import Hydrogen.Style.Token as Token
import Hydrogen.UI.Core (cls, svgNS, svgCls)
import Type.Proxy (Proxy(Proxy))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Preview size options
data Size
  = Small   -- 24x24px - Inline with text
  | Medium  -- 40x40px - Property panel
  | Large   -- 64x64px - Picker preview

derive instance eqSize :: Eq Size

-- | Get size dimensions
sizeToPx :: Size -> Number
sizeToPx = case _ of
  Small -> 24.0
  Medium -> 40.0
  Large -> 64.0

-- | Component input
type Input =
  { easing :: Easing
  , size :: Size
  , showLabel :: Boolean
  , isSelected :: Boolean
  }

-- | Component queries
data Query a
  = SetEasing Easing a
  | GetEasing (Easing -> a)

-- | Component output
data Output
  = Clicked        -- User clicked to edit
  | Hovered        -- Mouse entered
  | Unhovered      -- Mouse left

-- | Internal state
type State =
  { easing :: Easing
  , size :: Size
  , showLabel :: Boolean
  , isSelected :: Boolean
  , isHovered :: Boolean
  }

-- | Internal actions
data Action
  = Receive Input
  | HandleClick
  | HandleMouseEnter
  | HandleMouseLeave

-- | Slot type
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_easingPreview :: Proxy "easingPreview"
_easingPreview = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | EasingPreview component
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< Receive
      }
  }

-- | Initial state from input
initialState :: Input -> State
initialState input =
  { easing: input.easing
  , size: input.size
  , showLabel: input.showLabel
  , isSelected: input.isSelected
  , isHovered: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Container styles
containerStyles :: Boolean -> Boolean -> String
containerStyles isSelected isHovered = Css.cx
  [ "relative inline-flex flex-col items-center"
  , "cursor-pointer"
  , Token.radius Token.RoundedMd
  , Motion.transition Motion.All
  , Motion.duration Motion.Quick
  , Motion.easing Motion.EaseOut
  , Css.when isSelected "ring-2 ring-primary ring-offset-1"
  , Css.when isHovered "bg-muted/50"
  , Css.motionReduce "transition-none"
  ]

-- | SVG container styles
svgContainerStyles :: Boolean -> String
svgContainerStyles isHovered = Css.cx
  [ "bg-muted/30 border border-border"
  , Token.radius Token.RoundedSm
  , "overflow-hidden"
  , Motion.transition Motion.All
  , Motion.duration Motion.Quick
  , Css.when isHovered "border-primary/50"
  , Css.motionReduce "transition-none"
  ]

-- | Label styles
labelStyles :: String
labelStyles = Css.cx
  [ "text-xs text-muted-foreground"
  , "mt-1 truncate max-w-full"
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render the easing preview
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    px = sizeToPx state.size
    easingName = Easing.name state.easing
  in
    HH.div
      [ cls [ containerStyles state.isSelected state.isHovered ]
      , HE.onClick (\_ -> HandleClick)
      , HE.onMouseEnter (\_ -> HandleMouseEnter)
      , HE.onMouseLeave (\_ -> HandleMouseLeave)
      , ARIA.role "button"
      , ARIA.label ("Easing: " <> easingName)
      ]
      [ -- SVG curve preview
        HH.div
          [ cls [ svgContainerStyles state.isHovered ]
          , HP.attr (HH.AttrName "style") 
              ("width: " <> show px <> "px; height: " <> show px <> "px;")
          ]
          [ renderCurveSvg state.easing px ]
      -- Label (if enabled)
      , if state.showLabel
          then HH.span
            [ cls [ labelStyles ]
            , HP.attr (HH.AttrName "style") ("max-width: " <> show px <> "px;")
            ]
            [ HH.text easingName ]
          else HH.text ""
      ]

-- | Render the SVG curve
renderCurveSvg :: forall m. Easing -> Number -> H.ComponentHTML Action () m
renderCurveSvg easing svgSize =
  let
    -- Get bezier control points
    cp1x = Easing.p1x easing
    cp1y = Easing.p1y easing
    cp2x = Easing.p2x easing
    cp2y = Easing.p2y easing
    
    -- Padding inside SVG
    pad = svgSize * 0.1
    innerSize = svgSize - (pad * 2.0)
    
    -- Transform bezier coordinates to SVG space
    -- Bezier: (0,0) = start, (1,1) = end
    -- SVG: (pad, size-pad) = start, (size-pad, pad) = end (Y inverted)
    toSvgX x = pad + (x * innerSize)
    toSvgY y = (svgSize - pad) - (y * innerSize)
    
    -- Build SVG path
    -- M = move to start, C = cubic bezier to end
    startX = toSvgX 0.0
    startY = toSvgY 0.0
    ctrlP1X = toSvgX cp1x
    ctrlP1Y = toSvgY cp1y
    ctrlP2X = toSvgX cp2x
    ctrlP2Y = toSvgY cp2y
    endX = toSvgX 1.0
    endY = toSvgY 1.0
    
    -- SVG path data
    pathD = 
      "M " <> show startX <> " " <> show startY <> " " <>
      "C " <> show ctrlP1X <> " " <> show ctrlP1Y <> " " <>
             show ctrlP2X <> " " <> show ctrlP2Y <> " " <>
             show endX <> " " <> show endY
    
    -- Diagonal reference line (shows linear easing)
    refLineD = 
      "M " <> show startX <> " " <> show startY <> " " <>
      "L " <> show endX <> " " <> show endY
    
    viewBoxStr = "0 0 " <> show svgSize <> " " <> show svgSize
  in
    svgElement "svg"
      [ HP.attr (HH.AttrName "viewBox") viewBoxStr
      , HP.attr (HH.AttrName "width") (show svgSize)
      , HP.attr (HH.AttrName "height") (show svgSize)
      ]
      [ -- Reference line (linear)
        svgElement "path"
          [ HP.attr (HH.AttrName "d") refLineD
          , HP.attr (HH.AttrName "fill") "none"
          , HP.attr (HH.AttrName "stroke") "currentColor"
          , HP.attr (HH.AttrName "stroke-width") "1"
          , HP.attr (HH.AttrName "stroke-dasharray") "2 2"
          , HP.attr (HH.AttrName "stroke-opacity") "0.3"
          , svgCls [ "text-border" ]
          ]
          []
      -- The bezier curve
      , svgElement "path"
          [ HP.attr (HH.AttrName "d") pathD
          , HP.attr (HH.AttrName "fill") "none"
          , HP.attr (HH.AttrName "stroke") "currentColor"
          , HP.attr (HH.AttrName "stroke-width") "2"
          , HP.attr (HH.AttrName "stroke-linecap") "round"
          , svgCls [ "text-primary" ]
          ]
          []
      -- Start point
      , svgElement "circle"
          [ HP.attr (HH.AttrName "cx") (show startX)
          , HP.attr (HH.AttrName "cy") (show startY)
          , HP.attr (HH.AttrName "r") "2"
          , HP.attr (HH.AttrName "fill") "currentColor"
          , svgCls [ "text-muted-foreground" ]
          ]
          []
      -- End point
      , svgElement "circle"
          [ HP.attr (HH.AttrName "cx") (show endX)
          , HP.attr (HH.AttrName "cy") (show endY)
          , HP.attr (HH.AttrName "r") "2"
          , HP.attr (HH.AttrName "fill") "currentColor"
          , svgCls [ "text-muted-foreground" ]
          ]
          []
      ]

-- | Create an SVG element using the SVG namespace
svgElement :: forall w i. String -> Array (HH.IProp () i) -> Array (HH.HTML w i) -> HH.HTML w i
svgElement name props = HH.elementNS svgNS (HH.ElemName name) props

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ \s -> s
      { easing = input.easing
      , size = input.size
      , showLabel = input.showLabel
      , isSelected = input.isSelected
      }
  
  HandleClick -> do
    H.raise Clicked
  
  HandleMouseEnter -> do
    H.modify_ _ { isHovered = true }
    H.raise Hovered
  
  HandleMouseLeave -> do
    H.modify_ _ { isHovered = false }
    H.raise Unhovered

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetEasing eas reply -> do
    H.modify_ _ { easing = eas }
    pure (Just reply)
  
  GetEasing reply -> do
    state <- H.get
    pure (Just (reply state.easing))
