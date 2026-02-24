-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // loadingbar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LoadingBar component
-- |
-- | A progress/loading bar for page transitions and async operations.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.LoadingBar as LoadingBar
-- |
-- | -- Indeterminate loading (continuous animation)
-- | LoadingBar.loadingBar
-- |   [ LoadingBar.indeterminate true
-- |   , LoadingBar.visible state.isLoading
-- |   ]
-- |
-- | -- Determinate progress
-- | LoadingBar.loadingBar
-- |   [ LoadingBar.progress state.uploadProgress
-- |   , LoadingBar.visible true
-- |   ]
-- |
-- | -- Top of page (fixed position)
-- | LoadingBar.loadingBar
-- |   [ LoadingBar.position LoadingBar.Top
-- |   , LoadingBar.indeterminate true
-- |   , LoadingBar.visible state.isLoading
-- |   ]
-- |
-- | -- Custom color
-- | LoadingBar.loadingBar
-- |   [ LoadingBar.color "bg-green-500"
-- |   , LoadingBar.progress 75.0
-- |   ]
-- | ```
module Hydrogen.Component.LoadingBar
  ( -- * LoadingBar Component
    loadingBar
  , loadingBarInline
    -- * Props
  , LoadingBarProps
  , LoadingBarProp
  , defaultProps
    -- * Prop Builders
  , progress
  , indeterminate
  , visible
  , position
  , height
  , color
  , showPercentage
  , animated
  , striped
  , className
    -- * Types
  , Position(Top, Bottom, Inline)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Int (round)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Position variants
data Position
  = Top       -- Fixed to top of viewport
  | Bottom    -- Fixed to bottom of viewport
  | Inline    -- Inline within content flow

derive instance eqPosition :: Eq Position

-- | Get position classes
positionClasses :: Position -> String
positionClasses = case _ of
  Top -> "fixed top-0 left-0 right-0 z-50"
  Bottom -> "fixed bottom-0 left-0 right-0 z-50"
  Inline -> "relative w-full"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | LoadingBar properties
type LoadingBarProps =
  { progress :: Number      -- 0.0 to 100.0
  , indeterminate :: Boolean
  , visible :: Boolean
  , position :: Position
  , height :: String        -- CSS height value
  , color :: String         -- Tailwind color class
  , showPercentage :: Boolean
  , animated :: Boolean
  , striped :: Boolean
  , className :: String
  }

-- | Property modifier
type LoadingBarProp = LoadingBarProps -> LoadingBarProps

-- | Default properties
defaultProps :: LoadingBarProps
defaultProps =
  { progress: 0.0
  , indeterminate: false
  , visible: true
  , position: Inline
  , height: "h-1"
  , color: "bg-primary"
  , showPercentage: false
  , animated: true
  , striped: false
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set progress (0-100)
progress :: Number -> LoadingBarProp
progress p props = props { progress = clamp 0.0 100.0 p }

-- | Set indeterminate mode
indeterminate :: Boolean -> LoadingBarProp
indeterminate i props = props { indeterminate = i }

-- | Set visibility
visible :: Boolean -> LoadingBarProp
visible v props = props { visible = v }

-- | Set position
position :: Position -> LoadingBarProp
position p props = props { position = p }

-- | Set height (Tailwind class like "h-1", "h-2", etc)
height :: String -> LoadingBarProp
height h props = props { height = h }

-- | Set color (Tailwind class like "bg-primary", "bg-green-500")
color :: String -> LoadingBarProp
color c props = props { color = c }

-- | Show percentage text
showPercentage :: Boolean -> LoadingBarProp
showPercentage s props = props { showPercentage = s }

-- | Enable animation
animated :: Boolean -> LoadingBarProp
animated a props = props { animated = a }

-- | Enable striped pattern
striped :: Boolean -> LoadingBarProp
striped s props = props { striped = s }

-- | Add custom class
className :: String -> LoadingBarProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Background track classes
trackClasses :: String
trackClasses =
  "w-full bg-secondary overflow-hidden"

-- | Progress bar classes
barClasses :: String
barClasses =
  "h-full transition-all duration-300 ease-out"

-- | Indeterminate animation classes
indeterminateClasses :: String
indeterminateClasses =
  "animate-loading-bar"

-- | Striped pattern classes
stripedClasses :: String
stripedClasses =
  "bg-[linear-gradient(45deg,rgba(255,255,255,.15)_25%,transparent_25%,transparent_50%,rgba(255,255,255,.15)_50%,rgba(255,255,255,.15)_75%,transparent_75%,transparent)] bg-[length:1rem_1rem]"

-- | Animated stripes classes
animatedStripesClasses :: String
animatedStripesClasses =
  "animate-[progress-stripes_1s_linear_infinite]"

-- | Percentage container classes
percentageClasses :: String
percentageClasses =
  "absolute right-2 top-1/2 -translate-y-1/2 text-xs font-medium text-foreground"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- Note: Using Prelude.clamp for bounds checking

-- | Full loading bar component
loadingBar :: forall w i. Array LoadingBarProp -> HH.HTML w i
loadingBar propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Bar classes
    barCls = 
      barClasses 
      <> " " <> props.color
      <> (if props.striped then " " <> stripedClasses else "")
      <> (if props.striped && props.animated then " " <> animatedStripesClasses else "")
      <> (if props.indeterminate then " " <> indeterminateClasses else "")
    
    -- Width style
    widthStyle = 
      if props.indeterminate
        then "width: 50%"
        else "width: " <> show props.progress <> "%"
    
    -- Round percentage for display
    percentageText = show (round props.progress) <> "%"
  in
    if not props.visible
      then HH.text ""
      else
        HH.div
          [ cls [ positionClasses props.position, props.className ] ]
          [ HH.div
              [ cls [ trackClasses, props.height ]
              , ARIA.role "progressbar"
              , ARIA.valueMin "0"
              , ARIA.valueMax "100"
              , ARIA.valueNow (show (round props.progress))
              ]
              [ HH.div
                  [ cls [ barCls ]
                  , HP.attr (HH.AttrName "style") widthStyle
                  ]
                  []
              ]
          -- Percentage text (optional)
          , if props.showPercentage && not props.indeterminate
              then 
                HH.span
                  [ cls [ percentageClasses ] ]
                  [ HH.text percentageText ]
              else HH.text ""
          ]

-- | Inline loading bar (convenience wrapper)
loadingBarInline :: forall w i. Number -> HH.HTML w i
loadingBarInline progressValue =
  loadingBar [ progress progressValue, position Inline ]
