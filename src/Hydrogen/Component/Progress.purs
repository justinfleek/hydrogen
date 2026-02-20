-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // progress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Progress bar component
-- |
-- | Progress indicators for showing completion status.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Progress as Progress
-- |
-- | -- Basic progress bar
-- | Progress.progress [ Progress.value 60 ]
-- |
-- | -- With custom colors
-- | Progress.progress [ Progress.value 80, Progress.indicatorClass "bg-green-500" ]
-- |
-- | -- Indeterminate (loading)
-- | Progress.progressIndeterminate []
-- | ```
module Hydrogen.Component.Progress
  ( -- * Progress Component
    progress
  , progressIndeterminate
    -- * Props
  , ProgressProps
  , ProgressProp
  , value
  , max
  , className
  , indicatorClass
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type ProgressProps =
  { value :: Int
  , max :: Int
  , className :: String
  , indicatorClass :: String
  }

type ProgressProp = ProgressProps -> ProgressProps

defaultProps :: ProgressProps
defaultProps =
  { value: 0
  , max: 100
  , className: ""
  , indicatorClass: ""
  }

-- | Set progress value (0-100)
value :: Int -> ProgressProp
value v props = props { value = v }

-- | Set max value
max :: Int -> ProgressProp
max m props = props { max = m }

-- | Add custom class to container
className :: String -> ProgressProp
className c props = props { className = props.className <> " " <> c }

-- | Add custom class to indicator
indicatorClass :: String -> ProgressProp
indicatorClass c props = props { indicatorClass = props.indicatorClass <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Progress bar
progress :: forall w i. Array ProgressProp -> HH.HTML w i
progress propMods =
  let 
    props = foldl (\p f -> f p) defaultProps propMods
    percentage = (props.value * 100) / props.max
    widthStyle = "width: " <> show percentage <> "%"
  in
    HH.div
      [ cls [ "relative h-4 w-full overflow-hidden rounded-full bg-secondary", props.className ]
      , ARIA.role "progressbar"
      , ARIA.valueNow (show props.value)
      , ARIA.valueMin "0"
      , ARIA.valueMax (show props.max)
      ]
      [ HH.div
          [ cls [ "h-full w-full flex-1 bg-primary transition-all", props.indicatorClass ]
          , HP.attr (HH.AttrName "style") widthStyle
          ]
          []
      ]

-- | Indeterminate progress (loading state)
progressIndeterminate :: forall w i. Array ProgressProp -> HH.HTML w i
progressIndeterminate propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ "relative h-4 w-full overflow-hidden rounded-full bg-secondary", props.className ]
      , ARIA.role "progressbar"
      ]
      [ HH.div
          [ cls [ "h-full w-1/3 bg-primary animate-progress-indeterminate", props.indicatorClass ] ]
          []
      ]
