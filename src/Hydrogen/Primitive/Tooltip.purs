-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // tooltip
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tooltip component
-- |
-- | Accessible tooltips with positioning.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.Tooltip as Tooltip
-- |
-- | Tooltip.tooltip []
-- |   [ Tooltip.tooltipTrigger []
-- |       [ Button.button [] [ HH.text "Hover me" ] ]
-- |   , Tooltip.tooltipContent [ Tooltip.side Tooltip.Top ]
-- |       [ HH.text "Tooltip content" ]
-- |   ]
-- | ```
module Hydrogen.Primitive.Tooltip
  ( -- * Tooltip Components
    tooltip
  , tooltipTrigger
  , tooltipContent
    -- * Props
  , TooltipProps
  , TooltipProp
  , side
  , open
  , className
    -- * Side
  , Side(..)
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // side
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tooltip side positioning
data Side
  = Top
  | Right
  | Bottom
  | Left

derive instance eqSide :: Eq Side

sideClasses :: Side -> String
sideClasses = case _ of
  Top -> "bottom-full left-1/2 -translate-x-1/2 mb-2"
  Right -> "left-full top-1/2 -translate-y-1/2 ml-2"
  Bottom -> "top-full left-1/2 -translate-x-1/2 mt-2"
  Left -> "right-full top-1/2 -translate-y-1/2 mr-2"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type TooltipProps =
  { side :: Side
  , open :: Boolean
  , className :: String
  }

type TooltipProp = TooltipProps -> TooltipProps

defaultProps :: TooltipProps
defaultProps =
  { side: Top
  , open: false
  , className: ""
  }

-- | Set tooltip side
side :: Side -> TooltipProp
side s props = props { side = s }

-- | Set open state
open :: Boolean -> TooltipProp
open o props = props { open = o }

-- | Add custom class
className :: String -> TooltipProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tooltip container (must wrap trigger and content)
tooltip :: forall w i. Array TooltipProp -> Array (HH.HTML w i) -> HH.HTML w i
tooltip propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative inline-block group", props.className ] ]
    children

-- | Tooltip trigger (the element that shows tooltip on hover)
tooltipTrigger :: forall w i. Array TooltipProp -> Array (HH.HTML w i) -> HH.HTML w i
tooltipTrigger propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ] ]
    children

-- | Tooltip content (shown on hover)
tooltipContent :: forall w i. Array TooltipProp -> Array (HH.HTML w i) -> HH.HTML w i
tooltipContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClass = if props.open then "opacity-100 visible" else "opacity-0 invisible group-hover:opacity-100 group-hover:visible"
  in
    HH.div
      [ cls [ "absolute z-50 overflow-hidden rounded-md border bg-popover px-3 py-1.5 text-sm text-popover-foreground shadow-md transition-opacity duration-150", sideClasses props.side, visibilityClass, props.className ]
      , ARIA.role "tooltip"
      ]
      children
