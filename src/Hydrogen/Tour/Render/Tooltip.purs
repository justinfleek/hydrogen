-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // tour // render // tooltip
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tooltip Render Functions
-- |
-- | Renders the complete tooltip component including title, body, arrow,
-- | progress indicator, and navigation buttons.

module Hydrogen.Tour.Render.Tooltip
  ( tourTooltip
  ) where

import Prelude
  ( (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Render.Element
  ( Element
  , ariaLabel
  , attr
  , button_
  , class_
  , classes
  , dataAttr
  , div_
  , empty
  , onClick
  , path_
  , role
  , svg_
  , tabIndex
  , text
  )
import Hydrogen.Tour.Render.Arrow (tourArrow)
import Hydrogen.Tour.Render.Helpers (placementToClass, sideToString)
import Hydrogen.Tour.Render.Navigation (tourNavigation)
import Hydrogen.Tour.Render.Progress (tourProgress)
import Hydrogen.Tour.Render.Types (TooltipConfig)
import Hydrogen.Tour.Types (progressCurrent, progressTotal)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // tooltip
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete tooltip component
-- |
-- | Renders the tour step content including:
-- | - Title and body sections
-- | - Arrow pointing to target
-- | - Progress indicator
-- | - Navigation buttons
tourTooltip :: forall msg. TooltipConfig msg -> Element msg
tourTooltip config =
  div_
    [ classes
        [ "absolute"
        , "z-50"
        , "w-80"
        , "max-w-sm"
        , "rounded-lg"
        , "border"
        , "bg-popover"
        , "p-4"
        , "text-popover-foreground"
        , "shadow-lg"
        , "animate-in"
        , "fade-in-0"
        , "zoom-in-95"
        , "duration-200"
        , placementToClass config.placement
        ]
    , role "tooltip"
    , dataAttr "tour-tooltip" "true"
    , dataAttr "placement" (sideToString config.placement.side)
    , tabIndex 0
    , ariaLabel "Tour step"
    ]
    [ -- Arrow (if enabled)
      if config.showArrow
      then tourArrow config.placement
      else empty
    , -- Header section
      tooltipHeader config
    , -- Body section
      tooltipBody config.body
    , -- Footer with progress and navigation
      tooltipFooter config
    ]

-- | Tooltip header with title and close button
tooltipHeader :: forall msg. TooltipConfig msg -> Element msg
tooltipHeader config =
  div_
    [ class_ "flex items-start justify-between gap-2 mb-2" ]
    [ case config.title of
        Just t -> 
          div_
            [ class_ "font-semibold leading-none tracking-tight text-sm" ]
            [ text t ]
        Nothing -> empty
    , closeButton config.onClose
    ]

-- | Tooltip body text
tooltipBody :: forall msg. Maybe String -> Element msg
tooltipBody = case _ of
  Just b ->
    div_
      [ class_ "text-sm text-muted-foreground mb-4" ]
      [ text b ]
  Nothing -> empty

-- | Tooltip footer with progress and navigation
tooltipFooter :: forall msg. TooltipConfig msg -> Element msg
tooltipFooter config =
  div_
    [ class_ "flex items-center justify-between gap-2" ]
    [ -- Progress indicator
      case config.progress of
        Just p -> tourProgress (progressCurrent p) (progressTotal p) config.progressStyle
        Nothing -> empty
    , -- Navigation buttons
      tourNavigation
        { buttons: config.buttons
        , showKeyboardHints: false
        , isFirstStep: config.isFirstStep
        , isLastStep: config.isLastStep
        , onNext: config.onNext
        , onPrev: config.onPrev
        , onSkip: config.onSkip
        , onComplete: config.onComplete
        , onGoTo: config.onGoTo
        }
    ]

-- | Close button (X icon)
closeButton :: forall msg. msg -> Element msg
closeButton onClose =
  button_
    [ classes
        [ "rounded-sm"
        , "opacity-70"
        , "ring-offset-background"
        , "transition-opacity"
        , "hover:opacity-100"
        , "focus:outline-none"
        , "focus:ring-2"
        , "focus:ring-ring"
        , "focus:ring-offset-2"
        ]
    , attr "type" "button"
    , onClick onClose
    , ariaLabel "Close tour"
    ]
    [ closeIcon ]

-- | X icon for close button (SVG)
closeIcon :: forall msg. Element msg
closeIcon =
  svg_
    [ class_ "h-4 w-4"
    , attr "viewBox" "0 0 24 24"
    , attr "fill" "none"
    , attr "stroke" "currentColor"
    , attr "stroke-width" "2"
    , attr "stroke-linecap" "round"
    , attr "stroke-linejoin" "round"
    ]
    [ path_ [ attr "d" "M18 6L6 18" ]
    , path_ [ attr "d" "M6 6L18 18" ]
    ]
