-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // tour // view
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | View components for Product Tours
-- |
-- | This module provides the visual components for rendering product tours:
-- | - Overlay with spotlight cutout
-- | - Tooltip with step content
-- | - Progress indicators
-- | - Navigation buttons
-- |
-- | All components are pure functions producing Halogen HTML.
-- | State is managed externally; these are view-only.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.View as TourView
-- | import Hydrogen.Tour.State as Tour
-- |
-- | renderTour :: forall w. Tour.TourState MyMsg -> HH.HTML w (Tour.TourMsg MyMsg)
-- | renderTour state = TourView.tour state
-- | ```
module Hydrogen.Tour.View
  ( -- * Main Component
    tour
    -- * Sub-Components
  , overlay
  , spotlight
  , tooltip
  , tooltipContent
  , tooltipHeader
  , tooltipBody
  , tooltipFooter
  , progressDots
  , progressFraction
  , navigationButtons
  , closeButton
    -- * Styles
  , overlayClass
  , tooltipClass
  , buttonPrimaryClass
  , buttonSecondaryClass
  , buttonTextClass
  ) where

import Prelude

import Data.Array (mapWithIndex)
import Data.Maybe (Maybe(Just, Nothing))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.A11y.Focus (focusRing)
import Hydrogen.Tour.State (DismissReason(ClickedClose, ClickedOverlay, PressedEscape), TourMsg(CompleteTour, CustomAction, DismissTour, GoToStepById, NextStep, PrevStep), TourState, currentStep, isFirstStep, isLastStep, progress)
import Hydrogen.Tour.Step (Button, ButtonAction(ActionComplete, ActionCustom, ActionGoTo, ActionNext, ActionPrev, ActionSkip), ButtonVariant(Primary, Secondary, Text), Step)
import Hydrogen.Tour.Types (Pixel(Pixel), Progress, Side(Bottom, Left, Right, Top), TourPhase(TourActive), isActive, progressCurrent, progressTotal)
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // main component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render the complete tour UI
-- |
-- | This is the main entry point for rendering a tour. It handles:
-- | - Rendering nothing when inactive
-- | - Overlay with spotlight
-- | - Tooltip with content
-- | - Progress indicator
-- | - Keyboard event handling
tour :: forall w msg. TourState msg -> HH.HTML w (TourMsg msg)
tour state =
  if isActive state.phase
  then case currentStep state of
    Just step -> tourActive state step
    Nothing -> HH.text ""
  else HH.text ""

-- | Render active tour
tourActive :: forall w msg. TourState msg -> Step msg -> HH.HTML w (TourMsg msg)
tourActive state step =
  HH.div
    [ cls [ "fixed inset-0 z-50" ]
    , ARIA.role "dialog"
    , ARIA.modal "true"
    , ARIA.label "Product tour"
    , HP.attr (HH.AttrName "data-tour-active") "true"
    , HE.onKeyDown handleKeyDown
    ]
    [ overlay state.config.closeOnOverlayClick
    , spotlight step.highlight.padding step.highlight.borderRadius
    , tooltip state step
    ]
  where
  handleKeyDown event = 
    let key = eventKey event
    in if key == "Escape" && state.config.closeOnEscape
       then DismissTour PressedEscape
       else if key == "ArrowRight" && state.config.keyboardNavEnabled
       then NextStep
       else if key == "ArrowLeft" && state.config.keyboardNavEnabled
       then PrevStep
       else NextStep  -- Default action (could be NoOp if we had one)

-- Foreign helper for key event
foreign import eventKey :: forall e. e -> String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // overlay
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Semi-transparent overlay background
overlay :: forall w msg. Boolean -> HH.HTML w (TourMsg msg)
overlay closeOnClick =
  HH.div
    ( [ cls [ overlayClass ] ]
      <> if closeOnClick
         then [ HE.onClick \_ -> DismissTour ClickedOverlay ]
         else []
    )
    []

-- | Overlay CSS classes
overlayClass :: String
overlayClass = "fixed inset-0 bg-black/75 transition-opacity duration-300"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // spotlight
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spotlight cutout (positioned via JS)
-- |
-- | The actual positioning is handled by the runtime. This provides
-- | the visual element with proper styling for the cutout effect.
spotlight :: forall w i. Pixel -> Pixel -> HH.HTML w i
spotlight (Pixel padding) (Pixel radius) =
  HH.div
    [ cls [ "fixed pointer-events-none transition-all duration-300 ease-out" ]
    , HP.attr (HH.AttrName "data-tour-spotlight") "true"
    , HP.attr (HH.AttrName "data-padding") (show padding)
    , HP.attr (HH.AttrName "data-radius") (show radius)
    , HP.style $ "box-shadow: 0 0 0 9999px rgba(0, 0, 0, 0.75), 0 0 0 " 
                 <> show padding <> "px rgba(255, 255, 255, 0.1);"
                 <> " border-radius: " <> show radius <> "px;"
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // tooltip
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete tooltip component
tooltip :: forall w msg. TourState msg -> Step msg -> HH.HTML w (TourMsg msg)
tooltip state step =
  HH.div
    [ cls [ tooltipClass, placementClass step.placement.preferred.side ]
    , ARIA.role "tooltip"
    , HP.attr (HH.AttrName "data-tour-tooltip") "true"
    , HP.attr (HH.AttrName "data-placement") (sideString step.placement.preferred.side)
    , HP.tabIndex 0
    ]
    [ tooltipContent state step
    ]

-- | Placement-specific positioning class
placementClass :: Side -> String
placementClass = case _ of
  Top -> "bottom-full mb-3"
  Right -> "left-full ml-3"
  Bottom -> "top-full mt-3"
  Left -> "right-full mr-3"

-- | Convert side to string for data attribute
sideString :: Side -> String
sideString = case _ of
  Top -> "top"
  Right -> "right"
  Bottom -> "bottom"
  Left -> "left"

-- | Tooltip CSS classes
tooltipClass :: String
tooltipClass = 
  "absolute z-50 w-80 max-w-sm rounded-lg border bg-popover p-4 text-popover-foreground shadow-lg " <>
  "animate-in fade-in-0 zoom-in-95 duration-200"

-- | Inner tooltip content
tooltipContent :: forall w msg. TourState msg -> Step msg -> HH.HTML w (TourMsg msg)
tooltipContent state step =
  HH.div
    [ cls [ "space-y-4" ] ]
    [ tooltipHeader state step
    , tooltipBody step
    , tooltipFooter state step
    ]

-- | Tooltip header with title and close button
tooltipHeader :: forall w msg. TourState msg -> Step msg -> HH.HTML w (TourMsg msg)
tooltipHeader _state step =
  HH.div
    [ cls [ "flex items-start justify-between gap-2" ] ]
    [ case step.title of
        Just t -> HH.h3 [ cls [ "font-semibold leading-none tracking-tight" ] ] [ HH.text t ]
        Nothing -> HH.text ""
    , closeButton
    ]

-- | Tooltip body text
tooltipBody :: forall w i msg. Step msg -> HH.HTML w i
tooltipBody step =
  case step.body of
    Just b -> HH.p [ cls [ "text-sm text-muted-foreground" ] ] [ HH.text b ]
    Nothing -> HH.text ""

-- | Tooltip footer with progress and buttons
tooltipFooter :: forall w msg. TourState msg -> Step msg -> HH.HTML w (TourMsg msg)
tooltipFooter state step =
  HH.div
    [ cls [ "flex items-center justify-between gap-2" ] ]
    [ case progress state of
        Just p -> progressDots p
        Nothing -> HH.text ""
    , navigationButtons state step
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // progress
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Progress indicator with dots
progressDots :: forall w i. Progress -> HH.HTML w i
progressDots p =
  HH.div
    [ cls [ "flex items-center gap-1.5" ]
    , ARIA.label ("Step " <> show (progressCurrent p) <> " of " <> show (progressTotal p))
    ]
    (mapWithIndex renderDot (makeArray (progressTotal p)))
  where
  renderDot :: Int -> Unit -> HH.HTML w i
  renderDot idx _ =
    HH.div
      [ cls [ "w-1.5 h-1.5 rounded-full transition-colors"
            , if idx < progressCurrent p then "bg-primary" else "bg-muted"
            ]
      ]
      []
  
  makeArray :: Int -> Array Unit
  makeArray n = map (const unit) (range 0 (n - 1))
  
  range :: Int -> Int -> Array Int
  range start end = if start > end then [] else [start] <> range (start + 1) end

-- | Progress as fraction text (e.g., "2 of 5")
progressFraction :: forall w i. Progress -> HH.HTML w i
progressFraction p =
  HH.span
    [ cls [ "text-xs text-muted-foreground" ] ]
    [ HH.text $ show (progressCurrent p) <> " of " <> show (progressTotal p) ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // navigation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Navigation buttons based on step configuration
navigationButtons :: forall w msg. TourState msg -> Step msg -> HH.HTML w (TourMsg msg)
navigationButtons state step =
  HH.div
    [ cls [ "flex items-center gap-2" ] ]
    (map (renderButton state) step.buttons)

-- | Render a single button
renderButton :: forall w msg. TourState msg -> Button msg -> HH.HTML w (TourMsg msg)
renderButton state btn =
  HH.button
    [ cls [ buttonClasses btn.variant, focusRing ]
    , HP.type_ HP.ButtonButton
    , HE.onClick \_ -> actionToMsg btn.action
    , HP.disabled (isButtonDisabled state btn)
    ]
    [ HH.text btn.label ]

-- | Convert button action to tour message
actionToMsg :: forall msg. ButtonAction msg -> TourMsg msg
actionToMsg = case _ of
  ActionNext -> NextStep
  ActionPrev -> PrevStep
  ActionSkip -> DismissTour ClickedClose
  ActionComplete -> CompleteTour
  ActionGoTo sid -> GoToStepById sid
  ActionCustom m -> CustomAction m

-- | Check if button should be disabled
isButtonDisabled :: forall msg. TourState msg -> Button msg -> Boolean
isButtonDisabled state btn = case btn.action of
  ActionPrev -> isFirstStep state
  _ -> false

-- | CSS classes for button variants
buttonClasses :: ButtonVariant -> String
buttonClasses = case _ of
  Primary -> buttonPrimaryClass
  Secondary -> buttonSecondaryClass
  Text -> buttonTextClass

-- | Primary button classes
buttonPrimaryClass :: String
buttonPrimaryClass = 
  "inline-flex items-center justify-center rounded-md text-sm font-medium " <>
  "bg-primary text-primary-foreground hover:bg-primary/90 " <>
  "h-9 px-4 py-2 transition-colors"

-- | Secondary button classes
buttonSecondaryClass :: String
buttonSecondaryClass = 
  "inline-flex items-center justify-center rounded-md text-sm font-medium " <>
  "bg-secondary text-secondary-foreground hover:bg-secondary/80 " <>
  "h-9 px-4 py-2 transition-colors"

-- | Text button classes
buttonTextClass :: String
buttonTextClass = 
  "inline-flex items-center justify-center rounded-md text-sm font-medium " <>
  "text-muted-foreground hover:text-foreground hover:bg-accent " <>
  "h-9 px-3 py-2 transition-colors"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // close button
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Close button (X icon)
closeButton :: forall w msg. HH.HTML w (TourMsg msg)
closeButton =
  HH.button
    [ cls [ "rounded-sm opacity-70 ring-offset-background transition-opacity hover:opacity-100", focusRing ]
    , HP.type_ HP.ButtonButton
    , HE.onClick \_ -> DismissTour ClickedClose
    , ARIA.label "Close tour"
    ]
    [ closeIcon ]

-- | SVG namespace constant
svgNS :: HH.Namespace
svgNS = HH.Namespace "http://www.w3.org/2000/svg"

-- | X icon SVG
closeIcon :: forall w i. HH.HTML w i
closeIcon =
  HH.elementNS svgNS (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-4 w-4"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.elementNS svgNS (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "18"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "6"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    , HH.elementNS svgNS (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "6"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "18"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    ]
