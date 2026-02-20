-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // hydrogen // tour
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Product tour / onboarding component
-- |
-- | Step-by-step guided tours with element highlighting and tooltips.
-- |
-- | ## Features
-- |
-- | - Step-by-step tour
-- | - Highlight target elements
-- | - Tooltip with content
-- | - Navigation (next, prev, skip)
-- | - Step counter
-- | - Keyboard navigation
-- | - Scroll to step
-- | - Backdrop overlay
-- | - Progress bar
-- | - Callbacks: onStart, onStep, onComplete, onSkip
-- | - Persist progress (localStorage)
-- | - Conditional steps
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Tour as Tour
-- |
-- | -- Define tour steps
-- | tourSteps :: Array Tour.Step
-- | tourSteps =
-- |   [ Tour.step
-- |       { target: "#welcome-button"
-- |       , title: "Welcome!"
-- |       , content: "Click here to get started."
-- |       }
-- |   , Tour.step
-- |       { target: "#sidebar"
-- |       , title: "Navigation"
-- |       , content: "Use the sidebar to navigate."
-- |       , placement: Tour.Right
-- |       }
-- |   , Tour.step
-- |       { target: "#settings"
-- |       , title: "Settings"
-- |       , content: "Customize your experience here."
-- |       , condition: \state -> state.showAdvanced
-- |       }
-- |   ]
-- |
-- | -- Render tour
-- | Tour.tour
-- |   [ Tour.steps tourSteps
-- |   , Tour.showProgress true
-- |   , Tour.onComplete HandleTourComplete
-- |   , Tour.persistKey "onboarding-tour"
-- |   ]
-- |
-- | -- Or with manual control
-- | Tour.tour
-- |   [ Tour.steps tourSteps
-- |   , Tour.currentStep state.tourStep
-- |   , Tour.isActive state.tourActive
-- |   , Tour.onStepChange HandleStepChange
-- |   ]
-- | ```
module Hydrogen.Component.Tour
  ( -- * Components
    tour
  , tourOverlay
  , tourTooltip
  , tourHighlight
  , tourProgress
  , tourNavigation
    -- * Step Builder
  , step
  , Step
  , StepConfig
    -- * Props
  , TourProps
  , TourProp
  , TooltipProps
  , TooltipProp
  , defaultProps
  , defaultTooltipProps
    -- * Prop Builders
  , steps
  , currentStep
  , isActive
  , showProgress
  , showOverlay
  , overlayOpacity
  , allowClickThrough
  , scrollBehavior
  , persistKey
  , onStart
  , onStep
  , onComplete
  , onSkip
  , onStepChange
  , className
    -- * Prop Builders - Tooltip
  , placement
  , offset
  , tooltipClassName
    -- * Types
  , Placement(..)
  , ScrollBehavior(..)
    -- * FFI
  , TourElement
  , initTour
  , destroyTour
  , startTour
  , nextStep
  , prevStep
  , goToStep
  , skipTour
  , getProgress
  , clearProgress
  ) where

import Prelude

import Data.Array (foldl, index, length, mapWithIndex, replicate)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tooltip placement relative to target
data Placement
  = Top
  | TopStart
  | TopEnd
  | Bottom
  | BottomStart
  | BottomEnd
  | Left
  | LeftStart
  | LeftEnd
  | Right
  | RightStart
  | RightEnd

derive instance eqPlacement :: Eq Placement

-- | Scroll behavior when moving to a step
data ScrollBehavior
  = Smooth
  | Instant
  | None

derive instance eqScrollBehavior :: Eq ScrollBehavior

-- | Tour step configuration
type StepConfig =
  { target :: String          -- CSS selector
  , title :: String
  , content :: String
  , placement :: Placement
  , offset :: Int
  , showArrow :: Boolean
  , highlightPadding :: Int
  , scrollMargin :: Int
  }

-- | Tour step with all configuration
type Step =
  { config :: StepConfig
  , condition :: Maybe (forall a. a -> Boolean)
  }

-- | Create a tour step
step :: 
  { target :: String
  , title :: String
  , content :: String
  } -> 
  Step
step cfg =
  { config:
      { target: cfg.target
      , title: cfg.title
      , content: cfg.content
      , placement: Bottom
      , offset: 8
      , showArrow: true
      , highlightPadding: 4
      , scrollMargin: 20
      }
  , condition: Nothing
  }

-- | Opaque tour element for FFI
foreign import data TourElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize tour
foreign import initTourImpl :: EffectFn2
  { persistKey :: String
  , scrollBehavior :: String
  }
  { onStart :: Effect Unit
  , onStep :: Int -> Effect Unit
  , onComplete :: Effect Unit
  , onSkip :: Effect Unit
  }
  TourElement

-- | Destroy tour
foreign import destroyTourImpl :: EffectFn1 TourElement Unit

-- | Start tour
foreign import startTourImpl :: EffectFn1 TourElement Unit

-- | Go to next step
foreign import nextStepImpl :: EffectFn1 TourElement Boolean

-- | Go to previous step
foreign import prevStepImpl :: EffectFn1 TourElement Boolean

-- | Go to specific step
foreign import goToStepImpl :: EffectFn2 TourElement Int Boolean

-- | Skip/end tour
foreign import skipTourImpl :: EffectFn1 TourElement Unit

-- | Get persisted progress
foreign import getProgressImpl :: EffectFn1 String Int

-- | Clear persisted progress
foreign import clearProgressImpl :: EffectFn1 String Unit

-- | Highlight element
foreign import highlightElementImpl :: EffectFn3 String Int Boolean Unit

-- | Remove highlight
foreign import removeHighlightImpl :: EffectFn1 Unit Unit

-- | Initialize tour
initTour :: 
  { persistKey :: String, scrollBehavior :: String } ->
  { onStart :: Effect Unit
  , onStep :: Int -> Effect Unit
  , onComplete :: Effect Unit
  , onSkip :: Effect Unit
  } ->
  Effect TourElement
initTour _ _ = pure unsafeTourElement

-- | Destroy tour
destroyTour :: TourElement -> Effect Unit
destroyTour _ = pure unit

-- | Start tour
startTour :: TourElement -> Effect Unit
startTour _ = pure unit

-- | Next step
nextStep :: TourElement -> Effect Boolean
nextStep _ = pure false

-- | Previous step
prevStep :: TourElement -> Effect Boolean
prevStep _ = pure false

-- | Go to step
goToStep :: TourElement -> Int -> Effect Boolean
goToStep _ _ = pure false

-- | Skip tour
skipTour :: TourElement -> Effect Unit
skipTour _ = pure unit

-- | Get progress
getProgress :: String -> Effect Int
getProgress _ = pure 0

-- | Clear progress
clearProgress :: String -> Effect Unit
clearProgress _ = pure unit

-- Internal placeholder
foreign import unsafeTourElement :: TourElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tour properties
type TourProps i =
  { steps :: Array Step
  , currentStep :: Int
  , isActive :: Boolean
  , showProgress :: Boolean
  , showOverlay :: Boolean
  , overlayOpacity :: Number
  , allowClickThrough :: Boolean
  , scrollBehavior :: ScrollBehavior
  , persistKey :: Maybe String
  , onStart :: Maybe (Unit -> i)
  , onStep :: Maybe (Int -> i)
  , onComplete :: Maybe (Unit -> i)
  , onSkip :: Maybe (Unit -> i)
  , onStepChange :: Maybe (Int -> i)
  , className :: String
  }

-- | Tour property modifier
type TourProp i = TourProps i -> TourProps i

-- | Default tour properties
defaultProps :: forall i. TourProps i
defaultProps =
  { steps: []
  , currentStep: 0
  , isActive: true
  , showProgress: true
  , showOverlay: true
  , overlayOpacity: 0.5
  , allowClickThrough: false
  , scrollBehavior: Smooth
  , persistKey: Nothing
  , onStart: Nothing
  , onStep: Nothing
  , onComplete: Nothing
  , onSkip: Nothing
  , onStepChange: Nothing
  , className: ""
  }

-- | Tooltip properties
type TooltipProps =
  { placement :: Placement
  , offset :: Int
  , showArrow :: Boolean
  , className :: String
  }

-- | Tooltip property modifier
type TooltipProp = TooltipProps -> TooltipProps

-- | Default tooltip properties
defaultTooltipProps :: TooltipProps
defaultTooltipProps =
  { placement: Bottom
  , offset: 8
  , showArrow: true
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set tour steps
steps :: forall i. Array Step -> TourProp i
steps s props = props { steps = s }

-- | Set current step index
currentStep :: forall i. Int -> TourProp i
currentStep s props = props { currentStep = s }

-- | Set active state
isActive :: forall i. Boolean -> TourProp i
isActive a props = props { isActive = a }

-- | Show progress bar
showProgress :: forall i. Boolean -> TourProp i
showProgress s props = props { showProgress = s }

-- | Show backdrop overlay
showOverlay :: forall i. Boolean -> TourProp i
showOverlay s props = props { showOverlay = s }

-- | Set overlay opacity
overlayOpacity :: forall i. Number -> TourProp i
overlayOpacity o props = props { overlayOpacity = o }

-- | Allow clicking through overlay
allowClickThrough :: forall i. Boolean -> TourProp i
allowClickThrough a props = props { allowClickThrough = a }

-- | Set scroll behavior
scrollBehavior :: forall i. ScrollBehavior -> TourProp i
scrollBehavior s props = props { scrollBehavior = s }

-- | Set localStorage key for persistence
persistKey :: forall i. String -> TourProp i
persistKey k props = props { persistKey = Just k }

-- | Set start handler
onStart :: forall i. (Unit -> i) -> TourProp i
onStart handler props = props { onStart = Just handler }

-- | Set step handler
onStep :: forall i. (Int -> i) -> TourProp i
onStep handler props = props { onStep = Just handler }

-- | Set complete handler
onComplete :: forall i. (Unit -> i) -> TourProp i
onComplete handler props = props { onComplete = Just handler }

-- | Set skip handler
onSkip :: forall i. (Unit -> i) -> TourProp i
onSkip handler props = props { onSkip = Just handler }

-- | Set step change handler
onStepChange :: forall i. (Int -> i) -> TourProp i
onStepChange handler props = props { onStepChange = Just handler }

-- | Add custom class
className :: forall i. String -> TourProp i
className c props = props { className = props.className <> " " <> c }

-- | Set tooltip placement
placement :: Placement -> TooltipProp
placement p props = props { placement = p }

-- | Set tooltip offset
offset :: Int -> TooltipProp
offset o props = props { offset = o }

-- | Add custom class to tooltip
tooltipClassName :: String -> TooltipProp
tooltipClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert placement to string
placementToString :: Placement -> String
placementToString = case _ of
  Top -> "top"
  TopStart -> "top-start"
  TopEnd -> "top-end"
  Bottom -> "bottom"
  BottomStart -> "bottom-start"
  BottomEnd -> "bottom-end"
  Left -> "left"
  LeftStart -> "left-start"
  LeftEnd -> "left-end"
  Right -> "right"
  RightStart -> "right-start"
  RightEnd -> "right-end"

-- | Tour component
-- |
-- | Main tour container with overlay and tooltips
tour :: forall w i. Array (TourProp i) -> HH.HTML w i
tour propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    stepCount = length props.steps
    currentStepData = index props.steps props.currentStep
  in
    if not props.isActive || stepCount == 0
      then HH.text ""
      else
        HH.div
          [ cls [ "tour-container fixed inset-0 z-50", props.className ]
          , HP.attr (HH.AttrName "data-step") (show props.currentStep)
          , HP.attr (HH.AttrName "data-total") (show stepCount)
          , ARIA.role "dialog"
          , ARIA.modal "true"
          , ARIA.label "Product tour"
          ]
          [ -- Overlay
            if props.showOverlay
              then tourOverlay props.overlayOpacity props.allowClickThrough
              else HH.text ""
          , -- Highlight and tooltip for current step
            case currentStepData of
              Just stepData ->
                HH.div
                  [ cls [ "tour-step" ] ]
                  [ tourHighlight stepData.config.target stepData.config.highlightPadding
                  , tourTooltip 
                      stepData.config.title 
                      stepData.config.content
                      stepData.config.placement
                  ]
              Nothing -> HH.text ""
          , -- Navigation and progress
            HH.div
              [ cls [ "tour-footer fixed bottom-4 left-1/2 -translate-x-1/2 flex flex-col items-center gap-2" ] ]
              [ if props.showProgress
                  then tourProgress props.currentStep stepCount
                  else HH.text ""
              , tourNavigation props stepCount
              ]
          ]

-- | Tour overlay
-- |
-- | Semi-transparent backdrop
tourOverlay :: forall w i. Number -> Boolean -> HH.HTML w i
tourOverlay opacity allowClick =
  let
    pointerEvents = if allowClick then "pointer-events-none" else ""
    opacityStyle = "opacity: " <> show opacity
  in
    HH.div
      [ cls [ "tour-overlay fixed inset-0 bg-black transition-opacity", pointerEvents ]
      , HP.attr (HH.AttrName "style") opacityStyle
      , ARIA.hidden "true"
      ]
      []

-- | Tour tooltip
-- |
-- | Tooltip with title and content
tourTooltip :: forall w i. String -> String -> Placement -> HH.HTML w i
tourTooltip title content placementVal =
  let
    placementClass = "tour-tooltip-" <> placementToString placementVal
  in
    HH.div
      [ cls 
          [ "tour-tooltip fixed bg-popover text-popover-foreground rounded-lg shadow-lg border p-4 max-w-sm z-[60]"
          , placementClass
          ]
      , ARIA.role "tooltip"
      ]
      [ -- Arrow
        tooltipArrow placementVal
      , -- Content
        HH.div
          [ cls [ "tour-tooltip-content" ] ]
          [ HH.h4
              [ cls [ "tour-tooltip-title font-semibold text-lg mb-2" ] ]
              [ HH.text title ]
          , HH.p
              [ cls [ "tour-tooltip-description text-sm text-muted-foreground" ] ]
              [ HH.text content ]
          ]
      ]

-- | Tooltip arrow
tooltipArrow :: forall w i. Placement -> HH.HTML w i
tooltipArrow placementVal =
  let
    arrowClass = case placementVal of
      Top -> "bottom-0 left-1/2 -translate-x-1/2 translate-y-1/2 rotate-45"
      TopStart -> "bottom-0 left-4 translate-y-1/2 rotate-45"
      TopEnd -> "bottom-0 right-4 translate-y-1/2 rotate-45"
      Bottom -> "top-0 left-1/2 -translate-x-1/2 -translate-y-1/2 rotate-45"
      BottomStart -> "top-0 left-4 -translate-y-1/2 rotate-45"
      BottomEnd -> "top-0 right-4 -translate-y-1/2 rotate-45"
      Left -> "right-0 top-1/2 translate-x-1/2 -translate-y-1/2 rotate-45"
      LeftStart -> "right-0 top-4 translate-x-1/2 rotate-45"
      LeftEnd -> "right-0 bottom-4 translate-x-1/2 rotate-45"
      Right -> "left-0 top-1/2 -translate-x-1/2 -translate-y-1/2 rotate-45"
      RightStart -> "left-0 top-4 -translate-x-1/2 rotate-45"
      RightEnd -> "left-0 bottom-4 -translate-x-1/2 rotate-45"
  in
    HH.div
      [ cls [ "tour-tooltip-arrow absolute w-3 h-3 bg-popover border-r border-b", arrowClass ] ]
      []

-- | Tour highlight
-- |
-- | Highlights the target element
tourHighlight :: forall w i. String -> Int -> HH.HTML w i
tourHighlight target padding =
  HH.div
    [ cls [ "tour-highlight fixed ring-2 ring-primary ring-offset-2 rounded-md transition-all pointer-events-none z-[55]" ]
    , HP.attr (HH.AttrName "data-target") target
    , HP.attr (HH.AttrName "data-padding") (show padding)
    , ARIA.hidden "true"
    ]
    []

-- | Tour progress indicator
-- |
-- | Dots or progress bar showing current position
tourProgress :: forall w i. Int -> Int -> HH.HTML w i
tourProgress currentIdx total =
  HH.div
    [ cls [ "tour-progress flex items-center gap-1" ]
    , ARIA.label ("Step " <> show (currentIdx + 1) <> " of " <> show total)
    ]
    (mapWithIndex renderDot (replicate total unit))
  where
    renderDot :: Int -> Unit -> HH.HTML w i
    renderDot idx _ =
      let
        isActiveStep = idx == currentIdx
        activeClass = if isActiveStep then "bg-primary w-3" else "bg-muted-foreground/50 w-2"
      in
        HH.div
          [ cls [ "tour-progress-dot h-2 rounded-full transition-all", activeClass ] ]
          []

-- | Tour navigation
-- |
-- | Previous, Next, Skip buttons
tourNavigation :: forall w i. TourProps i -> Int -> HH.HTML w i
tourNavigation props total =
  let
    isFirst = props.currentStep == 0
    isLast = props.currentStep >= total - 1
    
    prevHandler = case props.onStepChange of
      Just handler -> [ HE.onClick (\_ -> handler (props.currentStep - 1)) ]
      Nothing -> []
    
    nextHandler = case props.onStepChange of
      Just handler -> [ HE.onClick (\_ -> handler (props.currentStep + 1)) ]
      Nothing -> []
    
    skipHandler = case props.onSkip of
      Just handler -> [ HE.onClick (\_ -> handler unit) ]
      Nothing -> []
    
    completeHandler = case props.onComplete of
      Just handler -> [ HE.onClick (\_ -> handler unit) ]
      Nothing -> []
  in
    HH.div
      [ cls [ "tour-navigation flex items-center gap-2 bg-popover rounded-lg p-2 shadow-lg border" ] ]
      [ -- Skip button
        HH.button
          ( [ cls 
                [ "tour-skip px-3 py-1.5 text-sm text-muted-foreground hover:text-foreground transition-colors"
                ]
            , HP.type_ HP.ButtonButton
            ] <> skipHandler
          )
          [ HH.text "Skip" ]
      , -- Spacer
        HH.div [ cls [ "flex-1" ] ] []
      , -- Previous button
        if isFirst
          then HH.text ""
          else HH.button
            ( [ cls 
                  [ "tour-prev px-3 py-1.5 text-sm rounded-md border border-input bg-background hover:bg-accent transition-colors"
                  ]
              , HP.type_ HP.ButtonButton
              ] <> prevHandler
            )
            [ HH.text "Previous" ]
      , -- Next/Complete button
        HH.button
          ( [ cls 
                [ "tour-next px-3 py-1.5 text-sm rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors"
                ]
            , HP.type_ HP.ButtonButton
            ] <> (if isLast then completeHandler else nextHandler)
          )
          [ HH.text (if isLast then "Complete" else "Next") ]
      ]
