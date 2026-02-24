-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // stepper
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Multi-step wizard/stepper component
-- |
-- | Step indicators and navigation for multi-step processes.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Stepper as Stepper
-- |
-- | -- Basic stepper
-- | Stepper.stepper
-- |   [ Stepper.steps
-- |       [ Stepper.step { label: "Account", description: "Create your account" }
-- |       , Stepper.step { label: "Profile", description: "Add your details" }
-- |       , Stepper.step { label: "Confirm", description: "Review and submit" }
-- |       ]
-- |   , Stepper.currentStep 1
-- |   ]
-- |
-- | -- Vertical stepper with content
-- | Stepper.stepper
-- |   [ Stepper.orientation Stepper.Vertical
-- |   , Stepper.steps mySteps
-- |   , Stepper.currentStep 2
-- |   , Stepper.showContent true
-- |   ]
-- |   [ stepOneContent, stepTwoContent, stepThreeContent ]
-- |
-- | -- Non-linear navigation
-- | Stepper.stepper
-- |   [ Stepper.steps mySteps
-- |   , Stepper.linear false
-- |   , Stepper.onStepClick HandleStepClick
-- |   ]
-- |
-- | -- With navigation buttons
-- | Stepper.stepperWithNav
-- |   [ Stepper.steps mySteps
-- |   , Stepper.currentStep current
-- |   , Stepper.onNext HandleNext
-- |   , Stepper.onPrevious HandlePrevious
-- |   ]
-- |   stepContent
-- | ```
module Hydrogen.Component.Stepper
  ( -- * Stepper Components
    stepper
  , stepperWithNav
  , stepIndicator
  , stepConnector
  , stepNavigation
    -- * Step Types
  , Step
  , StepStatus(Completed, Current, Upcoming, Error)
  , step
  , stepWithIcon
    -- * Props
  , StepperProps
  , StepperProp
  , defaultProps
    -- * Prop Builders
  , steps
  , currentStep
  , orientation
  , linear
  , showContent
  , showNumbers
  , clickable
  , className
  , onStepClick
  , onNext
  , onPrevious
  , onComplete
  , validateStep
    -- * Types
  , Orientation(Horizontal, Vertical)
  ) where

import Prelude

import Data.Array (foldl, length, (!!))
import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Stepper orientation
data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

-- | Step status
data StepStatus
  = Completed
  | Current
  | Upcoming
  | Error

derive instance eqStepStatus :: Eq StepStatus

-- | Step definition
type Step =
  { label :: String
  , description :: Maybe String
  , icon :: Maybe String  -- Optional custom icon/character
  , optional :: Boolean
  , status :: StepStatus
  }

-- | Create a simple step
step :: { label :: String, description :: String } -> Step
step cfg =
  { label: cfg.label
  , description: Just cfg.description
  , icon: Nothing
  , optional: false
  , status: Upcoming
  }

-- | Create a step with custom icon
stepWithIcon :: { label :: String, description :: String, icon :: String } -> Step
stepWithIcon cfg =
  { label: cfg.label
  , description: Just cfg.description
  , icon: Just cfg.icon
  , optional: false
  , status: Upcoming
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type StepperProps i =
  { steps :: Array Step
  , currentStep :: Int
  , orientation :: Orientation
  , linear :: Boolean
  , showContent :: Boolean
  , showNumbers :: Boolean
  , clickable :: Boolean
  , className :: String
  , onStepClick :: Maybe (Int -> i)
  , onNext :: Maybe (MouseEvent -> i)
  , onPrevious :: Maybe (MouseEvent -> i)
  , onComplete :: Maybe (MouseEvent -> i)
  , validateStep :: Maybe (Int -> Boolean)
  , nextLabel :: String
  , previousLabel :: String
  , completeLabel :: String
  }

type StepperProp i = StepperProps i -> StepperProps i

defaultProps :: forall i. StepperProps i
defaultProps =
  { steps: []
  , currentStep: 0
  , orientation: Horizontal
  , linear: true
  , showContent: false
  , showNumbers: true
  , clickable: true
  , className: ""
  , onStepClick: Nothing
  , onNext: Nothing
  , onPrevious: Nothing
  , onComplete: Nothing
  , validateStep: Nothing
  , nextLabel: "Next"
  , previousLabel: "Previous"
  , completeLabel: "Complete"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set steps
steps :: forall i. Array Step -> StepperProp i
steps s props = props { steps = s }

-- | Set current step (0-indexed)
currentStep :: forall i. Int -> StepperProp i
currentStep s props = props { currentStep = s }

-- | Set orientation
orientation :: forall i. Orientation -> StepperProp i
orientation o props = props { orientation = o }

-- | Set linear mode (must complete steps in order)
linear :: forall i. Boolean -> StepperProp i
linear l props = props { linear = l }

-- | Show step content inline
showContent :: forall i. Boolean -> StepperProp i
showContent s props = props { showContent = s }

-- | Show step numbers
showNumbers :: forall i. Boolean -> StepperProp i
showNumbers s props = props { showNumbers = s }

-- | Allow clicking on steps to navigate
clickable :: forall i. Boolean -> StepperProp i
clickable c props = props { clickable = c }

-- | Add custom class
className :: forall i. String -> StepperProp i
className c props = props { className = props.className <> " " <> c }

-- | Handle step click
onStepClick :: forall i. (Int -> i) -> StepperProp i
onStepClick handler props = props { onStepClick = Just handler }

-- | Handle next button click
onNext :: forall i. (MouseEvent -> i) -> StepperProp i
onNext handler props = props { onNext = Just handler }

-- | Handle previous button click
onPrevious :: forall i. (MouseEvent -> i) -> StepperProp i
onPrevious handler props = props { onPrevious = Just handler }

-- | Handle complete button click
onComplete :: forall i. (MouseEvent -> i) -> StepperProp i
onComplete handler props = props { onComplete = Just handler }

-- | Set validation function for steps
validateStep :: forall i. (Int -> Boolean) -> StepperProp i
validateStep v props = props { validateStep = Just v }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get status-based classes for indicator
statusClasses :: StepStatus -> String
statusClasses = case _ of
  Completed -> "bg-primary text-primary-foreground border-primary"
  Current -> "bg-primary text-primary-foreground border-primary ring-2 ring-primary ring-offset-2"
  Upcoming -> "bg-background text-muted-foreground border-muted"
  Error -> "bg-destructive text-destructive-foreground border-destructive"

-- | Get status-based classes for label
labelClasses :: StepStatus -> String
labelClasses = case _ of
  Completed -> "text-primary font-medium"
  Current -> "text-primary font-semibold"
  Upcoming -> "text-muted-foreground"
  Error -> "text-destructive font-medium"

-- | Get connector classes based on completion
connectorClasses :: Boolean -> String
connectorClasses completed =
  if completed
    then "bg-primary"
    else "bg-muted"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Determine step status based on current step
getStepStatus :: Int -> Int -> StepStatus
getStepStatus idx currentIdx
  | idx < currentIdx = Completed
  | idx == currentIdx = Current
  | otherwise = Upcoming

-- | Main stepper component (indicators only)
stepper :: forall w i. Array (StepperProp i) -> HH.HTML w i
stepper propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    totalSteps = length props.steps
    
    containerClasses = case props.orientation of
      Horizontal -> "flex items-start w-full"
      Vertical -> "flex flex-col"
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , ARIA.role "list"
      , ARIA.label "Progress steps"
      ]
      ( Array.mapWithIndex (renderStepWithConnector props totalSteps) props.steps )

-- | Stepper with navigation buttons
stepperWithNav :: forall w i. Array (StepperProp i) -> Array (HH.HTML w i) -> HH.HTML w i
stepperWithNav propMods content =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    totalSteps = length props.steps
    currentContent = content !! props.currentStep
  in
    HH.div
      [ cls [ "flex flex-col gap-6", props.className ] ]
      [ -- Step indicators
        stepper propMods
        -- Current step content
      , case currentContent of
          Just c -> 
            HH.div
              [ cls [ "min-h-[200px]" ] ]
              [ c ]
          Nothing -> HH.text ""
        -- Navigation buttons
      , stepNavigation props totalSteps
      ]

-- | Render step with connector
renderStepWithConnector :: forall w i. StepperProps i -> Int -> Int -> Step -> HH.HTML w i
renderStepWithConnector props totalSteps idx stepDef =
  let
    status = getStepStatus idx props.currentStep
    isLast = idx == totalSteps - 1
    canClick = props.clickable && (not props.linear || idx <= props.currentStep)
    
    clickHandler = 
      if canClick
        then case props.onStepClick of
          Just handler -> [ HE.onClick (\_ -> handler idx) ]
          Nothing -> []
        else []
  in
    case props.orientation of
      Horizontal ->
        HH.div
          [ cls [ "flex items-center", if isLast then "" else "flex-1" ] ]
          [ -- Step indicator
            HH.div
              [ cls [ "flex flex-col items-center gap-2" ] ]
              [ HH.button
                  ( [ cls 
                        [ "flex items-center justify-center w-10 h-10 rounded-full border-2 transition-all"
                        , statusClasses status
                        , if canClick then "cursor-pointer hover:opacity-80" else "cursor-default"
                        ]
                    , HP.disabled (not canClick)
                    , ARIA.role "listitem"
                    , HP.attr (HH.AttrName "aria-current") (if status == Current then "step" else "false")
                    ] <> clickHandler
                  )
                  [ stepIndicatorContent props idx stepDef status ]
              , HH.div
                  [ cls [ "text-center" ] ]
                  [ HH.div
                      [ cls [ "text-sm", labelClasses status ] ]
                      [ HH.text stepDef.label ]
                  , case stepDef.description of
                      Just desc ->
                        HH.div
                          [ cls [ "text-xs text-muted-foreground mt-0.5" ] ]
                          [ HH.text desc ]
                      Nothing -> HH.text ""
                  ]
              ]
            -- Connector
          , if isLast
              then HH.text ""
              else stepConnector props.orientation (idx < props.currentStep)
          ]
      Vertical ->
        HH.div
          [ cls [ "flex gap-4" ] ]
          [ -- Indicator column
            HH.div
              [ cls [ "flex flex-col items-center" ] ]
              [ HH.button
                  ( [ cls 
                        [ "flex items-center justify-center w-10 h-10 rounded-full border-2 transition-all"
                        , statusClasses status
                        , if canClick then "cursor-pointer hover:opacity-80" else "cursor-default"
                        ]
                    , HP.disabled (not canClick)
                    , ARIA.role "listitem"
                    ] <> clickHandler
                  )
                  [ stepIndicatorContent props idx stepDef status ]
              , if isLast
                  then HH.text ""
                  else stepConnector props.orientation (idx < props.currentStep)
              ]
            -- Content column
          , HH.div
              [ cls [ "flex-1 pb-8" ] ]
              [ HH.div
                  [ cls [ "text-sm font-medium", labelClasses status ] ]
                  [ HH.text stepDef.label ]
              , case stepDef.description of
                  Just desc ->
                    HH.div
                      [ cls [ "text-xs text-muted-foreground mt-1" ] ]
                      [ HH.text desc ]
                  Nothing -> HH.text ""
              , if stepDef.optional
                  then 
                    HH.div
                      [ cls [ "text-xs text-muted-foreground italic mt-1" ] ]
                      [ HH.text "Optional" ]
                  else HH.text ""
              ]
          ]

-- | Step indicator content (number, icon, or check)
stepIndicatorContent :: forall w i. StepperProps i -> Int -> Step -> StepStatus -> HH.HTML w i
stepIndicatorContent props idx stepDef status =
  case status of
    Completed -> checkIcon
    Error -> errorIcon
    _ ->
      case stepDef.icon of
        Just ic -> HH.span_ [ HH.text ic ]
        Nothing ->
          if props.showNumbers
            then HH.span_ [ HH.text (show (idx + 1)) ]
            else HH.span [ cls [ "w-2 h-2 rounded-full bg-current" ] ] []

-- | Step indicator circle
stepIndicator :: forall w i. Int -> StepStatus -> Boolean -> HH.HTML w i
stepIndicator idx status showNumber =
  HH.div
    [ cls 
        [ "flex items-center justify-center w-10 h-10 rounded-full border-2"
        , statusClasses status
        ]
    ]
    [ case status of
        Completed -> checkIcon
        Error -> errorIcon
        _ ->
          if showNumber
            then HH.span_ [ HH.text (show (idx + 1)) ]
            else HH.span [ cls [ "w-2 h-2 rounded-full bg-current" ] ] []
    ]

-- | Step connector line
stepConnector :: forall w i. Orientation -> Boolean -> HH.HTML w i
stepConnector orient completed =
  case orient of
    Horizontal ->
      HH.div
        [ cls [ "flex-1 h-0.5 mx-2 transition-colors", connectorClasses completed ] ]
        []
    Vertical ->
      HH.div
        [ cls [ "w-0.5 flex-1 min-h-[2rem] transition-colors", connectorClasses completed ] ]
        []

-- | Step navigation buttons
stepNavigation :: forall w i. StepperProps i -> Int -> HH.HTML w i
stepNavigation props totalSteps =
  let
    isFirst = props.currentStep == 0
    isLast = props.currentStep >= totalSteps - 1
    
    canGoNext = case props.validateStep of
      Just validate -> validate props.currentStep
      Nothing -> true
  in
    HH.div
      [ cls [ "flex justify-between pt-4" ] ]
      [ -- Previous button
        HH.button
          ( [ cls 
                [ "inline-flex items-center justify-center rounded-md text-sm font-medium h-10 px-4 py-2"
                , "border border-input bg-background hover:bg-accent hover:text-accent-foreground"
                , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
                , if isFirst then "opacity-50 cursor-not-allowed" else ""
                ]
            , HP.disabled isFirst
            ] <> case props.onPrevious of
              Just handler -> if isFirst then [] else [ HE.onClick handler ]
              Nothing -> []
          )
          [ HH.text props.previousLabel ]
        -- Next/Complete button
      , if isLast
          then
            HH.button
              ( [ cls 
                    [ "inline-flex items-center justify-center rounded-md text-sm font-medium h-10 px-4 py-2"
                    , "bg-primary text-primary-foreground hover:bg-primary/90"
                    , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
                    ]
                ] <> case props.onComplete of
                  Just handler -> [ HE.onClick handler ]
                  Nothing -> []
              )
              [ HH.text props.completeLabel ]
          else
            HH.button
              ( [ cls 
                    [ "inline-flex items-center justify-center rounded-md text-sm font-medium h-10 px-4 py-2"
                    , "bg-primary text-primary-foreground hover:bg-primary/90"
                    , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
                    , if not canGoNext then "opacity-50 cursor-not-allowed" else ""
                    ]
                , HP.disabled (not canGoNext)
                ] <> case props.onNext of
                  Just handler -> if canGoNext then [ HE.onClick handler ] else []
                  Nothing -> []
              )
              [ HH.text props.nextLabel ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check icon for completed steps
checkIcon :: forall w i. HH.HTML w i
checkIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "3"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "20 6 9 17 4 12" ]
        []
    ]

-- | Error icon for error steps
errorIcon :: forall w i. HH.HTML w i
errorIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "3"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "18"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "6"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "6"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "18"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    ]


