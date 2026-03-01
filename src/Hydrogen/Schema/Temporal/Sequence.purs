-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // temporal // sequence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sequence — Tour and onboarding sequence configuration atoms.
-- |
-- | ## Sequential UI Patterns
-- |
-- | Many UI patterns involve guiding users through a sequence:
-- | - **Product tours**: Highlight features for new users
-- | - **Onboarding flows**: Step-by-step account setup
-- | - **Tutorials**: Interactive learning sequences
-- | - **Wizards**: Multi-step form completion
-- |
-- | ## Tour Step Model
-- |
-- | Each step in a sequence consists of:
-- | - **Target**: Element to highlight (via selector)
-- | - **Content**: Explanatory text or rich content
-- | - **Placement**: Where to position the tooltip/popover
-- | - **Actions**: Available navigation (next, prev, skip, complete)
-- |
-- | ## State Machine
-- |
-- | A tour/sequence is a state machine tracking:
-- | - Current step index
-- | - Active/inactive state
-- | - Completion status per step
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Geometry.Position (Placement)
-- | - Hydrogen.Schema.Navigation.Index (Index, IndexedPosition)
-- | - Prelude (Eq, Ord, Show)
-- |
-- | ## Dependents
-- | - Tour component compound
-- | - Onboarding flow manager
-- | - Tutorial system
-- | - Wizard navigation

module Hydrogen.Schema.Temporal.Sequence
  ( -- * Element Selector
    ElementSelector(SelectorId, SelectorClass, SelectorData, SelectorCustom)
  , selectorId
  , selectorClass
  , selectorData
  , selectorCustom
  , selectorToString
  
  -- * Tour Step
  , TourStep
  , tourStep
  , stepTarget
  , stepContent
  , stepPlacement
  , stepTitle
  
  -- * Tour State
  , TourState
  , tourState
  , tourStateEmpty
  , tourStateFromSteps
  
  -- * State Accessors
  , tourSteps
  , tourCurrentStep
  , tourIsActive
  , tourCurrentStepData
  , tourStepCount
  , tourProgress
  
  -- * State Predicates
  , isFirstStep
  , isLastStep
  , canGoNext
  , canGoPrev
  , isTourComplete
  , isTourEmpty
  
  -- * State Transitions
  , startTour
  , endTour
  , nextStep
  , prevStep
  , goToStep
  , completeTour
  
  -- * Tour Configuration
  , TourConfig
  , tourConfig
  , configShowProgress
  , configShowSkip
  , configAllowClickOutside
  , configScrollToElement
  
  -- * Common Presets
  , tourConfigDefault
  , tourConfigMinimal
  , tourConfigStrict
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , (+)
  , (-)
  , (/)
  , (<)
  , (>)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Array (length, index) as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Geometry.Position (Placement)
import Hydrogen.Schema.Navigation.Index (Index, index, unwrapIndex)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // element // selector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selector for targeting DOM elements.
-- |
-- | Provides type-safe element targeting without raw CSS selector strings:
-- |
-- | - **SelectorId**: Target by element ID (#myElement)
-- | - **SelectorClass**: Target by class name (.myClass)
-- | - **SelectorData**: Target by data attribute (data-tour="step1")
-- | - **SelectorCustom**: Escape hatch for complex selectors
data ElementSelector
  = SelectorId String       -- ^ Target by ID
  | SelectorClass String    -- ^ Target by class
  | SelectorData String String  -- ^ Target by data attribute (key, value)
  | SelectorCustom String   -- ^ Raw CSS selector (escape hatch)

derive instance eqElementSelector :: Eq ElementSelector
derive instance ordElementSelector :: Ord ElementSelector

instance showElementSelector :: Show ElementSelector where
  show (SelectorId s) = "(SelectorId " <> show s <> ")"
  show (SelectorClass s) = "(SelectorClass " <> show s <> ")"
  show (SelectorData k v) = "(SelectorData " <> show k <> " " <> show v <> ")"
  show (SelectorCustom s) = "(SelectorCustom " <> show s <> ")"

-- | Create an ID selector.
-- |
-- | ```purescript
-- | selectorId "main-button" -- targets #main-button
-- | ```
selectorId :: String -> ElementSelector
selectorId = SelectorId

-- | Create a class selector.
-- |
-- | ```purescript
-- | selectorClass "feature-card" -- targets .feature-card
-- | ```
selectorClass :: String -> ElementSelector
selectorClass = SelectorClass

-- | Create a data attribute selector.
-- |
-- | ```purescript
-- | selectorData "tour" "step-1" -- targets [data-tour="step-1"]
-- | ```
selectorData :: String -> String -> ElementSelector
selectorData = SelectorData

-- | Create a custom CSS selector.
-- |
-- | Use only when structured selectors are insufficient.
selectorCustom :: String -> ElementSelector
selectorCustom = SelectorCustom

-- | Convert selector to CSS selector string.
-- |
-- | For use by runtime when querying DOM.
selectorToString :: ElementSelector -> String
selectorToString (SelectorId s) = "#" <> s
selectorToString (SelectorClass s) = "." <> s
selectorToString (SelectorData k v) = "[data-" <> k <> "=\"" <> v <> "\"]"
selectorToString (SelectorCustom s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // tour // step
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single step in a tour sequence.
-- |
-- | Defines what element to highlight and what content to display.
type TourStep =
  { target :: ElementSelector  -- ^ Element to highlight
  , content :: String          -- ^ Explanatory content
  , placement :: Placement     -- ^ Tooltip placement relative to target
  , title :: Maybe String      -- ^ Optional step title
  }

-- | Create a tour step with required fields.
tourStep :: ElementSelector -> String -> Placement -> TourStep
tourStep t c p = { target: t, content: c, placement: p, title: Nothing }

-- | Get step target selector.
stepTarget :: TourStep -> ElementSelector
stepTarget s = s.target

-- | Get step content.
stepContent :: TourStep -> String
stepContent s = s.content

-- | Get step placement.
stepPlacement :: TourStep -> Placement
stepPlacement s = s.placement

-- | Get step title.
stepTitle :: TourStep -> Maybe String
stepTitle s = s.title

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // tour // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete state of a tour sequence.
-- |
-- | Tracks all steps and current navigation position.
type TourState =
  { steps :: Array TourStep   -- ^ All steps in the tour
  , currentStep :: Index      -- ^ Current step index
  , isActive :: Boolean       -- ^ Is tour currently running
  }

-- | Create a tour state with explicit values.
tourState :: Array TourStep -> Index -> Boolean -> TourState
tourState ss idx active = { steps: ss, currentStep: idx, isActive: active }

-- | Create an empty, inactive tour state.
tourStateEmpty :: TourState
tourStateEmpty = { steps: [], currentStep: index 0, isActive: false }

-- | Create a tour state from steps, starting at first step.
-- |
-- | Tour starts inactive; call `startTour` to begin.
tourStateFromSteps :: Array TourStep -> TourState
tourStateFromSteps ss = tourState ss (index 0) false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // state // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all tour steps.
tourSteps :: TourState -> Array TourStep
tourSteps ts = ts.steps

-- | Get current step index.
tourCurrentStep :: TourState -> Index
tourCurrentStep ts = ts.currentStep

-- | Is tour currently active?
tourIsActive :: TourState -> Boolean
tourIsActive ts = ts.isActive

-- | Get current step data (if valid).
tourCurrentStepData :: TourState -> Maybe TourStep
tourCurrentStepData ts = Array.index ts.steps (unwrapIndex ts.currentStep)

-- | Get total number of steps.
tourStepCount :: TourState -> Int
tourStepCount ts = Array.length ts.steps

-- | Get progress as ratio (0.0 to 1.0).
-- |
-- | Returns 0.0 for empty tours.
tourProgress :: TourState -> Number
tourProgress ts =
  let total = tourStepCount ts
  in if total == 0 
     then 0.0
     else toNumber (unwrapIndex ts.currentStep + 1) / toNumber total

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // state // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is at first step?
isFirstStep :: TourState -> Boolean
isFirstStep ts = unwrapIndex ts.currentStep == 0

-- | Is at last step?
isLastStep :: TourState -> Boolean
isLastStep ts =
  let total = tourStepCount ts
  in total > 0 && unwrapIndex ts.currentStep == total - 1

-- | Can navigate to next step?
canGoNext :: TourState -> Boolean
canGoNext ts = ts.isActive && not (isLastStep ts)

-- | Can navigate to previous step?
canGoPrev :: TourState -> Boolean
canGoPrev ts = ts.isActive && not (isFirstStep ts)

-- | Is tour complete (at last step and active)?
isTourComplete :: TourState -> Boolean
isTourComplete ts = ts.isActive && isLastStep ts

-- | Is tour empty (no steps)?
isTourEmpty :: TourState -> Boolean
isTourEmpty ts = tourStepCount ts == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // state // transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start the tour (activate and go to first step).
startTour :: TourState -> TourState
startTour ts = ts { currentStep = index 0, isActive = true }

-- | End the tour (deactivate, keep position).
endTour :: TourState -> TourState
endTour ts = ts { isActive = false }

-- | Move to next step (if possible).
-- |
-- | Does nothing if at last step or tour inactive.
nextStep :: TourState -> TourState
nextStep ts
  | not ts.isActive = ts
  | isLastStep ts = ts
  | otherwise = ts { currentStep = index (unwrapIndex ts.currentStep + 1) }

-- | Move to previous step (if possible).
-- |
-- | Does nothing if at first step or tour inactive.
prevStep :: TourState -> TourState
prevStep ts
  | not ts.isActive = ts
  | isFirstStep ts = ts
  | otherwise = ts { currentStep = index (unwrapIndex ts.currentStep - 1) }

-- | Go to specific step.
-- |
-- | Index is clamped to valid range [0, stepCount - 1].
-- | Activates tour if not already active.
goToStep :: Int -> TourState -> TourState
goToStep targetIdx ts =
  let 
    total = tourStepCount ts
    clampedIdx = clampInt 0 (if total == 0 then 0 else total - 1) targetIdx
  in ts { currentStep = index clampedIdx, isActive = true }

-- | Complete the tour (go to last step and deactivate).
completeTour :: TourState -> TourState
completeTour ts =
  let total = tourStepCount ts
  in ts { currentStep = index (if total == 0 then 0 else total - 1), isActive = false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // tour // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration options for tour behavior.
-- |
-- | Controls UI chrome and interaction behavior.
type TourConfig =
  { showProgress :: Boolean        -- ^ Show step counter (e.g., "2 of 5")
  , showSkip :: Boolean            -- ^ Show skip/exit button
  , allowClickOutside :: Boolean   -- ^ Can click outside to dismiss
  , scrollToElement :: Boolean     -- ^ Auto-scroll to bring target into view
  }

-- | Create a tour configuration.
tourConfig :: Boolean -> Boolean -> Boolean -> Boolean -> TourConfig
tourConfig progress skip outside scroll =
  { showProgress: progress
  , showSkip: skip
  , allowClickOutside: outside
  , scrollToElement: scroll
  }

-- | Show progress indicator?
configShowProgress :: TourConfig -> Boolean
configShowProgress cfg = cfg.showProgress

-- | Show skip button?
configShowSkip :: TourConfig -> Boolean
configShowSkip cfg = cfg.showSkip

-- | Allow click outside to dismiss?
configAllowClickOutside :: TourConfig -> Boolean
configAllowClickOutside cfg = cfg.allowClickOutside

-- | Auto-scroll to element?
configScrollToElement :: TourConfig -> Boolean
configScrollToElement cfg = cfg.scrollToElement

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default tour configuration.
-- |
-- | Shows progress and skip, allows outside click, scrolls to element.
tourConfigDefault :: TourConfig
tourConfigDefault = tourConfig true true true true

-- | Minimal tour configuration.
-- |
-- | No progress, no skip, no outside click (focused experience).
tourConfigMinimal :: TourConfig
tourConfigMinimal = tourConfig false false false true

-- | Strict tour configuration.
-- |
-- | Shows progress but no skip or outside click (must complete).
tourConfigStrict :: TourConfig
tourConfigStrict = tourConfig true false false true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp an integer to bounds.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n
