-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // hydrogen // tour
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Product Tour Component — The ULTIMATE Tour System
-- |
-- | Type-safe, accessible, animated product tours for Hydrogen applications.
-- |
-- | ## Features
-- |
-- | - **Type-Safe**: All configuration via ADTs, not strings
-- | - **Accessible**: WCAG 2.1 AA compliant, keyboard navigation, screen reader support
-- | - **Elm Architecture**: Pure state management with `State × Msg → State × [Cmd]`
-- | - **Flexible Targeting**: CSS selectors, test IDs, ARIA roles, multi-element
-- | - **Spring Physics**: Natural motion with spring animations
-- | - **Spotlight Morphing**: Smooth transitions between target elements
-- | - **Persistent**: "Don't show again", snooze, completion tracking
-- | - **Reduced Motion**: Respects prefers-reduced-motion
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hydrogen.Tour as Tour
-- |
-- | -- Define your steps
-- | mySteps :: Array (Tour.Step MyMsg)
-- | mySteps =
-- |   [ Tour.step (Tour.mkStepId "welcome")
-- |       [ Tour.target (Tour.ByTestId (Tour.mkTestId "welcome-btn"))
-- |       , Tour.title "Welcome!"
-- |       , Tour.body "Let's take a quick tour."
-- |       , Tour.buttons
-- |           [ Tour.nextButton "Get Started"
-- |           , Tour.skipButton "Skip"
-- |           ]
-- |       ]
-- |   , Tour.step (Tour.mkStepId "feature")
-- |       [ Tour.target (Tour.BySelector (Tour.unsafeSelector "#main-feature"))
-- |       , Tour.title "Main Feature"
-- |       , Tour.body "This is where the magic happens."
-- |       , Tour.placement Tour.Right Tour.Center
-- |       , Tour.buttons
-- |           [ Tour.prevButton "Back"
-- |           , Tour.completeButton "Done"
-- |           ]
-- |       ]
-- |   ]
-- |
-- | -- Initialize tour state
-- | tourState :: Tour.TourState MyMsg
-- | tourState = Tour.initTour (Tour.mkTourId "onboarding") mySteps
-- |
-- | -- Render the tour
-- | view :: forall w. AppState -> HH.HTML w AppMsg
-- | view state = HH.div_
-- |   [ mainContent
-- |   , map TourAction (Tour.tour state.tourState)
-- |   ]
-- |
-- | -- Handle tour messages
-- | handleAction :: AppMsg -> H.HalogenM ...
-- | handleAction = case _ of
-- |   TourAction msg -> do
-- |     result <- Tour.update msg <$> H.gets _.tourState
-- |     H.modify_ _ { tourState = result.state }
-- |     -- Handle commands (scrolling, analytics, etc.)
-- |     for_ result.cmds handleTourCmd
-- | ```
-- |
-- | ## Architecture
-- |
-- | The tour follows the Elm architecture:
-- |
-- | ```
-- | TourState × TourMsg → TourState × [TourCmd]
-- | view :: TourState → Element TourMsg
-- | ```
-- |
-- | State changes are pure and predictable. Side effects (DOM manipulation,
-- | storage, analytics) are represented as commands that the runtime executes.
-- |
-- | ## Module Structure
-- |
-- | - **Hydrogen.Tour.Types** - Core ADTs (identifiers, targets, placement)
-- | - **Hydrogen.Tour.Step** - Step configuration
-- | - **Hydrogen.Tour.State** - State and configuration types
-- | - **Hydrogen.Tour.Update** - State machine
-- | - **Hydrogen.Tour.View** - UI components (Halogen)
-- | - **Hydrogen.Tour.Storage** - Persistence
-- | - **Hydrogen.Tour.Animation** - Motion system (springs, easing, morph)
-- | - **Hydrogen.Tour.Target** - Target resolution
-- | - **Hydrogen.Tour.Highlight** - Spotlight and overlay
-- | - **Hydrogen.Tour.Navigation** - Progress and buttons
-- | - **Hydrogen.Tour.Msg** - Complete message algebra
module Hydrogen.Tour
  ( -- * Re-exports from Types
    module Hydrogen.Tour.Types
    -- * Re-exports from Step
  , module Hydrogen.Tour.Step
    -- * Re-exports from State
  , module Hydrogen.Tour.State
    -- * Re-exports from Update
  , module Hydrogen.Tour.Update
    -- * Re-exports from View
  , module Hydrogen.Tour.View
    -- * Re-exports from Storage
  , module Hydrogen.Tour.Storage
  ) where

import Hydrogen.Tour.Types 
  ( TourId
  , mkTourId
  , StepId
  , mkStepId
  , Target(BySelector, ByTestId, ByRole, NoTarget)
  , Selector
  , mkSelector
  , unsafeSelector
  , runSelector
  , TestId
  , mkTestId
  , runTestId
  , AriaRole(..)
  , ariaRoleString
  , Side(Top, Right, Bottom, Left)
  , Alignment(Start, Center, End)
  , Placement
  , mkPlacement
  , defaultPlacement
  , oppositeSide
  , Pixel(Pixel)
  , Milliseconds(Milliseconds)
  , TourPhase(..)
  , isActive
  , isPaused
  , isTerminal
  , Progress
  , mkProgress
  , progressCurrent
  , progressTotal
  , progressPercent
  )

import Hydrogen.Tour.Step
  ( Step
  , PlacementConfig
  , defaultPlacementConfig
  , step
  , stepId
  , StepProp
  , target
  , title
  , body
  , placement
  , placementWithOffset
  , buttons
  , arrow
  , noArrow
  , highlight
  , scrollIntoView
  , noScroll
  , Button
  , ButtonAction(..)
  , ButtonVariant(..)
  , button
  , nextButton
  , prevButton
  , skipButton
  , completeButton
  , customButton
  , HighlightConfig
  , defaultHighlight
  , highlightPadding
  , highlightRadius
  , ScrollConfig
  , defaultScroll
  , scrollBehavior
  , ScrollBehavior(..)
  )

import Hydrogen.Tour.State
  ( TourState
  , initTour
  , tourId
  , currentStep
  , currentStepIndex
  , totalSteps
  , progress
  , phase
  , steps
  , canGoNext
  , canGoPrev
  , isFirstStep
  , isLastStep
  , TourMsg(..)
  , TourConfig
  , defaultConfig
  , withOverlayColor
  , withOverlayOpacity
  , withKeyboardNav
  , withCloseOnOverlay
  , withCloseOnEscape
  , DismissReason(..)
  )

import Hydrogen.Tour.Update
  ( update
  , UpdateResult
  , TourCmd(..)
  , AnalyticsEvent(..)
  , findStepByIdIndex
  )

import Hydrogen.Tour.View
  ( tour
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
  , overlayClass
  , tooltipClass
  , buttonPrimaryClass
  , buttonSecondaryClass
  , buttonTextClass
  )

import Hydrogen.Tour.Storage
  ( shouldShowTour
  , hasCompleted
  , hasDismissed
  , isSnoozed
  , markCompleted
  , markDismissed
  , snooze
  , clearSnooze
  , clearTourState
  , completedKey
  , dismissedKey
  , snoozeKey
  )

-- Note: Additional modules available for advanced usage:
--
-- import Hydrogen.Tour.Animation as Animation
-- import Hydrogen.Tour.Target as Target
-- import Hydrogen.Tour.Highlight as Highlight
-- import Hydrogen.Tour.Navigation as Navigation
-- import Hydrogen.Tour.Msg as Msg
