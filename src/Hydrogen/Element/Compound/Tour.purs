-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // tour
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour — The ULTIMATE product tour component.
-- |
-- | ## Overview
-- |
-- | A pure Element tour system with:
-- | - 50+ message types for complete control
-- | - Spring physics and morph animations
-- | - Multi-target spotlight with shape morphing
-- | - Branching paths with merge points
-- | - Accessibility-first design (WCAG 2.1 AA)
-- | - Reduced motion respect
-- | - Persistence (localStorage/sessionStorage)
-- | - Analytics events
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hydrogen.Element.Component.Tour as Tour
-- |
-- | myTour :: forall msg. (Tour.TourMsg -> msg) -> Tour.Element msg
-- | myTour wrapMsg =
-- |   Tour.tour
-- |     [ Tour.steps
-- |         [ Tour.step
-- |             { id: Tour.stepId "welcome"
-- |             , target: Tour.noTarget
-- |             , title: "Welcome!"
-- |             , content: "Let's get you started."
-- |             }
-- |         , Tour.step
-- |             { id: Tour.stepId "sidebar"
-- |             , target: Tour.bySelector ".sidebar"
-- |             , title: "Navigation"
-- |             , content: "Use the sidebar to navigate."
-- |             }
-- |         ]
-- |     , Tour.onNext (wrapMsg Tour.NextStep)
-- |     , Tour.onPrev (wrapMsg Tour.PrevStep)
-- |     , Tour.onSkip (wrapMsg Tour.SkipTour)
-- |     ]
-- | ```
-- |
-- | ## Architecture
-- |
-- | Tours are pure data. The component produces `Element msg` which runtime
-- | targets interpret. State changes flow through `TourMsg` messages.
-- |
-- | ```
-- | TourConfig → Element msg
-- |     ↓
-- | Runtime (DOM/Canvas/WebGL)
-- |     ↓
-- | User Interaction → TourMsg → State Update
-- | ```
-- |
-- | ## Modules
-- |
-- | | Module           | Purpose                                |
-- | |------------------|----------------------------------------|
-- | | Tour.Types       | Core atoms (StepId, Placement, etc.)   |
-- | | Tour.Target      | Target selection strategies            |
-- | | Tour.Highlight   | Spotlight and overlay styles           |
-- | | Tour.Animation   | Transitions, easing, spring physics    |
-- | | Tour.Navigation  | Progress indicators and buttons        |
-- | | Tour.Content     | Step content types                     |
-- | | Tour.Msg         | Complete message algebra               |
-- | | Tour.Motion      | Motion design presets                  |
-- |
-- | ## CSS Custom Properties
-- |
-- | ```css
-- | /* Overlay */
-- | --tour-overlay-color: rgba(0, 0, 0, 0.5);
-- | --tour-overlay-blur: 0px;
-- |
-- | /* Tooltip */
-- | --tour-tooltip-bg: var(--popover);
-- | --tour-tooltip-fg: var(--popover-foreground);
-- | --tour-tooltip-border: var(--border);
-- | --tour-tooltip-shadow: 0 4px 12px rgba(0, 0, 0, 0.15);
-- | --tour-tooltip-radius: 8px;
-- | --tour-tooltip-max-width: 320px;
-- |
-- | /* Spotlight */
-- | --tour-spotlight-padding: 4px;
-- | --tour-spotlight-radius: 4px;
-- |
-- | /* Progress */
-- | --tour-progress-color: var(--primary);
-- | --tour-progress-bg: var(--muted);
-- |
-- | /* Animation */
-- | --tour-duration: 300ms;
-- | --tour-easing: cubic-bezier(0.22, 1.0, 0.36, 1.0);
-- | ```
-- |
-- | ## Keyboard Shortcuts
-- |
-- | | Key       | Action          |
-- | |-----------|-----------------|
-- | | Escape    | Close tour      |
-- | | ArrowRight| Next step       |
-- | | ArrowLeft | Previous step   |
-- | | Enter     | Confirm/Next    |
-- | | Tab       | Focus trap      |

module Hydrogen.Element.Component.Tour
  ( -- * Component
    tour
  , tourWithState
  
  -- * Step Builder
  , step
  , Step
  , StepConfig
  , defaultStepConfig
  
  -- * Tour Props
  , TourProps
  , TourProp
  , defaultTourProps
  
  -- * Prop Builders - Steps
  , steps
  , currentStepIndex
  , currentStepIndexRaw
  , pushHistory
  , goToNextStep
  , goToPrevStep
  , goToStep
  , isActive
  
  -- * Prop Builders - Navigation
  , onNext
  , onPrev
  , onSkip
  , onClose
  , onComplete
  , onStepChange
  , onStepChangeRaw
  , onKeyboardEvent
  , onProgressDotClick
  
  -- * Prop Builders - Display
  , showProgress
  , showOverlay
  , showNavigation
  , placement
  
  -- * Prop Builders - Behavior
  , scrollBehavior
  , keyboardEnabled
  , closeOnOverlayClick
  , closeOnEscape
  
  -- * Prop Builders - Persistence
  , persistKey
  
  -- * Prop Builders - Accessibility
  , ariaLabel
  , announceSteps
  
  -- * Prop Builders - Styling
  , className
  , overlayOpacity
  , spotlightPadding
  
  -- * Target Builders
  , noTarget
  , bySelector
  , byTestId
  , byId
  , byMultiple
  
  -- * Debug (feature flag)
  , debugTourState
  
  -- * Re-exports: Types
  , module ReexportTypes
  
  -- * Re-exports: Target
  , module ReexportTarget
  
  -- * Re-exports: Highlight
  , module ReexportHighlight
  
  -- * Re-exports: Animation
  , module ReexportAnimation
  
  -- * Re-exports: Navigation
  , module ReexportNavigation
  
  -- * Re-exports: Content
  , module ReexportContent
  
  -- * Re-exports: Msg
  , module ReexportMsg
  
  -- * Re-exports: Motion
  , module ReexportMotion
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , Unit
  , show
  , map
  , unit
  , (<>)
  , (<<<)
  , (+)
  , (-)
  , (==)
  , (>=)
  )

import Data.Array (foldl, length, index, mapWithIndex, cons, snoc) as Array
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E

-- Submodules for re-export
import Hydrogen.Element.Component.Tour.Types
  ( StepId
  , stepId
  , unwrapStepId
  , TourId
  , tourId
  , unwrapTourId
  , StepIndex
  , stepIndex
  , unwrapStepIndex
  , firstStepIndex
  , nextStepIndex
  , prevStepIndex
  , Side
      ( SideTop
      , SideRight
      , SideBottom
      , SideLeft
      )
  , oppositeSide
  , Placement
      ( PlacementTop
      , PlacementTopStart
      , PlacementTopEnd
      , PlacementBottom
      , PlacementBottomStart
      , PlacementBottomEnd
      , PlacementLeft
      , PlacementLeftStart
      , PlacementLeftEnd
      , PlacementRight
      , PlacementRightStart
      , PlacementRightEnd
      )
  , placementToString
  , placementToSide
  , oppositePlacement
  , PlacementAuto
      ( AutoBest
      , AutoVertical
      , AutoHorizontal
      , AutoClockwise
      , AutoCounterclockwise
      , AutoFlip
      , AutoFixed
      )
  , Alignment
      ( AlignStart
      , AlignCenter
      , AlignEnd
      )
  , ScrollBehavior
      ( ScrollSmooth
      , ScrollInstant
      , ScrollNone
      )
  , scrollBehaviorToString
  , ScrollBlock
      ( BlockStart
      , BlockCenter
      , BlockEnd
      , BlockNearest
      )
  , ScrollInline
      ( InlineStart
      , InlineCenter
      , InlineEnd
      , InlineNearest
      )
  ) as ReexportTypes

import Hydrogen.Element.Component.Tour.Target
  ( TargetKind
      ( TargetSelector
      , TargetRef
      , TargetRect
      , TargetVirtual
      , TargetBeacon
      , TargetViewport
      , TargetMultiple
      )
  , Selector
  , selector
  , unwrapSelector
  , TargetRect
  , targetRect
  , rectX
  , rectY
  , rectWidth
  , rectHeight
  , TargetAnchor
      ( AnchorCenter
      , AnchorTopLeft
      , AnchorTopCenter
      , AnchorTopRight
      , AnchorMiddleLeft
      , AnchorMiddleRight
      , AnchorBottomLeft
      , AnchorBottomCenter
      , AnchorBottomRight
      )
  , anchorToOffset
  , WaitStrategy
      ( WaitImmediate
      , WaitVisible
      , WaitInViewport
      , WaitInteractive
      , WaitStable
      , WaitCustom
      )
  , WaitTimeout
  , waitTimeout
  , unwrapWaitTimeout
  , defaultWaitTimeout
  , noTimeout
  , TargetConfig
  , defaultTargetConfig
  ) as ReexportTarget

import Hydrogen.Element.Component.Tour.Highlight
  ( HighlightKind
      ( HighlightSpotlight
      , HighlightOutline
      , HighlightGlow
      , HighlightOverlay
      , HighlightNone
      )
  , SpotlightShape
      ( ShapeRect
      , ShapeRoundedRect
      , ShapeCircle
      , ShapeEllipse
      , ShapePill
      , ShapeInset
      , ShapeCustomPath
      )
  , OverlayStyle
      ( OverlaySolid
      , OverlayBlur
      , OverlayGradient
      , OverlayPattern
      , OverlayNone
      )
  , PulseAnimation
      ( PulseNone
      , PulseRing
      , PulseGlow
      , PulseScale
      , PulseBounce
      , PulseShake
      , PulseBreathing
      )
  , GlowStyle
      ( GlowNone
      , GlowSoft
      , GlowStrong
      , GlowNeon
      , GlowPulsing
      )
  , BorderStyle
      ( BorderNone
      , BorderSolid
      , BorderDashed
      , BorderDotted
      , BorderAnimated
      , BorderGradient
      )
  , Opacity
  , opacity
  , unwrapOpacity
  , opaque
  , transparent
  , semiTransparent
  , CornerRadius
  , cornerRadius
  , unwrapCornerRadius
  , sharpCorners
  , roundedCorners
  , pillCorners
  , HighlightConfig
  , defaultHighlightConfig
  , spotlightConfig
  , outlineConfig
  , glowConfig
  , noHighlightConfig
  ) as ReexportHighlight

import Hydrogen.Element.Component.Tour.Animation
  ( TransitionKind
      ( TransitionNone
      , TransitionFade
      , TransitionSlide
      , TransitionZoom
      , TransitionFlip
      , TransitionMorph
      , TransitionCrossfade
      )
  , EasingCurve
      ( EaseLinear
      , EaseIn
      , EaseOut
      , EaseInOut
      , EaseInQuad
      , EaseOutQuad
      , EaseInOutQuad
      , EaseInCubic
      , EaseOutCubic
      , EaseInOutCubic
      , EaseInQuart
      , EaseOutQuart
      , EaseInOutQuart
      , EaseInExpo
      , EaseOutExpo
      , EaseInOutExpo
      , EaseInBack
      , EaseOutBack
      , EaseInOutBack
      , EaseInBounce
      , EaseOutBounce
      , EaseInOutBounce
      , EaseSpring
      , EaseCustom
      )
  , easingToCss
  , EntranceKind
      ( EnterFade
      , EnterSlideUp
      , EnterSlideDown
      , EnterSlideLeft
      , EnterSlideRight
      , EnterZoomIn
      , EnterFlipX
      , EnterFlipY
      , EnterPop
      , EnterNone
      )
  , ExitKind
      ( ExitFade
      , ExitSlideUp
      , ExitSlideDown
      , ExitSlideLeft
      , ExitSlideRight
      , ExitZoomOut
      , ExitFlipX
      , ExitFlipY
      , ExitPop
      , ExitNone
      )
  , Duration
  , duration
  , unwrapDuration
  , instant
  , fast
  , normal
  , slow
  , verySlow
  , Delay
  , delay
  , unwrapDelay
  , noDelay
  , shortDelay
  , mediumDelay
  , longDelay
  , SpringConfig
  , springConfig
  , defaultSpring
  , bouncySpring
  , stiffSpring
  , gentleSpring
  , AnimationConfig
  , defaultAnimationConfig
  , fastAnimationConfig
  , slowAnimationConfig
  , noAnimationConfig
  ) as ReexportAnimation

import Hydrogen.Element.Component.Tour.Navigation
  ( NavigationStyle
      ( NavMinimal
      , NavStandard
      , NavExpanded
      , NavCompact
      , NavFloating
      , NavDocked
      , NavHidden
      )
  , ProgressStyle
      ( ProgressNone
      , ProgressDots
      , ProgressBar
      , ProgressNumbers
      , ProgressFraction
      , ProgressSteps
      , ProgressCircle
      )
  , ButtonPosition
      ( ButtonInTooltip
      , ButtonBelowTooltip
      , ButtonFooter
      , ButtonFloating
      , ButtonInline
      )
  , ButtonVariant
      ( VariantPrimary
      , VariantSecondary
      , VariantGhost
      , VariantLink
      , VariantOutline
      , VariantIcon
      )
  , CloseMode
      ( CloseButton
      , CloseOverlayClick
      , CloseEscape
      , CloseAny
      , CloseNone
      )
  , SkipMode
      ( SkipAlways
      , SkipAfterSteps
      , SkipNever
      , SkipOnlyLast
      )
  , KeyboardKey
      ( KeyArrowRight
      , KeyArrowLeft
      , KeyArrowUp
      , KeyArrowDown
      , KeyEnter
      , KeySpace
      , KeyEscape
      , KeyTab
      , KeyHome
      , KeyEnd
      , KeyN
      , KeyP
      )
  , NavigationLabels
  , defaultLabels
  , minimalLabels
  , KeyboardConfig
  , defaultKeyboardConfig
  , arrowKeyConfig
  , vimKeyConfig
  , disabledKeyboardConfig
  , NavigationConfig
  , defaultNavigationConfig
  , minimalNavigationConfig
  , expandedNavigationConfig
  ) as ReexportNavigation

import Hydrogen.Element.Component.Tour.Content
  ( ContentKind
      ( ContentText
      , ContentRichText
      , ContentMedia
      , ContentInteractive
      , ContentChecklist
      , ContentVideo
      , ContentCode
      , ContentCustom
      )
  , MediaType
      ( MediaImage
      , MediaGif
      , MediaVideo
      , MediaLottie
      , MediaRive
      , MediaSvg
      )
  , InteractiveKind
      ( InteractiveClick
      , InteractiveInput
      , InteractiveSelect
      , InteractiveToggle
      , InteractiveHotspot
      , InteractiveTask
      )
  , TooltipSize
      ( SizeAuto
      , SizeSmall
      , SizeMedium
      , SizeLarge
      , SizeFullWidth
      , SizeCustom
      )
  , sizeToMaxWidth
  -- Note: ContentAlign is NOT re-exported to avoid conflict with Types.Alignment
  -- Use Tour.Content.AlignLeft/AlignCenter/AlignRight directly
  , TextContent
  , textContent
  , withSubtitle
  , withDescription
  , MediaContent
  , imageContent
  , videoContent
  , gifContent
  , ChecklistItem
  , checklistItem
  , requiredItem
  , optionalItem
  , ContentConfig
  , defaultContentConfig
  , mediaContentConfig
  , interactiveContentConfig
  ) as ReexportContent

import Hydrogen.Element.Component.Tour.Msg
  ( TourMsg
      ( NextStep
      , PrevStep
      , GoToStep
      , FirstStep
      , LastStep
      , SkipTour
      , SkipToEnd
      , StartTour
      , PauseTour
      , ResumeTour
      , CompleteTour
      , RestartTour
      , ResetTour
      , TargetFound
      , TargetLost
      , TargetReady
      , TargetTimeout
      , ScrollStart
      , ScrollComplete
      , ScrollError
      , HighlightShow
      , HighlightHide
      , HighlightClick
      , OverlayClick
      , TooltipShow
      , TooltipHide
      , TooltipFocus
      , TooltipBlur
      , TaskComplete
      , ChecklistItemToggle
      , InputChange
      , HotspotClick
      , KeyDown
      , FocusTrap
      , SwipeLeft
      , SwipeRight
      , PinchZoom
      , ProgressLoaded
      , ProgressSaved
      , ProgressCleared
      , TrackView
      , TrackInteraction
      , TrackComplete
      , TourError
      , Recover
      )
  ) as ReexportMsg

import Hydrogen.Element.Component.Tour.Motion
  ( -- Spotlight Morphing
    MorphConfig
  , defaultMorphConfig
  , snappyMorphConfig
  , elasticMorphConfig
  , MorphPath(PathDirect, PathArc, PathBezier, PathAvoid, PathFollow)
  , MorphInterpolation(InterpolateDirect, InterpolateSmooth, InterpolateSuperellipse, InterpolateCorners)
  , ShapeInterpolation
  , interpolateRect
  , interpolateCircle
  , interpolatePill
  , computeMorphPath
  
  -- Tooltip Choreography
  , TooltipChoreography
  , MicroInteractionConfig
  , ChoreographyPhase(PhaseIdle, PhaseEntering, PhaseVisible, PhaseExiting, PhaseFollowing)
  , defaultChoreography
  , minimalChoreography
  , dramaticChoreography
  , defaultMicroInteractions
  , computeEntryAnimation
  , computeExitAnimation
  , computeFollowBehavior
  
  -- Progress Animations
  -- Note: ProgressAnimationStyle is NOT re-exported to avoid conflict with Navigation.ProgressStyle
  -- Use Tour.Motion.ProgressAnimationStyle directly for advanced animation configs
  , DotProgressConfig
  , BarProgressConfig
  , BarFillStyle(FillLinear, FillLiquid, FillElastic, FillGradient)
  , CircularProgressConfig
  , FlipCounterConfig
  , defaultDotProgress
  , liquidBarProgress
  , strokeCircularProgress
  , flipCounterConfig
  
  -- Attention Grabbers
  , AttentionPattern(AttentionPulse, AttentionBeacon, AttentionMagnetic, AttentionCelebration, AttentionNone)
  , PulseConfig
  , BeaconConfig
  , MagneticConfig
  , CelebrationConfig
  , gentlePulse
  , subtleBeacon
  , magneticPull
  , celebrationBurst
  
  -- Responsive Motion
  , MotionScale(MotionFull, MotionReduced, MotionMinimal, MotionNone)
  , ReducedMotionFallback
  , PerformanceTier(TierHigh, TierMedium, TierLow, TierMinimal)
  , computeMotionScale
  , reducedMotionFallbacks
  , performanceAdaptations
  
  -- Spring Physics
  -- Note: SpringParams and spring presets from Motion are NOT re-exported 
  -- to avoid conflict with Animation.SpringConfig
  -- Use Tour.Motion for advanced spring physics (SpringPreset, SpringParams)
  -- Use Tour.Animation for basic springs (SpringConfig, bouncySpring, etc.)
  , SpringPreset(Snappy, Bouncy, Smooth, Precise, Critical)
  , springToCss
  , springDuration
  
  -- Timing Curves
  , TimingCurve
  , organicEase
  , morphEase
  , tooltipEntryEase
  , tooltipExitEase
  , progressEase
  , attentionEase
  ) as ReexportMotion

-- Internal imports (for use within this module)
-- These are separate from re-exports to allow internal usage
import Hydrogen.Element.Component.Tour.Types
  ( StepId
  , stepId
  , StepIndex
  , stepIndex
  , unwrapStepIndex
  , firstStepIndex
  , nextStepIndex
  , prevStepIndex
  , Placement
      ( PlacementTop
      , PlacementTopStart
      , PlacementTopEnd
      , PlacementBottom
      , PlacementBottomStart
      , PlacementBottomEnd
      , PlacementLeft
      , PlacementLeftStart
      , PlacementLeftEnd
      , PlacementRight
      , PlacementRightStart
      , PlacementRightEnd
      )
  , placementToString
  , ScrollBehavior(ScrollSmooth)
  , scrollBehaviorToString
  )

-- Internal Target import (separate from ReexportTarget for unqualified use)
import Hydrogen.Element.Component.Tour.Target
  ( TargetKind
      ( TargetSelector
      , TargetRef
      , TargetRect
      , TargetVirtual
      , TargetBeacon
      , TargetViewport
      , TargetMultiple
      )
  , Selector
  , selector
  , unwrapSelector
  )

import Hydrogen.Element.Component.Tour.Highlight
  ( Opacity
  , unwrapOpacity
  , semiTransparent
  )

-- Note: TourMsg is re-exported via ReexportMsg but not used internally

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Step configuration for a single tour step.
type StepConfig =
  { id :: StepId
  , target :: TargetKind
  , title :: String
  , content :: String
  , placement :: Placement
  , spotlightPadding :: Int
  }

-- | Tour step.
type Step = { config :: StepConfig }

-- | Default step configuration.
defaultStepConfig :: StepConfig
defaultStepConfig =
  { id: stepId "step"
  , target: TargetViewport
  , title: ""
  , content: ""
  , placement: PlacementBottom
  , spotlightPadding: 8
  }

-- | Create a step from partial config.
step :: { id :: StepId, target :: TargetKind, title :: String, content :: String } -> Step
step cfg =
  { config:
      { id: cfg.id
      , target: cfg.target
      , title: cfg.title
      , content: cfg.content
      , placement: PlacementBottom
      , spotlightPadding: 8
      }
  }

-- | Tour properties.
-- |
-- | Uses bounded `StepIndex` instead of raw `Int` to prevent invalid states.
-- | Tracks `history` for back navigation support.
type TourProps msg =
  { steps :: Array Step
  , currentStepIndex :: StepIndex
  , history :: Array StepIndex           -- For back navigation
  , isActive :: Boolean
  
  -- Navigation handlers
  , onNext :: Maybe msg
  , onPrev :: Maybe msg
  , onSkip :: Maybe msg
  , onClose :: Maybe msg
  , onComplete :: Maybe msg
  , onStepChange :: Maybe (StepIndex -> msg)
  
  -- Keyboard handler
  -- | Maps key string (e.g., "Escape", "ArrowRight") to message.
  -- | Pure data - rendering target interprets and dispatches.
  , onKeyboardEvent :: Maybe (String -> msg)
  
  -- Progress dot click handler
  -- | Called when user clicks a progress dot for direct navigation.
  -- | Pure data - receives the target StepIndex.
  , onProgressDotClick :: Maybe (StepIndex -> msg)
  
  -- Display
  , showProgress :: Boolean
  , showOverlay :: Boolean
  , showNavigation :: Boolean
  , placement :: Placement
  
  -- Behavior
  , scrollBehavior :: ScrollBehavior
  , keyboardEnabled :: Boolean
  , closeOnOverlayClick :: Boolean
  , closeOnEscape :: Boolean
  
  -- Persistence
  , persistKey :: Maybe String
  
  -- Accessibility
  , ariaLabel :: String
  , announceSteps :: Boolean
  
  -- Styling
  , className :: String
  , overlayOpacity :: Opacity
  , spotlightPadding :: Int
  }

-- | Tour property modifier.
type TourProp msg = TourProps msg -> TourProps msg

-- | Default tour properties.
defaultTourProps :: forall msg. TourProps msg
defaultTourProps =
  { steps: []
  , currentStepIndex: firstStepIndex
  , history: []
  , isActive: true
  
  , onNext: Nothing
  , onPrev: Nothing
  , onSkip: Nothing
  , onClose: Nothing
  , onComplete: Nothing
  , onStepChange: Nothing
  , onKeyboardEvent: Nothing
  , onProgressDotClick: Nothing
  
  , showProgress: true
  , showOverlay: true
  , showNavigation: true
  , placement: PlacementBottom
  
  , scrollBehavior: ScrollSmooth
  , keyboardEnabled: true
  , closeOnOverlayClick: false
  , closeOnEscape: true
  
  , persistKey: Nothing
  
  , ariaLabel: "Product tour"
  , announceSteps: true
  
  , className: ""
  , overlayOpacity: semiTransparent
  , spotlightPadding: 8
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set tour steps.
steps :: forall msg. Array Step -> TourProp msg
steps s props = props { steps = s }

-- | Set current step index (bounded).
currentStepIndex :: forall msg. StepIndex -> TourProp msg
currentStepIndex idx props = props { currentStepIndex = idx }

-- | Set current step index from raw Int (validates to non-negative).
currentStepIndexRaw :: forall msg. Int -> TourProp msg
currentStepIndexRaw idx props = props { currentStepIndex = stepIndex idx }

-- | Add a step to navigation history (for back button support).
pushHistory :: forall msg. StepIndex -> TourProp msg
pushHistory idx props = props { history = Array.snoc props.history idx }

-- | Set active state.
isActive :: forall msg. Boolean -> TourProp msg
isActive a props = props { isActive = a }

-- | Set next step handler.
onNext :: forall msg. msg -> TourProp msg
onNext m props = props { onNext = Just m }

-- | Set previous step handler.
onPrev :: forall msg. msg -> TourProp msg
onPrev m props = props { onPrev = Just m }

-- | Set skip handler.
onSkip :: forall msg. msg -> TourProp msg
onSkip m props = props { onSkip = Just m }

-- | Set close handler.
onClose :: forall msg. msg -> TourProp msg
onClose m props = props { onClose = Just m }

-- | Set completion handler.
onComplete :: forall msg. msg -> TourProp msg
onComplete m props = props { onComplete = Just m }

-- | Set step change handler (receives bounded StepIndex).
onStepChange :: forall msg. (StepIndex -> msg) -> TourProp msg
onStepChange f props = props { onStepChange = Just f }

-- | Set step change handler from raw Int (validates to non-negative).
onStepChangeRaw :: forall msg. (Int -> msg) -> TourProp msg
onStepChangeRaw f props = props { onStepChange = Just (f <<< unwrapStepIndex) }

-- | Set keyboard event handler.
-- |
-- | Maps key strings (e.g., "Escape", "ArrowRight", "ArrowLeft") to messages.
-- | Pure data - rendering target interprets and dispatches.
-- |
-- | Example:
-- | ```purescript
-- | Tour.onKeyboardEvent \key -> case key of
-- |   "Escape" -> MyCloseMsg
-- |   "ArrowRight" -> MyNextMsg
-- |   "ArrowLeft" -> MyPrevMsg
-- |   _ -> MyNoOp
-- | ```
onKeyboardEvent :: forall msg. (String -> msg) -> TourProp msg
onKeyboardEvent f props = props { onKeyboardEvent = Just f }

-- | Set progress dot click handler for direct step navigation.
-- |
-- | Called when user clicks a progress dot. Receives the target StepIndex.
-- |
-- | Example:
-- | ```purescript
-- | Tour.onProgressDotClick \idx -> GoToStep idx
-- | ```
onProgressDotClick :: forall msg. (StepIndex -> msg) -> TourProp msg
onProgressDotClick f props = props { onProgressDotClick = Just f }

-- | Advance to next step, recording current in history.
goToNextStep :: forall msg. TourProp msg
goToNextStep props = props 
  { currentStepIndex = nextStepIndex props.currentStepIndex
  , history = Array.snoc props.history props.currentStepIndex
  }

-- | Go to previous step using history if available.
goToPrevStep :: forall msg. TourProp msg
goToPrevStep props = props
  { currentStepIndex = prevStepIndex props.currentStepIndex
  }

-- | Jump to specific step.
goToStep :: forall msg. StepIndex -> TourProp msg
goToStep idx props = props
  { currentStepIndex = idx
  , history = Array.snoc props.history props.currentStepIndex
  }

-- | Show/hide progress indicator.
showProgress :: forall msg. Boolean -> TourProp msg
showProgress s props = props { showProgress = s }

-- | Show/hide overlay.
showOverlay :: forall msg. Boolean -> TourProp msg
showOverlay s props = props { showOverlay = s }

-- | Show/hide navigation buttons.
showNavigation :: forall msg. Boolean -> TourProp msg
showNavigation s props = props { showNavigation = s }

-- | Set tooltip placement.
placement :: forall msg. Placement -> TourProp msg
placement p props = props { placement = p }

-- | Set scroll behavior.
scrollBehavior :: forall msg. ScrollBehavior -> TourProp msg
scrollBehavior s props = props { scrollBehavior = s }

-- | Enable/disable keyboard navigation.
keyboardEnabled :: forall msg. Boolean -> TourProp msg
keyboardEnabled k props = props { keyboardEnabled = k }

-- | Close tour on overlay click.
closeOnOverlayClick :: forall msg. Boolean -> TourProp msg
closeOnOverlayClick c props = props { closeOnOverlayClick = c }

-- | Close tour on Escape key.
closeOnEscape :: forall msg. Boolean -> TourProp msg
closeOnEscape c props = props { closeOnEscape = c }

-- | Set localStorage key for persistence.
persistKey :: forall msg. String -> TourProp msg
persistKey k props = props { persistKey = Just k }

-- | Set accessible label.
ariaLabel :: forall msg. String -> TourProp msg
ariaLabel l props = props { ariaLabel = l }

-- | Announce step changes to screen readers.
announceSteps :: forall msg. Boolean -> TourProp msg
announceSteps a props = props { announceSteps = a }

-- | Add custom CSS class.
className :: forall msg. String -> TourProp msg
className c props = props { className = props.className <> " " <> c }

-- | Set overlay opacity.
overlayOpacity :: forall msg. Opacity -> TourProp msg
overlayOpacity o props = props { overlayOpacity = o }

-- | Set spotlight padding.
spotlightPadding :: forall msg. Int -> TourProp msg
spotlightPadding p props = props { spotlightPadding = p }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // target builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | No target (centered modal).
noTarget :: TargetKind
noTarget = TargetViewport

-- | Target by CSS selector.
bySelector :: String -> TargetKind
bySelector s = TargetSelector (selector s)

-- | Target by data-testid attribute.
byTestId :: String -> TargetKind
byTestId tid = TargetSelector (selector ("[data-testid=\"" <> tid <> "\"]"))

-- | Target by element ID.
byId :: String -> TargetKind
byId eid = TargetSelector (selector ("#" <> eid))

-- | Target multiple elements.
byMultiple :: Array String -> TargetKind
byMultiple sels = TargetMultiple (map selector sels)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main tour component.
-- |
-- | Renders a complete tour with overlay, spotlight, tooltip, and navigation.
tour :: forall msg. Array (TourProp msg) -> E.Element msg
tour propMods =
  let
    props = Array.foldl (\p f -> f p) defaultTourProps propMods
  in
    tourWithState props

-- | Tour component with explicit props.
tourWithState :: forall msg. TourProps msg -> E.Element msg
tourWithState props =
  let
    stepCount = Array.length props.steps
    currentInt = unwrapStepIndex props.currentStepIndex
    currentStep = Array.index props.steps currentInt
    isFirst = currentInt == 0
    isLast = currentInt >= stepCount - 1
    
    -- Keyboard handler (pure data — rendering target interprets)
    keyboardHandler = case props.onKeyboardEvent of
      Just handler -> [ E.onKeyDown handler ]
      Nothing -> []
  in
    if props.isActive then
      E.div_
        ( [ E.class_ ("tour-container fixed inset-0 z-50" <> props.className)
          , E.role "dialog"
          , E.ariaLabel props.ariaLabel
          , E.tabIndex 0  -- Make focusable for keyboard events
          , E.dataAttr "tour-active" "true"
          , E.dataAttr "tour-step" (show currentInt)
          , E.dataAttr "tour-total" (show stepCount)
          , E.dataAttr "keyboard-enabled" (show props.keyboardEnabled)
          , E.dataAttr "scroll-behavior" (scrollBehaviorToString props.scrollBehavior)
          ] <> keyboardHandler
        )
        [ -- Overlay
          if props.showOverlay then
            tourOverlay props
          else
            E.empty
        
        -- Spotlight (for targeted steps)
        , case currentStep of
            Just s -> tourSpotlight props s
            Nothing -> E.empty
        
        -- Tooltip
        , case currentStep of
            Just s -> tourTooltip props s isFirst isLast stepCount
            Nothing -> E.empty
        
        -- Screen reader announcements
        , if props.announceSteps then
            case currentStep of
              Just s -> tourAnnouncement props s stepCount
              Nothing -> E.empty
          else
            E.empty
        ]
    else
      E.empty

-- | Overlay backdrop.
tourOverlay :: forall msg. TourProps msg -> E.Element msg
tourOverlay props =
  let
    opacityValue = unwrapOpacity props.overlayOpacity
    clickHandler = case props.closeOnOverlayClick of
      true -> case props.onClose of
        Just handler -> [ E.onClick handler ]
        Nothing -> []
      false -> []
  in
    E.div_
      ( [ E.class_ "tour-overlay fixed inset-0 bg-black transition-opacity"
        , E.style "opacity" (show opacityValue)
        , E.ariaHidden true
        , E.dataAttr "tour-overlay" "true"
        ] <> clickHandler
      )
      []

-- | Spotlight cutout around target.
tourSpotlight :: forall msg. TourProps msg -> Step -> E.Element msg
tourSpotlight props s =
  let
    targetAttr = case s.config.target of
      TargetSelector sel -> E.dataAttr "target-selector" (unwrapSelector sel)
      TargetRef refName -> E.dataAttr "target-ref" refName
      TargetRect _ -> E.dataAttr "target-rect" "true"
      TargetVirtual _ -> E.dataAttr "target-virtual" "true"
      TargetBeacon beaconId -> E.dataAttr "target-beacon" beaconId
      TargetViewport -> E.dataAttr "target-viewport" "true"
      TargetMultiple _ -> E.dataAttr "target-multiple" "true"
  in
    E.div_
      [ E.class_ "tour-spotlight fixed pointer-events-none z-[55] transition-all"
      , targetAttr
      , E.dataAttr "spotlight-padding" (show props.spotlightPadding)
      , E.ariaHidden true
      ]
      []

-- | Tooltip with step content.
tourTooltip :: forall msg. TourProps msg -> Step -> Boolean -> Boolean -> Int -> E.Element msg
tourTooltip props s isFirst isLast stepCount =
  let
    placementClass = "tour-tooltip-" <> placementToString s.config.placement
  in
    E.div_
      [ E.class_ ("tour-tooltip fixed bg-popover text-popover-foreground rounded-lg shadow-lg border p-4 max-w-sm z-[60] " <> placementClass)
      , E.role "tooltip"
      , E.dataAttr "placement" (placementToString s.config.placement)
      ]
      [ -- Arrow
        tourArrow s.config.placement
      
      -- Title
      , E.h4_
          [ E.class_ "tour-tooltip-title font-semibold text-lg mb-2" ]
          [ E.text s.config.title ]
      
      -- Content
      , E.p_
          [ E.class_ "tour-tooltip-description text-sm text-muted-foreground mb-4" ]
          [ E.text s.config.content ]
      
      -- Progress
      , if props.showProgress then
          tourProgress props stepCount
        else
          E.empty
      
      -- Navigation
      , if props.showNavigation then
          tourNavigation props isFirst isLast
        else
          E.empty
      ]

-- | Tooltip arrow.
tourArrow :: forall msg. Placement -> E.Element msg
tourArrow p =
  let
    arrowClass = case p of
      PlacementTop -> "bottom-0 left-1/2 -translate-x-1/2 translate-y-1/2 rotate-45"
      PlacementTopStart -> "bottom-0 left-4 translate-y-1/2 rotate-45"
      PlacementTopEnd -> "bottom-0 right-4 translate-y-1/2 rotate-45"
      PlacementBottom -> "top-0 left-1/2 -translate-x-1/2 -translate-y-1/2 rotate-45"
      PlacementBottomStart -> "top-0 left-4 -translate-y-1/2 rotate-45"
      PlacementBottomEnd -> "top-0 right-4 -translate-y-1/2 rotate-45"
      PlacementLeft -> "right-0 top-1/2 translate-x-1/2 -translate-y-1/2 rotate-45"
      PlacementLeftStart -> "right-0 top-4 translate-x-1/2 rotate-45"
      PlacementLeftEnd -> "right-0 bottom-4 translate-x-1/2 rotate-45"
      PlacementRight -> "left-0 top-1/2 -translate-x-1/2 -translate-y-1/2 rotate-45"
      PlacementRightStart -> "left-0 top-4 -translate-x-1/2 rotate-45"
      PlacementRightEnd -> "left-0 bottom-4 -translate-x-1/2 rotate-45"
  in
    E.div_
      [ E.class_ ("tour-tooltip-arrow absolute w-3 h-3 bg-popover border-r border-b " <> arrowClass) ]
      []

-- | Progress indicator.
-- |
-- | Uses bounded StepIndex for current position.
tourProgress :: forall msg. TourProps msg -> Int -> E.Element msg
tourProgress props total =
  let
    currentInt = unwrapStepIndex props.currentStepIndex
  in
    E.div_
      [ E.class_ "tour-progress flex items-center gap-1 mb-3"
      , E.ariaLabel ("Step " <> show (currentInt + 1) <> " of " <> show total)
      ]
      (Array.mapWithIndex (progressDot props currentInt) (replicate total))

-- | Single progress dot.
-- |
-- | Clickable when `onProgressDotClick` is set. Pure data.
progressDot :: forall msg. TourProps msg -> Int -> Int -> Unit -> E.Element msg
progressDot props currentInt idx _ =
  let
    isActiveStep = idx == currentInt
    activeClass = if isActiveStep then "bg-primary w-3" else "bg-muted-foreground/50 w-2"
    
    -- Click handler for direct navigation (pure data)
    clickHandler = case props.onProgressDotClick of
      Just handler -> 
        [ E.onClick (handler (stepIndex idx))
        , E.class_ "cursor-pointer"
        , E.role "button"
        , E.ariaLabel ("Go to step " <> show (idx + 1))
        ]
      Nothing -> []
  in
    E.div_
      ( [ E.class_ ("tour-progress-dot h-2 rounded-full transition-all " <> activeClass)
        , E.dataAttr "step-index" (show idx)
        ] <> clickHandler
      )
      []

-- | Navigation buttons.
tourNavigation :: forall msg. TourProps msg -> Boolean -> Boolean -> E.Element msg
tourNavigation props isFirst isLast =
  E.div_
    [ E.class_ "tour-navigation flex items-center justify-between gap-2" ]
    [ -- Skip button
      case props.onSkip of
        Just handler ->
          E.button_
            [ E.class_ "tour-skip px-3 py-1.5 text-sm text-muted-foreground hover:text-foreground transition-colors"
            , E.type_ "button"
            , E.onClick handler
            ]
            [ E.text "Skip" ]
        Nothing -> E.empty
    
    -- Spacer
    , E.div_ [ E.class_ "flex-1" ] []
    
    -- Previous button
    , if isFirst then
        E.empty
      else
        case props.onPrev of
          Just handler ->
            E.button_
              [ E.class_ "tour-prev px-3 py-1.5 text-sm rounded-md border border-input bg-background hover:bg-accent transition-colors"
              , E.type_ "button"
              , E.onClick handler
              ]
              [ E.text "Previous" ]
          Nothing -> E.empty
    
    -- Next/Complete button
    , if isLast then
        case props.onComplete of
          Just h ->
            E.button_
              [ E.class_ "tour-next px-3 py-1.5 text-sm rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors"
              , E.type_ "button"
              , E.onClick h
              ]
              [ E.text "Complete" ]
          Nothing -> E.empty
      else
        case props.onNext of
          Just h ->
            E.button_
              [ E.class_ "tour-next px-3 py-1.5 text-sm rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors"
              , E.type_ "button"
              , E.onClick h
              ]
              [ E.text "Next" ]
          Nothing -> E.empty
    ]

-- | Screen reader announcement.
tourAnnouncement :: forall msg. TourProps msg -> Step -> Int -> E.Element msg
tourAnnouncement props s total =
  let
    stepNum = show (unwrapStepIndex props.currentStepIndex + 1)
    totalStr = show total
  in
    E.div_
      [ E.class_ "sr-only"
      , E.role "status"
      , E.ariaLive "polite"
      , E.ariaAtomic "true"
      ]
      [ E.text ("Step " <> stepNum <> " of " <> totalStr <> ": " <> s.config.title <> ". " <> s.config.content) ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an array of units for mapping.
replicate :: Int -> Array Unit
replicate n = go n []
  where
    go 0 acc = acc
    go i acc = go (i - 1) (Array.cons unit acc)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // debug
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Debug representation of tour state.
-- |
-- | Uses Show instances to produce human-readable debug output.
-- | This is a debugging feature, not for production display.
debugTourState :: forall msg. Show msg => TourProps msg -> String
debugTourState props =
  "Tour { "
    <> "step: " <> show (unwrapStepIndex props.currentStepIndex)
    <> "/" <> show (Array.length props.steps)
    <> ", active: " <> show props.isActive
    <> ", history: " <> show (Array.length props.history) <> " steps"
    <> ", placement: " <> placementToString props.placement
    <> " }"
