-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // tour // navigation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Navigation and Progress for Product Tours
-- |
-- | This module provides the navigation vocabulary for tour progression:
-- | - Progress indicators (dots, bar, fraction, stepper)
-- | - Button configurations (next, prev, skip, complete)
-- | - Keyboard navigation
-- | - Swipe gesture support
-- | - Close button configuration
-- | - Accessibility features
-- |
-- | ## Design Philosophy
-- |
-- | Navigation elements are pure functions producing Element data. They are
-- | completely stateless — all state comes from TourState.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Navigation as Nav
-- |
-- | -- Progress dots
-- | progressView = Nav.progressDots { current: 2, total: 5, variant: Nav.DotsDefault }
-- |
-- | -- Navigation buttons
-- | buttonsView = Nav.navigationButtons
-- |   { showPrev: true
-- |   , showSkip: true
-- |   , nextLabel: "Continue"
-- |   , prevLabel: "Back"
-- |   , onNext: NextStep
-- |   , onPrev: PrevStep
-- |   }
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Navigation.Progress` — Progress indicator types and builders
-- | - `Navigation.Buttons` — Button configuration and builders
-- | - `Navigation.Keyboard` — Keyboard navigation configuration
-- | - `Navigation.Gestures` — Swipe gesture configuration
-- | - `Navigation.CloseButton` — Close button configuration
-- | - `Navigation.Accessibility` — Accessibility configuration
module Hydrogen.Tour.Navigation
  ( module Progress
  , module Buttons
  , module Keyboard
  , module Gestures
  , module CloseButton
  , module Accessibility
  ) where

import Hydrogen.Tour.Navigation.Progress
  ( DotSize(DotSmall, DotMedium, DotLarge)
  , DotsConfig
  , FractionFormat(FractionOfFormat, FractionSlashFormat, FractionDashFormat)
  , ProgressBarElement
  , ProgressConfig
  , ProgressDotsElement
  , ProgressFractionElement
  , ProgressStepperElement
  , ProgressStyle(ProgressDots, ProgressBar, ProgressFraction, ProgressStepper, ProgressNone)
  , ProgressVariant(VariantDefault, VariantMinimal, VariantProminent, VariantBrand)
  , StepperOrientation(Horizontal, Vertical)
  , defaultProgressConfig
  , progressBar
  , progressDots
  , progressFraction
  , progressStepper
  , variantActiveColor
  , variantInactiveColor
  ) as Progress

import Hydrogen.Tour.Navigation.Buttons
  ( ButtonConfig
  , ButtonIcon(IconArrowLeft, IconArrowRight, IconCheck, IconX, IconSkip, IconCustom)
  , ButtonLayout(LayoutSpaceBetween, LayoutEnd, LayoutStacked)
  , ButtonPosition(PositionStart, PositionCenter, PositionEnd)
  , ButtonSize(ButtonSmall, ButtonMedium, ButtonLarge)
  , ButtonStyle(ButtonPrimary, ButtonSecondary, ButtonGhost, ButtonDestructive, ButtonOutline)
  , NavigationButtonsConfig
  , NavigationElement
  , completeButton
  , customButton
  , defaultButtonConfig
  , navigationButtons
  , nextButton
  , prevButton
  , skipButton
  ) as Buttons

import Hydrogen.Tour.Navigation.Keyboard
  ( KeyAction(KeyNext, KeyPrev, KeyDismiss, KeyComplete, KeyGoToStep)
  , KeyBinding
  , KeyModifier(ModCtrl, ModShift, ModAlt, ModMeta)
  , KeyboardConfig
  , defaultKeyBindings
  , defaultKeyboardConfig
  , withArrowNav
  , withEscapeDismiss
  , withTabNav
  ) as Keyboard

import Hydrogen.Tour.Navigation.Gestures
  ( SwipeConfig
  , SwipeDirection(SwipeLeft, SwipeRight, SwipeUp, SwipeDown)
  , defaultSwipeConfig
  , swipeEnabled
  ) as Gestures

import Hydrogen.Tour.Navigation.CloseButton
  ( CloseButtonConfig
  , CloseButtonPosition(CloseTopRight, CloseTopLeft, CloseInHeader)
  , CloseButtonStyle(CloseIcon, CloseText, CloseIconWithLabel)
  , defaultCloseConfig
  ) as CloseButton

import Hydrogen.Tour.Navigation.Accessibility
  ( A11yConfig
  , FocusTrapConfig
  , InitialFocus(FocusFirstTabbable, FocusContainer, FocusPrimaryButton, FocusNone)
  , LiveRegion(LiveOff, LivePolite, LiveAssertive)
  , defaultA11yConfig
  , focusTrapConfig
  , screenReaderAnnouncement
  ) as Accessibility
