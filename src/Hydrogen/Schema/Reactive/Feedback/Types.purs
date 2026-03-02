-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // reactive // feedback // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core feedback types - atoms for notification and messaging.
-- |
-- | Defines the fundamental enums and action types used across
-- | all feedback molecules and compounds.

module Hydrogen.Schema.Reactive.Feedback.Types
  ( -- * Feedback Type
    FeedbackType(ToastType, SnackbarType, BannerType, AlertType, DialogType')
  , isToast
  , isSnackbar
  , isBanner
  , isAlert
  , isDialog
  -- * Feedback Severity
  , FeedbackSeverity(FeedbackSuccess, FeedbackInfo, FeedbackWarning, FeedbackError, FeedbackNeutral)
  , isFeedbackSuccess
  , isFeedbackInfo
  , isFeedbackWarning
  , isFeedbackError
  , isFeedbackNeutral
  -- * Feedback Position
  , FeedbackPosition(TopLeft, TopCenter, TopRight, BottomLeft, BottomCenter, BottomRight)
  , isTopLeft
  , isTopCenter
  , isTopRight
  , isBottomLeft
  , isBottomCenter
  , isBottomRight
  -- * Duration
  , FeedbackDuration(DurationShort, DurationMedium, DurationLong, DurationPersistent)
  , isShort
  , isMedium
  , isLong
  , isPersistent
  , durationMs
  -- * Dismissal
  , DismissalMethod(AutoDismiss, ManualDismiss, ActionDismiss, SwipeDismiss)
  , isAutoDismiss
  , isManualDismiss
  , isActionDismiss
  , isSwipeDismiss
  -- * Action Button
  , FeedbackAction
  , feedbackAction
  , undoAction
  , retryAction
  , dismissAction
  , actionLabel
  -- * Computed Properties
  , shouldAutoDismiss
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // feedback type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of feedback notification
data FeedbackType
  = ToastType      -- ^ Brief, non-blocking notification
  | SnackbarType   -- ^ Brief with optional action
  | BannerType     -- ^ Persistent top/bottom message
  | AlertType      -- ^ Inline alert box
  | DialogType'    -- ^ Modal dialog (named with ' to avoid conflict)

derive instance eqFeedbackType :: Eq FeedbackType
derive instance ordFeedbackType :: Ord FeedbackType

instance showFeedbackType :: Show FeedbackType where
  show ToastType = "toast"
  show SnackbarType = "snackbar"
  show BannerType = "banner"
  show AlertType = "alert"
  show DialogType' = "dialog"

isToast :: FeedbackType -> Boolean
isToast ToastType = true
isToast _ = false

isSnackbar :: FeedbackType -> Boolean
isSnackbar SnackbarType = true
isSnackbar _ = false

isBanner :: FeedbackType -> Boolean
isBanner BannerType = true
isBanner _ = false

isAlert :: FeedbackType -> Boolean
isAlert AlertType = true
isAlert _ = false

isDialog :: FeedbackType -> Boolean
isDialog DialogType' = true
isDialog _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // feedback severity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Severity/intent of feedback
data FeedbackSeverity
  = FeedbackSuccess   -- ^ Operation succeeded
  | FeedbackInfo      -- ^ Informational message
  | FeedbackWarning   -- ^ Warning/caution
  | FeedbackError     -- ^ Error occurred
  | FeedbackNeutral   -- ^ No specific severity

derive instance eqFeedbackSeverity :: Eq FeedbackSeverity
derive instance ordFeedbackSeverity :: Ord FeedbackSeverity

instance showFeedbackSeverity :: Show FeedbackSeverity where
  show FeedbackSuccess = "success"
  show FeedbackInfo = "info"
  show FeedbackWarning = "warning"
  show FeedbackError = "error"
  show FeedbackNeutral = "neutral"

isFeedbackSuccess :: FeedbackSeverity -> Boolean
isFeedbackSuccess FeedbackSuccess = true
isFeedbackSuccess _ = false

isFeedbackInfo :: FeedbackSeverity -> Boolean
isFeedbackInfo FeedbackInfo = true
isFeedbackInfo _ = false

isFeedbackWarning :: FeedbackSeverity -> Boolean
isFeedbackWarning FeedbackWarning = true
isFeedbackWarning _ = false

isFeedbackError :: FeedbackSeverity -> Boolean
isFeedbackError FeedbackError = true
isFeedbackError _ = false

isFeedbackNeutral :: FeedbackSeverity -> Boolean
isFeedbackNeutral FeedbackNeutral = true
isFeedbackNeutral _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // feedback position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Screen position for feedback
data FeedbackPosition
  = TopLeft
  | TopCenter
  | TopRight
  | BottomLeft
  | BottomCenter
  | BottomRight

derive instance eqFeedbackPosition :: Eq FeedbackPosition
derive instance ordFeedbackPosition :: Ord FeedbackPosition

instance showFeedbackPosition :: Show FeedbackPosition where
  show TopLeft = "top-left"
  show TopCenter = "top-center"
  show TopRight = "top-right"
  show BottomLeft = "bottom-left"
  show BottomCenter = "bottom-center"
  show BottomRight = "bottom-right"

isTopLeft :: FeedbackPosition -> Boolean
isTopLeft TopLeft = true
isTopLeft _ = false

isTopCenter :: FeedbackPosition -> Boolean
isTopCenter TopCenter = true
isTopCenter _ = false

isTopRight :: FeedbackPosition -> Boolean
isTopRight TopRight = true
isTopRight _ = false

isBottomLeft :: FeedbackPosition -> Boolean
isBottomLeft BottomLeft = true
isBottomLeft _ = false

isBottomCenter :: FeedbackPosition -> Boolean
isBottomCenter BottomCenter = true
isBottomCenter _ = false

isBottomRight :: FeedbackPosition -> Boolean
isBottomRight BottomRight = true
isBottomRight _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display duration for auto-dismissing feedback
data FeedbackDuration
  = DurationShort       -- ^ ~2 seconds
  | DurationMedium      -- ^ ~4 seconds
  | DurationLong        -- ^ ~8 seconds
  | DurationPersistent  -- ^ Never auto-dismiss

derive instance eqFeedbackDuration :: Eq FeedbackDuration
derive instance ordFeedbackDuration :: Ord FeedbackDuration

instance showFeedbackDuration :: Show FeedbackDuration where
  show DurationShort = "short"
  show DurationMedium = "medium"
  show DurationLong = "long"
  show DurationPersistent = "persistent"

isShort :: FeedbackDuration -> Boolean
isShort DurationShort = true
isShort _ = false

isMedium :: FeedbackDuration -> Boolean
isMedium DurationMedium = true
isMedium _ = false

isLong :: FeedbackDuration -> Boolean
isLong DurationLong = true
isLong _ = false

isPersistent :: FeedbackDuration -> Boolean
isPersistent DurationPersistent = true
isPersistent _ = false

-- | Get duration in milliseconds
durationMs :: FeedbackDuration -> Maybe Number
durationMs DurationShort = Just 2000.0
durationMs DurationMedium = Just 4000.0
durationMs DurationLong = Just 8000.0
durationMs DurationPersistent = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // dismissal
-- ═════════════════════════════════════════════════════════════════════════════

-- | How feedback can be dismissed
data DismissalMethod
  = AutoDismiss     -- ^ Dismissed after duration
  | ManualDismiss   -- ^ Requires explicit close action
  | ActionDismiss   -- ^ Dismissed when action taken
  | SwipeDismiss    -- ^ Can be swiped away (mobile)

derive instance eqDismissalMethod :: Eq DismissalMethod
derive instance ordDismissalMethod :: Ord DismissalMethod

instance showDismissalMethod :: Show DismissalMethod where
  show AutoDismiss = "auto"
  show ManualDismiss = "manual"
  show ActionDismiss = "action"
  show SwipeDismiss = "swipe"

isAutoDismiss :: DismissalMethod -> Boolean
isAutoDismiss AutoDismiss = true
isAutoDismiss _ = false

isManualDismiss :: DismissalMethod -> Boolean
isManualDismiss ManualDismiss = true
isManualDismiss _ = false

isActionDismiss :: DismissalMethod -> Boolean
isActionDismiss ActionDismiss = true
isActionDismiss _ = false

isSwipeDismiss :: DismissalMethod -> Boolean
isSwipeDismiss SwipeDismiss = true
isSwipeDismiss _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // action button
-- ═════════════════════════════════════════════════════════════════════════════

-- | Action button for feedback
type FeedbackAction =
  { label :: String
  , actionId :: String
  , dismissOnAction :: Boolean
  }

-- | Create feedback action
feedbackAction :: String -> String -> Boolean -> FeedbackAction
feedbackAction label actionId dismissOnAction =
  { label, actionId, dismissOnAction }

-- | Standard undo action
undoAction :: FeedbackAction
undoAction = feedbackAction "Undo" "undo" true

-- | Standard retry action
retryAction :: FeedbackAction
retryAction = feedbackAction "Retry" "retry" true

-- | Standard dismiss action
dismissAction :: FeedbackAction
dismissAction = feedbackAction "Dismiss" "dismiss" true

-- | Get action label
actionLabel :: FeedbackAction -> String
actionLabel a = a.label

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Should auto-dismiss based on duration?
shouldAutoDismiss :: FeedbackDuration -> Boolean
shouldAutoDismiss DurationPersistent = false
shouldAutoDismiss _ = true
