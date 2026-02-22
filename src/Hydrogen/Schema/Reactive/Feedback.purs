-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // reactive // feedback
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Feedback - notification and messaging atoms.
-- |
-- | Models toast, snackbar, banner, alert, and dialog patterns
-- | for user feedback and system messaging.

module Hydrogen.Schema.Reactive.Feedback
  ( -- * Feedback Type
    FeedbackType(..)
  , isToast
  , isSnackbar
  , isBanner
  , isAlert
  , isDialog
  -- * Feedback Severity
  , FeedbackSeverity(..)
  , isFeedbackSuccess
  , isFeedbackInfo
  , isFeedbackWarning
  , isFeedbackError
  , isFeedbackNeutral
  -- * Feedback Position
  , FeedbackPosition(..)
  , isTopLeft
  , isTopCenter
  , isTopRight
  , isBottomLeft
  , isBottomCenter
  , isBottomRight
  -- * Duration
  , FeedbackDuration(..)
  , isShort
  , isMedium
  , isLong
  , isPersistent
  , durationMs
  -- * Dismissal
  , DismissalMethod(..)
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
  -- * Toast (Molecule)
  , Toast
  , toast
  , successToast
  , errorToast
  , infoToast
  , warningToast
  -- * Snackbar (Molecule)
  , Snackbar
  , snackbar
  , snackbarWithAction
  , snackbarWithUndo
  -- * Banner (Molecule)
  , Banner
  , banner
  , infoBanner
  , warningBanner
  , errorBanner
  -- * Alert (Molecule)
  , Alert
  , alert
  , inlineAlert
  , alertWithActions
  -- * Dialog (Compound)
  , DialogType(..)
  , isConfirmDialog
  , isAlertDialog
  , isPromptDialog
  , Dialog
  , dialog
  , confirmDialog
  , alertDialog
  , destructiveDialog
  -- * Notification Queue (Compound)
  , NotificationQueue
  , emptyQueue
  , enqueue
  , dequeue
  , queueLength
  , currentNotification
  -- * Computed Properties
  , shouldAutoDismiss
  , hasAction
  , isBlocking
  ) where

import Prelude

import Data.Array (drop, head, length, snoc)
import Data.Maybe (Maybe(..), isJust)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // feedback type
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // feedback severity
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // feedback position
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // dismissal
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // action button
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // toast molecule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Toast notification
type Toast =
  { id :: String
  , message :: String
  , severity :: FeedbackSeverity
  , duration :: FeedbackDuration
  , position :: FeedbackPosition
  , dismissible :: Boolean
  }

-- | Create toast
toast :: String -> String -> FeedbackSeverity -> Toast
toast id message severity =
  { id
  , message
  , severity
  , duration: DurationMedium
  , position: BottomCenter
  , dismissible: true
  }

-- | Success toast
successToast :: String -> String -> Toast
successToast id message = toast id message FeedbackSuccess

-- | Error toast
errorToast :: String -> String -> Toast
errorToast id message = (toast id message FeedbackError)
  { duration = DurationLong }

-- | Info toast
infoToast :: String -> String -> Toast
infoToast id message = toast id message FeedbackInfo

-- | Warning toast
warningToast :: String -> String -> Toast
warningToast id message = toast id message FeedbackWarning

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // snackbar molecule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Snackbar notification (with optional action)
type Snackbar =
  { id :: String
  , message :: String
  , action :: Maybe FeedbackAction
  , duration :: FeedbackDuration
  , position :: FeedbackPosition
  }

-- | Create snackbar
snackbar :: String -> String -> Snackbar
snackbar id message =
  { id
  , message
  , action: Nothing
  , duration: DurationMedium
  , position: BottomCenter
  }

-- | Snackbar with action
snackbarWithAction :: String -> String -> FeedbackAction -> Snackbar
snackbarWithAction id message action =
  (snackbar id message) { action = Just action }

-- | Snackbar with undo action
snackbarWithUndo :: String -> String -> Snackbar
snackbarWithUndo id message = snackbarWithAction id message undoAction

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // banner molecule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Banner notification (persistent, full-width)
type Banner =
  { id :: String
  , message :: String
  , severity :: FeedbackSeverity
  , dismissible :: Boolean
  , action :: Maybe FeedbackAction
  , position :: FeedbackPosition  -- ^ TopCenter or BottomCenter typically
  }

-- | Create banner
banner :: String -> String -> FeedbackSeverity -> Banner
banner id message severity =
  { id
  , message
  , severity
  , dismissible: true
  , action: Nothing
  , position: TopCenter
  }

-- | Info banner
infoBanner :: String -> String -> Banner
infoBanner id message = banner id message FeedbackInfo

-- | Warning banner
warningBanner :: String -> String -> Banner
warningBanner id message = banner id message FeedbackWarning

-- | Error banner
errorBanner :: String -> String -> Banner
errorBanner id message = (banner id message FeedbackError)
  { dismissible = false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // alert molecule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Inline alert
type Alert =
  { id :: String
  , title :: Maybe String
  , message :: String
  , severity :: FeedbackSeverity
  , dismissible :: Boolean
  , actions :: Array FeedbackAction
  }

-- | Create alert
alert :: String -> String -> FeedbackSeverity -> Alert
alert id message severity =
  { id
  , title: Nothing
  , message
  , severity
  , dismissible: false
  , actions: []
  }

-- | Inline alert (within content)
inlineAlert :: String -> String -> String -> FeedbackSeverity -> Alert
inlineAlert id title message severity =
  (alert id message severity) { title = Just title }

-- | Alert with actions
alertWithActions :: String -> String -> FeedbackSeverity -> Array FeedbackAction -> Alert
alertWithActions id message severity actions =
  (alert id message severity) { actions = actions }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // dialog compound
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dialog type
data DialogType
  = ConfirmDialog    -- ^ Yes/No or OK/Cancel
  | AlertDialogType  -- ^ Informational with OK only
  | PromptDialog     -- ^ Requires input

derive instance eqDialogType :: Eq DialogType
derive instance ordDialogType :: Ord DialogType

instance showDialogType :: Show DialogType where
  show ConfirmDialog = "confirm"
  show AlertDialogType = "alert"
  show PromptDialog = "prompt"

isConfirmDialog :: DialogType -> Boolean
isConfirmDialog ConfirmDialog = true
isConfirmDialog _ = false

isAlertDialog :: DialogType -> Boolean
isAlertDialog AlertDialogType = true
isAlertDialog _ = false

isPromptDialog :: DialogType -> Boolean
isPromptDialog PromptDialog = true
isPromptDialog _ = false

-- | Modal dialog
type Dialog =
  { id :: String
  , dialogType :: DialogType
  , title :: String
  , message :: String
  , severity :: FeedbackSeverity
  , confirmLabel :: String
  , cancelLabel :: Maybe String
  , isDestructive :: Boolean
  , isOpen :: Boolean
  }

-- | Create dialog
dialog :: String -> DialogType -> String -> String -> Dialog
dialog id dialogType title message =
  { id
  , dialogType
  , title
  , message
  , severity: FeedbackNeutral
  , confirmLabel: "OK"
  , cancelLabel: Nothing
  , isDestructive: false
  , isOpen: false
  }

-- | Confirm dialog
confirmDialog :: String -> String -> String -> Dialog
confirmDialog id title message =
  (dialog id ConfirmDialog title message)
    { cancelLabel = Just "Cancel"
    , confirmLabel = "Confirm"
    }

-- | Alert dialog
alertDialog :: String -> String -> String -> Dialog
alertDialog id title message = dialog id AlertDialogType title message

-- | Destructive confirm dialog (red confirm button)
destructiveDialog :: String -> String -> String -> Dialog
destructiveDialog id title message =
  (confirmDialog id title message)
    { isDestructive = true
    , severity = FeedbackError
    , confirmLabel = "Delete"
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // notification queue compound
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Queue of pending notifications
type NotificationQueue =
  { items :: Array Toast
  , maxVisible :: Int
  }

-- | Empty notification queue
emptyQueue :: Int -> NotificationQueue
emptyQueue maxVisible =
  { items: []
  , maxVisible
  }

-- | Add notification to queue
enqueue :: Toast -> NotificationQueue -> NotificationQueue
enqueue item queue =
  queue { items = snoc queue.items item }

-- | Remove oldest notification
dequeue :: NotificationQueue -> NotificationQueue
dequeue queue =
  queue { items = drop 1 queue.items }

-- | Get queue length
queueLength :: NotificationQueue -> Int
queueLength queue = length queue.items

-- | Get current notification (head of queue)
currentNotification :: NotificationQueue -> Maybe Toast
currentNotification queue = head queue.items

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Should auto-dismiss based on duration?
shouldAutoDismiss :: FeedbackDuration -> Boolean
shouldAutoDismiss DurationPersistent = false
shouldAutoDismiss _ = true

-- | Does feedback have an action?
hasAction :: Snackbar -> Boolean
hasAction sb = isJust sb.action

-- | Is feedback blocking (modal)?
isBlocking :: Dialog -> Boolean
isBlocking _ = true  -- Dialogs are always blocking
