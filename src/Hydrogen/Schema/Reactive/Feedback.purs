-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // reactive // feedback
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Feedback - notification and messaging atoms.
-- |
-- | Leader module re-exporting all feedback submodules.
-- | Models toast, snackbar, banner, alert, dialog, tooltip,
-- | popover, drawer, and sheet patterns for user feedback
-- | and system messaging.

module Hydrogen.Schema.Reactive.Feedback
  ( -- * Re-exports from Types
    module Hydrogen.Schema.Reactive.Feedback.Types
  -- * Re-exports from Toast
  , module Hydrogen.Schema.Reactive.Feedback.Toast
  -- * Re-exports from Snackbar
  , module Hydrogen.Schema.Reactive.Feedback.Snackbar
  -- * Re-exports from Banner
  , module Hydrogen.Schema.Reactive.Feedback.Banner
  -- * Re-exports from Alert
  , module Hydrogen.Schema.Reactive.Feedback.Alert
  -- * Re-exports from Dialog
  , module Hydrogen.Schema.Reactive.Feedback.Dialog
  -- * Re-exports from Queue
  , module Hydrogen.Schema.Reactive.Feedback.Queue
  -- * Re-exports from Tooltip
  , module Hydrogen.Schema.Reactive.Feedback.Tooltip
  -- * Re-exports from Popover
  , module Hydrogen.Schema.Reactive.Feedback.Popover
  -- * Re-exports from Overlay
  , module Hydrogen.Schema.Reactive.Feedback.Overlay
  ) where

import Hydrogen.Schema.Reactive.Feedback.Types
  ( FeedbackType(ToastType, SnackbarType, BannerType, AlertType, DialogType')
  , isToast
  , isSnackbar
  , isBanner
  , isAlert
  , isDialog
  , FeedbackSeverity(FeedbackSuccess, FeedbackInfo, FeedbackWarning, FeedbackError, FeedbackNeutral)
  , isFeedbackSuccess
  , isFeedbackInfo
  , isFeedbackWarning
  , isFeedbackError
  , isFeedbackNeutral
  , FeedbackPosition(TopLeft, TopCenter, TopRight, BottomLeft, BottomCenter, BottomRight)
  , isTopLeft
  , isTopCenter
  , isTopRight
  , isBottomLeft
  , isBottomCenter
  , isBottomRight
  , FeedbackDuration(DurationShort, DurationMedium, DurationLong, DurationPersistent)
  , isShort
  , isMedium
  , isLong
  , isPersistent
  , durationMs
  , DismissalMethod(AutoDismiss, ManualDismiss, ActionDismiss, SwipeDismiss)
  , isAutoDismiss
  , isManualDismiss
  , isActionDismiss
  , isSwipeDismiss
  , FeedbackAction
  , feedbackAction
  , undoAction
  , retryAction
  , dismissAction
  , actionLabel
  , shouldAutoDismiss
  )

import Hydrogen.Schema.Reactive.Feedback.Toast
  ( Toast
  , toast
  , successToast
  , errorToast
  , infoToast
  , warningToast
  )

import Hydrogen.Schema.Reactive.Feedback.Snackbar
  ( Snackbar
  , snackbar
  , snackbarWithAction
  , snackbarWithUndo
  , hasAction
  )

import Hydrogen.Schema.Reactive.Feedback.Banner
  ( Banner
  , banner
  , infoBanner
  , warningBanner
  , errorBanner
  )

import Hydrogen.Schema.Reactive.Feedback.Alert
  ( Alert
  , alert
  , inlineAlert
  , alertWithActions
  )

import Hydrogen.Schema.Reactive.Feedback.Dialog
  ( DialogType(ConfirmDialog, AlertDialogType, PromptDialog)
  , isConfirmDialog
  , isAlertDialog
  , isPromptDialog
  , Dialog
  , dialog
  , confirmDialog
  , alertDialog
  , destructiveDialog
  , isBlocking
  )

import Hydrogen.Schema.Reactive.Feedback.Queue
  ( NotificationQueue
  , emptyQueue
  , enqueue
  , dequeue
  , queueLength
  , currentNotification
  )

import Hydrogen.Schema.Reactive.Feedback.Tooltip
  ( TooltipPlacement(TooltipTop, TooltipTopStart, TooltipTopEnd, TooltipBottom, TooltipBottomStart, TooltipBottomEnd, TooltipLeft, TooltipLeftStart, TooltipLeftEnd, TooltipRight, TooltipRightStart, TooltipRightEnd)
  , Tooltip
  , tooltip
  , simpleTooltip
  , interactiveTooltip
  )

import Hydrogen.Schema.Reactive.Feedback.Popover
  ( PopoverTrigger(PopoverClick, PopoverHover, PopoverFocus, PopoverManual)
  , Popover
  , popover
  , popoverWithTitle
  , isPopoverOpen
  , openPopover
  , closePopover
  )

import Hydrogen.Schema.Reactive.Feedback.Overlay
  ( DrawerPosition(DrawerLeft, DrawerRight, DrawerTop, DrawerBottom)
  , Drawer
  , drawer
  , navigationDrawer
  , sidePanelDrawer
  , isDrawerOpen
  , openDrawer
  , closeDrawer
  , toggleDrawer
  , SheetSnapPoint(SheetMinimized, SheetPartial, SheetExpanded, SheetCustom)
  , Sheet
  , sheet
  , standardSheet
  , multiDetentSheet
  , isSheetOpen
  , openSheet
  , closeSheet
  , snapSheet
  )
