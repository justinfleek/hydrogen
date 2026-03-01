-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // reactive // feedback // dialog
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dialog - modal dialog compound.
-- |
-- | Dialogs interrupt workflow to request user confirmation,
-- | display critical information, or prompt for input.
-- | They are blocking and require explicit dismissal.

module Hydrogen.Schema.Reactive.Feedback.Dialog
  ( -- * Dialog Type
    DialogType(..)
  , isConfirmDialog
  , isAlertDialog
  , isPromptDialog
  -- * Dialog (Compound)
  , Dialog
  , dialog
  , confirmDialog
  , alertDialog
  , destructiveDialog
  -- * Computed Properties
  , isBlocking
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.Feedback.Types
  ( FeedbackSeverity(FeedbackError, FeedbackNeutral)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // dialog compound
-- ═════════════════════════════════════════════════════════════════════════════

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is feedback blocking (modal)?
isBlocking :: Dialog -> Boolean
isBlocking _ = true  -- Dialogs are always blocking
