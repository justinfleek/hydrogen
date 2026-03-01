-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // reactive // feedback // toast
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toast - brief, non-blocking notification molecule.
-- |
-- | Toasts appear briefly to confirm actions or provide
-- | non-critical information without interrupting workflow.

module Hydrogen.Schema.Reactive.Feedback.Toast
  ( -- * Toast (Molecule)
    Toast
  , toast
  , successToast
  , errorToast
  , infoToast
  , warningToast
  ) where

import Hydrogen.Schema.Reactive.Feedback.Types
  ( FeedbackDuration(DurationLong, DurationMedium)
  , FeedbackPosition(BottomCenter)
  , FeedbackSeverity(FeedbackError, FeedbackInfo, FeedbackSuccess, FeedbackWarning)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // toast molecule
-- ═════════════════════════════════════════════════════════════════════════════

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
