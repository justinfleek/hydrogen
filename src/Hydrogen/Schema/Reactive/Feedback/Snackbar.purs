-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // reactive // feedback // snackbar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Snackbar - brief notification with optional action molecule.
-- |
-- | Snackbars provide brief messages with an optional action,
-- | typically used for undo operations or quick responses.

module Hydrogen.Schema.Reactive.Feedback.Snackbar
  ( -- * Snackbar (Molecule)
    Snackbar
  , snackbar
  , snackbarWithAction
  , snackbarWithUndo
  -- * Computed Properties
  , hasAction
  ) where

import Data.Maybe (Maybe(Just, Nothing), isJust)

import Hydrogen.Schema.Reactive.Feedback.Types
  ( FeedbackAction
  , FeedbackDuration(DurationMedium)
  , FeedbackPosition(BottomCenter)
  , undoAction
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // snackbar molecule
-- ═════════════════════════════════════════════════════════════════════════════

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Does snackbar have an action?
hasAction :: Snackbar -> Boolean
hasAction sb = isJust sb.action
