-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // reactive // feedback // alert
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Alert - inline notification molecule.
-- |
-- | Alerts display contextual messages within content,
-- | providing warnings, errors, or informational messages
-- | without interrupting workflow.

module Hydrogen.Schema.Reactive.Feedback.Alert
  ( -- * Alert (Molecule)
    Alert
  , alert
  , inlineAlert
  , alertWithActions
  ) where

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.Feedback.Types
  ( FeedbackAction
  , FeedbackSeverity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // alert molecule
-- ═════════════════════════════════════════════════════════════════════════════

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
