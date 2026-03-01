-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // reactive // feedback // banner
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Banner - persistent full-width notification molecule.
-- |
-- | Banners display important messages at the top or bottom
-- | of the screen, persisting until dismissed or resolved.

module Hydrogen.Schema.Reactive.Feedback.Banner
  ( -- * Banner (Molecule)
    Banner
  , banner
  , infoBanner
  , warningBanner
  , errorBanner
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Schema.Reactive.Feedback.Types
  ( FeedbackAction
  , FeedbackPosition(TopCenter)
  , FeedbackSeverity(FeedbackError, FeedbackInfo, FeedbackWarning)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // banner molecule
-- ═════════════════════════════════════════════════════════════════════════════

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
