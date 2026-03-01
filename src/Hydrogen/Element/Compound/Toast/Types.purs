-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // toast // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toast Types — Core type definitions for toast notifications.
-- |
-- | This module contains the fundamental type definitions used throughout
-- | the Toast component system.

module Hydrogen.Element.Compound.Toast.Types
  ( -- * Position Type
    ToastPosition(TopRight, TopLeft, TopCenter, BottomRight, BottomLeft, BottomCenter)
  
  -- * Action Configuration
  , ToastActionConfig
  ) where

import Prelude
  ( class Eq
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toast position on screen
-- |
-- | Determines where the toast container is anchored within the viewport.
-- | Toasts stack in the direction appropriate for each position:
-- | - Top positions: stack downward
-- | - Bottom positions: stack upward
data ToastPosition
  = TopRight
  | TopLeft
  | TopCenter
  | BottomRight
  | BottomLeft
  | BottomCenter

derive instance eqToastPosition :: Eq ToastPosition

instance showToastPosition :: Show ToastPosition where
  show TopRight = "top-right"
  show TopLeft = "top-left"
  show TopCenter = "top-center"
  show BottomRight = "bottom-right"
  show BottomLeft = "bottom-left"
  show BottomCenter = "bottom-center"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // action configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Action button configuration
-- |
-- | Defines an optional action button that can be displayed within a toast.
-- | The action provides a way for users to respond to the notification
-- | without dismissing it.
type ToastActionConfig msg =
  { label :: String
  , onAction :: msg
  }
