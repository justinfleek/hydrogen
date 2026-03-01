-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // tour // navigation // closebutton
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Close Button Configuration for Tours
-- |
-- | This module provides close button types and configuration:
-- | - Position (top-right, top-left, in-header)
-- | - Style (icon, text, icon with label)
-- | - Accessibility labels
module Hydrogen.Tour.Navigation.CloseButton
  ( -- * Close Button Configuration
    CloseButtonConfig
  , defaultCloseConfig
  , CloseButtonPosition(..)
  , CloseButtonStyle(..)
  ) where

import Prelude (class Eq, class Show)

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // close button
-- ═════════════════════════════════════════════════════════════════════════════

-- | Close button configuration
type CloseButtonConfig =
  { visible :: Boolean
  , position :: CloseButtonPosition
  , style :: CloseButtonStyle
  , label :: String
    -- ^ Accessible label
  }

-- | Close button position
data CloseButtonPosition
  = CloseTopRight
  | CloseTopLeft
  | CloseInHeader

derive instance eqCloseButtonPosition :: Eq CloseButtonPosition
derive instance genericCloseButtonPosition :: Generic CloseButtonPosition _

instance showCloseButtonPosition :: Show CloseButtonPosition where
  show = genericShow

-- | Close button style
data CloseButtonStyle
  = CloseIcon
    -- ^ X icon only
  | CloseText
    -- ^ "Close" text
  | CloseIconWithLabel
    -- ^ Icon + "Close"

derive instance eqCloseButtonStyle :: Eq CloseButtonStyle
derive instance genericCloseButtonStyle :: Generic CloseButtonStyle _

instance showCloseButtonStyle :: Show CloseButtonStyle where
  show = genericShow

-- | Default close button configuration
defaultCloseConfig :: CloseButtonConfig
defaultCloseConfig =
  { visible: true
  , position: CloseTopRight
  , style: CloseIcon
  , label: "Close tour"
  }
