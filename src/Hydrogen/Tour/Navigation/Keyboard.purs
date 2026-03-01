-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // tour // navigation // keyboard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyboard Navigation Configuration for Tours
-- |
-- | This module provides keyboard navigation types and configuration:
-- | - Key bindings (arrow keys, escape, tab)
-- | - Key actions (next, prev, dismiss)
-- | - Modifiers (ctrl, shift, alt, meta)
module Hydrogen.Tour.Navigation.Keyboard
  ( -- * Keyboard Configuration
    KeyboardConfig
  , defaultKeyboardConfig
    -- * Key Bindings
  , KeyBinding
  , KeyAction(KeyNext, KeyPrev, KeyDismiss, KeyComplete, KeyGoToStep)
  , KeyModifier(ModCtrl, ModShift, ModAlt, ModMeta)
  , defaultKeyBindings
    -- * Configuration Builders
  , withArrowNav
  , withEscapeDismiss
  , withTabNav
  ) where

import Prelude (class Eq, class Show, (&&), (<>), (/=))

import Data.Array (filter)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // keyboard configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyboard navigation configuration
type KeyboardConfig =
  { enabled :: Boolean
  , bindings :: Array KeyBinding
  , trapFocus :: Boolean
    -- ^ Keep focus within tour tooltip
  , announceToScreenReader :: Boolean
  }

-- | Key binding
type KeyBinding =
  { key :: String
    -- ^ Key name (e.g., "ArrowRight", "Escape")
  , action :: KeyAction
  , requireModifier :: Maybe KeyModifier
  }

-- | Key action
data KeyAction
  = KeyNext
  | KeyPrev
  | KeyDismiss
  | KeyComplete
  | KeyGoToStep Int

derive instance eqKeyAction :: Eq KeyAction
derive instance genericKeyAction :: Generic KeyAction _

instance showKeyAction :: Show KeyAction where
  show = genericShow

-- | Key modifier
data KeyModifier
  = ModCtrl
  | ModShift
  | ModAlt
  | ModMeta

derive instance eqKeyModifier :: Eq KeyModifier
derive instance genericKeyModifier :: Generic KeyModifier _

instance showKeyModifier :: Show KeyModifier where
  show = genericShow

-- | Default keyboard configuration
defaultKeyboardConfig :: KeyboardConfig
defaultKeyboardConfig =
  { enabled: true
  , bindings: defaultKeyBindings
  , trapFocus: true
  , announceToScreenReader: true
  }

-- | Default key bindings
defaultKeyBindings :: Array KeyBinding
defaultKeyBindings =
  [ { key: "ArrowRight", action: KeyNext, requireModifier: Nothing }
  , { key: "ArrowLeft", action: KeyPrev, requireModifier: Nothing }
  , { key: "Escape", action: KeyDismiss, requireModifier: Nothing }
  , { key: "Enter", action: KeyNext, requireModifier: Nothing }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // configuration builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable arrow key navigation
withArrowNav :: Boolean -> KeyboardConfig -> KeyboardConfig
withArrowNav enabled cfg =
  let
    arrowBindings :: Array KeyBinding
    arrowBindings =
      [ { key: "ArrowRight", action: KeyNext, requireModifier: Nothing }
      , { key: "ArrowLeft", action: KeyPrev, requireModifier: Nothing }
      ]
    
    filterOutArrows :: Array KeyBinding -> Array KeyBinding
    filterOutArrows = filter (\b -> b.key /= "ArrowRight" && b.key /= "ArrowLeft")
  in
    if enabled
    then cfg { bindings = cfg.bindings <> arrowBindings }
    else cfg { bindings = filterOutArrows cfg.bindings }

-- | Enable escape to dismiss
withEscapeDismiss :: Boolean -> KeyboardConfig -> KeyboardConfig
withEscapeDismiss enabled cfg =
  let
    escBinding :: KeyBinding
    escBinding = { key: "Escape", action: KeyDismiss, requireModifier: Nothing }
    
    filterOutEscape :: Array KeyBinding -> Array KeyBinding
    filterOutEscape = filter (\b -> b.key /= "Escape")
  in
    if enabled
    then cfg { bindings = cfg.bindings <> [escBinding] }
    else cfg { bindings = filterOutEscape cfg.bindings }

-- | Enable tab navigation between steps
withTabNav :: Boolean -> KeyboardConfig -> KeyboardConfig
withTabNav enabled cfg =
  let
    tabBindings :: Array KeyBinding
    tabBindings =
      [ { key: "Tab", action: KeyNext, requireModifier: Nothing }
      , { key: "Tab", action: KeyPrev, requireModifier: Just ModShift }
      ]
    
    filterOutTab :: Array KeyBinding -> Array KeyBinding
    filterOutTab = filter (\b -> b.key /= "Tab")
  in
    if enabled
    then cfg { bindings = cfg.bindings <> tabBindings }
    else cfg { bindings = filterOutTab cfg.bindings }
