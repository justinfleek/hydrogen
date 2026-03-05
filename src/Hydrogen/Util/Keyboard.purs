-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // keyboard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyboard shortcut configuration and parsing.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.Keyboard as Keyboard
-- |
-- | saveShortcut :: ShortcutBinding
-- | saveShortcut = Keyboard.parseBinding "Ctrl+S" "Save document"
-- |
-- | customShortcut :: ShortcutBinding
-- | customShortcut = Keyboard.binding "K"
-- |   # Keyboard.withCtrl
-- |   # Keyboard.withDescription "Open command palette"
-- | ```
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Gestural.Keyboard
-- |
-- | ## Dependents
-- | - Element shortcut configuration
-- | - Command palette
-- | - Help dialog shortcut display

module Hydrogen.Util.Keyboard
  ( -- * Types
    ShortcutBinding
  , Modifier(Ctrl, Alt, Shift, Meta)
  , Scope(Scope)
  , ShortcutConfig
    -- * Binding Creation
  , binding
  , parseBinding
    -- * Modifier Builders
  , withCtrl
  , withAlt
  , withShift
  , withMeta
  , withModifiers
    -- * Config Builders
  , withDescription
  , withPreventDefault
  , withStopPropagation
  , withIgnoreInputs
    -- * Scope
  , globalScope
  , createScope
    -- * Formatting
  , formatBinding
  , formatKey
  , formatModifier
    -- * Predicates
  , hasCtrl
  , hasAlt
  , hasShift
  , hasMeta
  , hasModifier
    -- * Re-exports from Schema
  , module SchemaShortcut
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , not
  , show
  , ($)
  , (&&)
  , (<>)
  , (==)
  , (>>>)
  , (<<<)
  )

import Data.Array (elem, filter)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String
import Data.String.Pattern (Pattern(Pattern))

import Hydrogen.Schema.Gestural.Keyboard.Shortcut
  ( Shortcut
  , shortcut
  , simpleShortcut
  , ctrlShortcut
  , ctrlShiftShortcut
  , altShortcut
  , altShiftShortcut
  , metaShortcut
  , metaShiftShortcut
  , matchesShortcut
  , matchesShortcutLoose
  , shortcutCopy
  , shortcutCut
  , shortcutPaste
  , shortcutUndo
  , shortcutRedo
  , shortcutSelectAll
  , shortcutSave
  , shortcutFind
  , shortcutClose
  , shortcutNew
  , shortcutOpen
  , shortcutRedoY
  ) as SchemaShortcut

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A keyboard shortcut binding with metadata.
type ShortcutBinding =
  { key :: String
  , modifiers :: Array Modifier
  , config :: ShortcutConfig
  , scope :: Scope
  }

-- | Shortcut configuration
type ShortcutConfig =
  { preventDefault :: Boolean
  , stopPropagation :: Boolean
  , ignoreInputs :: Boolean
  , description :: String
  }

-- | Keyboard modifiers
data Modifier
  = Ctrl
  | Alt
  | Shift
  | Meta

derive instance eqModifier :: Eq Modifier
derive instance ordModifier :: Ord Modifier

instance showModifier :: Show Modifier where
  show Ctrl = "Ctrl"
  show Alt = "Alt"
  show Shift = "Shift"
  show Meta = "Meta"

-- | Scope for scoped shortcuts
newtype Scope = Scope String

derive instance eqScope :: Eq Scope
derive instance ordScope :: Ord Scope

instance showScope :: Show Scope where
  show (Scope s) = "Scope(" <> s <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

defaultConfig :: ShortcutConfig
defaultConfig =
  { preventDefault: true
  , stopPropagation: false
  , ignoreInputs: true
  , description: ""
  }

-- | Global scope (always active)
globalScope :: Scope
globalScope = Scope "global"

-- | Create a named scope
createScope :: String -> Scope
createScope = Scope

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // binding creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a binding from a key
binding :: String -> ShortcutBinding
binding key =
  { key
  , modifiers: []
  , config: defaultConfig
  , scope: globalScope
  }

-- | Parse a shortcut string into a binding
-- |
-- | Supports formats: "Ctrl+K", "Cmd+Shift+P", "Alt+1"
-- | Uses "Cmd" as alias for Meta.
parseBinding :: String -> String -> ShortcutBinding
parseBinding str description =
  let
    parts = String.split (Pattern "+") str
    mods = filter isModifier parts
    keys = filter (not <<< isModifier) parts
    key = case keys of
      [k] -> k
      _ -> ""
  in
    { key
    , modifiers: parseModifiers mods
    , config: defaultConfig { description = description }
    , scope: globalScope
    }
  where
  isModifier :: String -> Boolean
  isModifier s = elem (String.toLower s) ["ctrl", "alt", "shift", "meta", "cmd"]
  
  parseModifiers :: Array String -> Array Modifier
  parseModifiers = map parseModifier >>> filter isJust >>> map unsafeFromJust
  
  parseModifier :: String -> Maybe Modifier
  parseModifier s = case String.toLower s of
    "ctrl" -> Just Ctrl
    "alt" -> Just Alt
    "shift" -> Just Shift
    "meta" -> Just Meta
    "cmd" -> Just Meta
    _ -> Nothing
  
  isJust :: forall a. Maybe a -> Boolean
  isJust (Just _) = true
  isJust Nothing = false
  
  unsafeFromJust :: forall a. Maybe a -> a
  unsafeFromJust (Just a) = a
  unsafeFromJust Nothing = unsafeFromJust Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // modifier builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add Ctrl modifier
withCtrl :: ShortcutBinding -> ShortcutBinding
withCtrl s = s { modifiers = s.modifiers <> [Ctrl] }

-- | Add Alt modifier
withAlt :: ShortcutBinding -> ShortcutBinding
withAlt s = s { modifiers = s.modifiers <> [Alt] }

-- | Add Shift modifier
withShift :: ShortcutBinding -> ShortcutBinding
withShift s = s { modifiers = s.modifiers <> [Shift] }

-- | Add Meta modifier (Cmd on Mac)
withMeta :: ShortcutBinding -> ShortcutBinding
withMeta s = s { modifiers = s.modifiers <> [Meta] }

-- | Add multiple modifiers
withModifiers :: Array Modifier -> ShortcutBinding -> ShortcutBinding
withModifiers mods s = s { modifiers = s.modifiers <> mods }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // config builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set description
withDescription :: String -> ShortcutBinding -> ShortcutBinding
withDescription desc s = s { config = s.config { description = desc } }

-- | Enable preventDefault
withPreventDefault :: ShortcutBinding -> ShortcutBinding
withPreventDefault s = s { config = s.config { preventDefault = true } }

-- | Enable stopPropagation
withStopPropagation :: ShortcutBinding -> ShortcutBinding
withStopPropagation s = s { config = s.config { stopPropagation = true } }

-- | Enable ignoreInputs
withIgnoreInputs :: ShortcutBinding -> ShortcutBinding
withIgnoreInputs s = s { config = s.config { ignoreInputs = true } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format binding for display
formatBinding :: ShortcutBinding -> String
formatBinding s =
  let
    modStrs = map formatModifier s.modifiers
    parts = modStrs <> [s.key]
  in
    String.joinWith "+" parts

-- | Format a key for display
formatKey :: String -> String
formatKey = String.toUpper

-- | Format a modifier for display
formatModifier :: Modifier -> String
formatModifier = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if binding has Ctrl modifier
hasCtrl :: ShortcutBinding -> Boolean
hasCtrl s = elem Ctrl s.modifiers

-- | Check if binding has Alt modifier
hasAlt :: ShortcutBinding -> Boolean
hasAlt s = elem Alt s.modifiers

-- | Check if binding has Shift modifier
hasShift :: ShortcutBinding -> Boolean
hasShift s = elem Shift s.modifiers

-- | Check if binding has Meta modifier
hasMeta :: ShortcutBinding -> Boolean
hasMeta s = elem Meta s.modifiers

-- | Check if binding has a specific modifier
hasModifier :: Modifier -> ShortcutBinding -> Boolean
hasModifier m s = elem m s.modifiers
