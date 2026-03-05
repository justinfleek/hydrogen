-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // element // input // behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | InputBehavior — Interaction atoms for input response.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - Milliseconds (Dimension.Temporal) — Verified timing
-- |
-- | ## Input Behavior Model
-- |
-- | An input responds to:
-- | - Typing: Character input with optional masking
-- | - Paste: Clipboard content
-- | - Selection: Text selection for copy
-- | - Clear: Clear button or Escape key
-- | - Submit: Enter key behavior
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Dimension.Temporal (Milliseconds)

module Hydrogen.Schema.Element.Input.Behavior
  ( -- * Input Behavior Record
    InputBehavior
  , defaultBehavior
  , passwordBehavior
  , searchBehavior
  , formBehavior
  
  -- * Behavior Accessors
  , getDebounceMs
  , isAutoFocus
  , isAutoComplete
  , isAutoCapitalize
  , isAutoCorrect
  , isSpellCheck
  , hasClearButton
  , isSelectOnFocus
  , submitOnEnter
  
  -- * Behavior Modifiers
  , setDebounceMs
  , setAutoFocus
  , setAutoComplete
  , setAutoCapitalize
  , setAutoCorrect
  , setSpellCheck
  , enableClearButton
  , disableClearButton
  , setSelectOnFocus
  , setSubmitOnEnter
  
  -- * Re-exports
  , module Hydrogen.Schema.Dimension.Temporal
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Prim (Boolean, Number, String)

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Dimension.Temporal
  ( Milliseconds(Milliseconds)
  , milliseconds
  , unwrapMilliseconds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // input behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete input behavior — all interaction properties.
-- |
-- | ## Verified Bounds
-- |
-- | - debounceMs: bounded [0-1000] ms
-- | - All boolean flags as explicit
-- |
-- | ## Interaction Modes
-- |
-- | - onChange debounce: Delay before emitting change events
-- | - autoFocus: Focus on mount
-- | - clearButton: Show clear (X) button
-- | - selectOnFocus: Select all text on focus
-- | - submitOnEnter: Emit submit on Enter key
type InputBehavior =
  { -- Timing
    debounceMs :: Milliseconds         -- ^ Debounce onChange events
    -- Focus behavior
  , autoFocus :: Boolean               -- ^ Focus on mount
  , selectOnFocus :: Boolean           -- ^ Select all on focus
    -- Clear button
  , showClearButton :: Boolean         -- ^ Show clear (X) button
  , clearOnEscape :: Boolean           -- ^ Clear on Escape key
    -- Submit behavior
  , submitOnEnter :: Boolean           -- ^ Submit on Enter key
  , blurOnSubmit :: Boolean            -- ^ Blur after submit
    -- Auto-* attributes
  , autoComplete :: Maybe String       -- ^ Autocomplete hint (e.g., "email", "off")
  , autoCapitalize :: Boolean          -- ^ Auto-capitalize on mobile
  , autoCorrect :: Boolean             -- ^ Auto-correct spelling
  , spellCheck :: Boolean              -- ^ Enable spell check
    -- Input mode (mobile keyboard)
  , inputMode :: Maybe String          -- ^ Input mode hint (e.g., "numeric", "email")
  }

-- | Default input behavior — no debounce, standard settings.
defaultBehavior :: InputBehavior
defaultBehavior =
  { debounceMs: milliseconds 0.0
  , autoFocus: false
  , selectOnFocus: false
  , showClearButton: false
  , clearOnEscape: true
  , submitOnEnter: false
  , blurOnSubmit: false
  , autoComplete: Nothing
  , autoCapitalize: true
  , autoCorrect: true
  , spellCheck: true
  , inputMode: Nothing
  }

-- | Password input behavior — no autocomplete, no spellcheck.
passwordBehavior :: InputBehavior
passwordBehavior = defaultBehavior
  { autoComplete = Just "current-password"
  , autoCapitalize = false
  , autoCorrect = false
  , spellCheck = false
  }

-- | Search input behavior — clear button, submit on enter.
searchBehavior :: InputBehavior
searchBehavior = defaultBehavior
  { showClearButton = true
  , submitOnEnter = true
  , debounceMs = milliseconds 300.0  -- Debounce search
  , inputMode = Just "search"
  }

-- | Form input behavior — submit on enter, blur after.
formBehavior :: InputBehavior
formBehavior = defaultBehavior
  { submitOnEnter = true
  , blurOnSubmit = true
  , selectOnFocus = true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get debounce time in milliseconds (bounded 0-1000).
getDebounceMs :: InputBehavior -> Milliseconds
getDebounceMs b = 
  let (Milliseconds ms) = b.debounceMs
  in milliseconds (Bounded.clampNumber 0.0 1000.0 ms)

-- | Should input auto-focus on mount?
isAutoFocus :: InputBehavior -> Boolean
isAutoFocus b = b.autoFocus

-- | Get autocomplete setting.
isAutoComplete :: InputBehavior -> Maybe String
isAutoComplete b = b.autoComplete

-- | Is auto-capitalize enabled?
isAutoCapitalize :: InputBehavior -> Boolean
isAutoCapitalize b = b.autoCapitalize

-- | Is auto-correct enabled?
isAutoCorrect :: InputBehavior -> Boolean
isAutoCorrect b = b.autoCorrect

-- | Is spell check enabled?
isSpellCheck :: InputBehavior -> Boolean
isSpellCheck b = b.spellCheck

-- | Is clear button shown?
hasClearButton :: InputBehavior -> Boolean
hasClearButton b = b.showClearButton

-- | Should select all on focus?
isSelectOnFocus :: InputBehavior -> Boolean
isSelectOnFocus b = b.selectOnFocus

-- | Should submit on Enter key?
submitOnEnter :: InputBehavior -> Boolean
submitOnEnter b = b.submitOnEnter

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set debounce time (bounded 0-1000ms).
setDebounceMs :: Number -> InputBehavior -> InputBehavior
setDebounceMs ms b = 
  b { debounceMs = milliseconds (Bounded.clampNumber 0.0 1000.0 ms) }

-- | Set auto-focus.
setAutoFocus :: Boolean -> InputBehavior -> InputBehavior
setAutoFocus v b = b { autoFocus = v }

-- | Set autocomplete hint.
setAutoComplete :: String -> InputBehavior -> InputBehavior
setAutoComplete v b = b { autoComplete = Just v }

-- | Set auto-capitalize.
setAutoCapitalize :: Boolean -> InputBehavior -> InputBehavior
setAutoCapitalize v b = b { autoCapitalize = v }

-- | Set auto-correct.
setAutoCorrect :: Boolean -> InputBehavior -> InputBehavior
setAutoCorrect v b = b { autoCorrect = v }

-- | Set spell check.
setSpellCheck :: Boolean -> InputBehavior -> InputBehavior
setSpellCheck v b = b { spellCheck = v }

-- | Enable clear button.
enableClearButton :: InputBehavior -> InputBehavior
enableClearButton b = b { showClearButton = true }

-- | Disable clear button.
disableClearButton :: InputBehavior -> InputBehavior
disableClearButton b = b { showClearButton = false }

-- | Set select-on-focus.
setSelectOnFocus :: Boolean -> InputBehavior -> InputBehavior
setSelectOnFocus v b = b { selectOnFocus = v }

-- | Set submit-on-enter.
setSubmitOnEnter :: Boolean -> InputBehavior -> InputBehavior
setSubmitOnEnter v b = b { submitOnEnter = v }
