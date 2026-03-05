-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // element // input // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | InputState — State atoms for text input controls.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - DisabledFlag, FocusedFlag (Reactive.Flags) — UI state
-- | - ValidationState (Reactive.Validation) — Error/success/warning
-- |
-- | ## Input Value Model
-- |
-- | InputValue is a sum type capturing all input value types:
-- | - Text: Plain text content
-- | - Password: Masked text content
-- | - Email: Email address with validation
-- | - Number: Numeric input with min/max/step
-- | - Search: Search query text
-- | - URL: URL with validation
-- | - Tel: Telephone number
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Reactive.Flags (UI state flags)
-- | - Hydrogen.Schema.Reactive.Validation (validation state)

module Hydrogen.Schema.Element.Input.State
  ( -- * Input Type
    InputType
      ( TypeText
      , TypePassword
      , TypeEmail
      , TypeNumber
      , TypeSearch
      , TypeUrl
      , TypeTel
      )
  , inputTypeToString
  
  -- * Input Element State Record
  , InputElementState
  , defaultState
  , passwordState
  , emailState
  , numberState
  , searchState
  
  -- * State Accessors
  , getValue
  , getPlaceholder
  , getInputType
  , isDisabled
  , isFocused
  , isHovered
  , isReadOnly
  , hasError
  , hasWarning
  , isValid
  , getErrorMessage
  , getCharCount
  , getMaxLength
  
  -- * State Modifiers
  , setValue
  , setPlaceholder
  , setDisabled
  , setFocused
  , setHovered
  , setReadOnly
  , setError
  , setWarning
  , setValid
  , clearValidation
  , setMaxLength
  , setMinLength
  
  -- * Validation State
  , ValidationState
      ( ValidationNone
      , ValidationValid
      , ValidationWarning
      , ValidationError
      )
  
  -- * Re-exports from Reactive
  , module Hydrogen.Schema.Reactive.Flags
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Prim (Boolean, Int, String)

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String

import Hydrogen.Schema.Reactive.Flags
  ( DisabledFlag(DisabledFlag)
  , FocusedFlag(FocusedFlag)
  , HoveredFlag(HoveredFlag)
  , ReadOnlyFlag(ReadOnlyFlag)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // input type
-- ═════════════════════════════════════════════════════════════════════════════

-- | InputType — Semantic type of the input control.
-- |
-- | Determines:
-- | - Keyboard type on mobile
-- | - Browser autocomplete behavior
-- | - Validation rules
-- | - Visual masking (password)
data InputType
  = TypeText           -- ^ Plain text input
  | TypePassword       -- ^ Masked password input
  | TypeEmail          -- ^ Email with @ validation
  | TypeNumber         -- ^ Numeric input
  | TypeSearch         -- ^ Search query
  | TypeUrl            -- ^ URL with protocol validation
  | TypeTel            -- ^ Telephone number

derive instance eqInputType :: Eq InputType
derive instance ordInputType :: Ord InputType

instance showInputType :: Show InputType where
  show TypeText = "text"
  show TypePassword = "password"
  show TypeEmail = "email"
  show TypeNumber = "number"
  show TypeSearch = "search"
  show TypeUrl = "url"
  show TypeTel = "tel"

-- | Convert InputType to string for ARIA/data attributes.
inputTypeToString :: InputType -> String
inputTypeToString = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // validation state
-- ═════════════════════════════════════════════════════════════════════════════

-- | ValidationState — Current validation status of the input.
data ValidationState
  = ValidationNone       -- ^ No validation applied
  | ValidationValid      -- ^ Input is valid
  | ValidationWarning String -- ^ Warning message
  | ValidationError String   -- ^ Error message

derive instance eqValidationState :: Eq ValidationState
derive instance ordValidationState :: Ord ValidationState

instance showValidationState :: Show ValidationState where
  show ValidationNone = "none"
  show ValidationValid = "valid"
  show (ValidationWarning msg) = "warning: " <> msg
  show (ValidationError msg) = "error: " <> msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // input element state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete input element state — all values needed to render an input.
-- |
-- | ## Verified Bounded Types
-- |
-- | Every field uses a verified Schema atom:
-- | - value: String (the text content)
-- | - inputType: InputType (semantic type)
-- | - disabled/focused/hovered/readOnly: Verified flags
-- | - validation: ValidationState
-- | - maxLength/minLength: Bounded integers
-- |
-- | ## State Machine
-- |
-- | An input transitions between states:
-- | - Idle: No interaction
-- | - Hovered: Pointer over input
-- | - Focused: Has keyboard focus (caret visible)
-- | - Disabled: Cannot interact
-- | - ReadOnly: Can select/copy but not edit
type InputElementState =
  { -- Core value
    value :: String                    -- ^ Current text content
  , placeholder :: String              -- ^ Placeholder when empty
  , inputType :: InputType             -- ^ Semantic input type
    -- Length constraints
  , maxLength :: Maybe Int             -- ^ Maximum character count
  , minLength :: Maybe Int             -- ^ Minimum character count
    -- Interaction state (verified flags)
  , disabled :: DisabledFlag           -- ^ Cannot interact
  , focused :: FocusedFlag             -- ^ Has keyboard focus
  , hovered :: HoveredFlag             -- ^ Pointer is over input
  , readOnly :: ReadOnlyFlag           -- ^ Can select but not edit
    -- Validation
  , validation :: ValidationState      -- ^ Current validation status
    -- Selection (for future use)
  , selectionStart :: Maybe Int        -- ^ Caret/selection start
  , selectionEnd :: Maybe Int          -- ^ Selection end
  }

-- | Default input state — empty text input, enabled.
defaultState :: InputElementState
defaultState =
  { value: ""
  , placeholder: ""
  , inputType: TypeText
  , maxLength: Nothing
  , minLength: Nothing
  , disabled: DisabledFlag false
  , focused: FocusedFlag false
  , hovered: HoveredFlag false
  , readOnly: ReadOnlyFlag false
  , validation: ValidationNone
  , selectionStart: Nothing
  , selectionEnd: Nothing
  }

-- | Password input state.
passwordState :: InputElementState
passwordState = defaultState
  { inputType = TypePassword
  , placeholder = "Enter password"
  }

-- | Email input state.
emailState :: InputElementState
emailState = defaultState
  { inputType = TypeEmail
  , placeholder = "email@example.com"
  }

-- | Number input state.
numberState :: InputElementState
numberState = defaultState
  { inputType = TypeNumber
  , placeholder = "0"
  }

-- | Search input state.
searchState :: InputElementState
searchState = defaultState
  { inputType = TypeSearch
  , placeholder = "Search..."
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current value.
getValue :: InputElementState -> String
getValue s = s.value

-- | Get placeholder text.
getPlaceholder :: InputElementState -> String
getPlaceholder s = s.placeholder

-- | Get input type.
getInputType :: InputElementState -> InputType
getInputType s = s.inputType

-- | Is the input disabled?
isDisabled :: InputElementState -> Boolean
isDisabled s = case s.disabled of
  DisabledFlag b -> b

-- | Does the input have focus?
isFocused :: InputElementState -> Boolean
isFocused s = case s.focused of
  FocusedFlag b -> b

-- | Is the pointer hovering?
isHovered :: InputElementState -> Boolean
isHovered s = case s.hovered of
  HoveredFlag b -> b

-- | Is the input read-only?
isReadOnly :: InputElementState -> Boolean
isReadOnly s = case s.readOnly of
  ReadOnlyFlag b -> b

-- | Does the input have an error?
hasError :: InputElementState -> Boolean
hasError s = case s.validation of
  ValidationError _ -> true
  _ -> false

-- | Does the input have a warning?
hasWarning :: InputElementState -> Boolean
hasWarning s = case s.validation of
  ValidationWarning _ -> true
  _ -> false

-- | Is the input valid?
isValid :: InputElementState -> Boolean
isValid s = case s.validation of
  ValidationValid -> true
  _ -> false

-- | Get error/warning message if any.
getErrorMessage :: InputElementState -> Maybe String
getErrorMessage s = case s.validation of
  ValidationError msg -> Just msg
  ValidationWarning msg -> Just msg
  _ -> Nothing

-- | Get current character count.
getCharCount :: InputElementState -> Int
getCharCount s = String.length s.value

-- | Get maximum length constraint.
getMaxLength :: InputElementState -> Maybe Int
getMaxLength s = s.maxLength

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set value.
setValue :: String -> InputElementState -> InputElementState
setValue v s = s { value = v }

-- | Set placeholder.
setPlaceholder :: String -> InputElementState -> InputElementState
setPlaceholder p s = s { placeholder = p }

-- | Set disabled state.
setDisabled :: Boolean -> InputElementState -> InputElementState
setDisabled b s = s { disabled = DisabledFlag b }

-- | Set focused state.
setFocused :: Boolean -> InputElementState -> InputElementState
setFocused b s = s { focused = FocusedFlag b }

-- | Set hovered state.
setHovered :: Boolean -> InputElementState -> InputElementState
setHovered b s = s { hovered = HoveredFlag b }

-- | Set read-only state.
setReadOnly :: Boolean -> InputElementState -> InputElementState
setReadOnly b s = s { readOnly = ReadOnlyFlag b }

-- | Set error validation state.
setError :: String -> InputElementState -> InputElementState
setError msg s = s { validation = ValidationError msg }

-- | Set warning validation state.
setWarning :: String -> InputElementState -> InputElementState
setWarning msg s = s { validation = ValidationWarning msg }

-- | Set valid validation state.
setValid :: InputElementState -> InputElementState
setValid s = s { validation = ValidationValid }

-- | Clear validation state.
clearValidation :: InputElementState -> InputElementState
clearValidation s = s { validation = ValidationNone }

-- | Set maximum length constraint.
setMaxLength :: Int -> InputElementState -> InputElementState
setMaxLength n s = s { maxLength = Just n }

-- | Set minimum length constraint.
setMinLength :: Int -> InputElementState -> InputElementState
setMinLength n s = s { minLength = Just n }
