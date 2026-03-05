-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // element // input // semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | InputSemantics — Purpose, identity, and accessibility atoms.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - UUID5 (Attestation.UUID5) — Deterministic identity
-- |
-- | ## Input Semantics Model
-- |
-- | An input control has:
-- | - Purpose: What it captures (email, password, search, etc.)
-- | - ARIA role: "textbox" for single-line, "searchbox" for search
-- | - Label: Accessible name for screen readers
-- | - Error messages: For validation feedback
-- |
-- | ## Accessibility (WCAG 2.1)
-- |
-- | - role="textbox" or role="searchbox"
-- | - aria-label/aria-labelledby for accessible name
-- | - aria-describedby for help text or errors
-- | - aria-invalid for validation state
-- | - aria-required for required fields
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Attestation.UUID5 (UUID5)

module Hydrogen.Schema.Element.Input.Semantics
  ( -- * Input Purpose
    InputPurpose
      ( PurposeGeneric
      , PurposeEmail
      , PurposePassword
      , PurposeSearch
      , PurposeUrl
      , PurposePhone
      , PurposeName
      , PurposeUsername
      , PurposeAddress
      , PurposeCity
      , PurposePostalCode
      , PurposeCreditCard
      , PurposeCustom
      )
  , purposeToString
  , purposeToAutocomplete
  
  -- * Input Semantics Record
  , InputSemantics
  , defaultSemantics
  , emailSemantics
  , passwordSemantics
  , searchSemantics
  , urlSemantics
  , phoneSemantics
  
  -- * Semantics Accessors
  , getPurpose
  , getLabel
  , getHelpText
  , getErrorId
  , getAriaRole
  , isRequired
  , isDisabled
  
  -- * Semantics Modifiers
  , setPurpose
  , setLabel
  , setHelpText
  , setRequired
  , setDisabled
  , setAriaDescribedBy
  
  -- * UUID5 Identity
  , inputId
  , inputIdString
  
  -- * Re-exports
  , module Hydrogen.Schema.Attestation.UUID5
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

import Prim (Boolean, String)

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Attestation.UUID5
  ( UUID5
  , uuid5
  , toString
  , nsInput
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // input purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input purpose — what kind of data does this input capture?
-- |
-- | Purpose determines:
-- | - Autocomplete hints
-- | - Keyboard type on mobile
-- | - Default validation rules
data InputPurpose
  = PurposeGeneric         -- ^ Generic text
  | PurposeEmail           -- ^ Email address
  | PurposePassword        -- ^ Password (new or current)
  | PurposeSearch          -- ^ Search query
  | PurposeUrl             -- ^ URL/website
  | PurposePhone           -- ^ Phone number
  | PurposeName            -- ^ Full name
  | PurposeUsername        -- ^ Username/handle
  | PurposeAddress         -- ^ Street address
  | PurposeCity            -- ^ City name
  | PurposePostalCode      -- ^ Postal/ZIP code
  | PurposeCreditCard      -- ^ Credit card number
  | PurposeCustom String   -- ^ Custom purpose

derive instance eqInputPurpose :: Eq InputPurpose
derive instance ordInputPurpose :: Ord InputPurpose

instance showInputPurpose :: Show InputPurpose where
  show PurposeGeneric = "generic"
  show PurposeEmail = "email"
  show PurposePassword = "password"
  show PurposeSearch = "search"
  show PurposeUrl = "url"
  show PurposePhone = "phone"
  show PurposeName = "name"
  show PurposeUsername = "username"
  show PurposeAddress = "address"
  show PurposeCity = "city"
  show PurposePostalCode = "postal-code"
  show PurposeCreditCard = "credit-card"
  show (PurposeCustom s) = "custom:" <> s

-- | Convert purpose to string for data attributes.
purposeToString :: InputPurpose -> String
purposeToString = show

-- | Get autocomplete attribute value for purpose.
purposeToAutocomplete :: InputPurpose -> Maybe String
purposeToAutocomplete = case _ of
  PurposeGeneric -> Nothing
  PurposeEmail -> Just "email"
  PurposePassword -> Just "current-password"
  PurposeSearch -> Nothing
  PurposeUrl -> Just "url"
  PurposePhone -> Just "tel"
  PurposeName -> Just "name"
  PurposeUsername -> Just "username"
  PurposeAddress -> Just "street-address"
  PurposeCity -> Just "address-level2"
  PurposePostalCode -> Just "postal-code"
  PurposeCreditCard -> Just "cc-number"
  PurposeCustom _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // input semantics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete input semantics — purpose, identity, and accessibility.
-- |
-- | ## ARIA Attributes
-- |
-- | - role="textbox" (default) or role="searchbox"
-- | - aria-label (or aria-labelledby)
-- | - aria-describedby (for help text or errors)
-- | - aria-invalid (for validation state)
-- | - aria-required (for required fields)
-- |
-- | ## UUID5 Identity
-- |
-- | Input identity is derived from:
-- | - uniqueKey
-- | - purpose
-- | - label
-- |
-- | Same inputs = same UUID5. Always. Everywhere.
type InputSemantics =
  { -- Purpose and identity
    purpose :: InputPurpose            -- ^ What kind of input
  , uniqueKey :: String                -- ^ Unique identifier for UUID5
    -- Labels
  , label :: String                    -- ^ Visible or ARIA label
  , labelledBy :: Maybe String         -- ^ ID of labelling element
  , helpText :: Maybe String           -- ^ Help text description
  , describedBy :: Maybe String        -- ^ ID of describing element
    -- Validation
  , required :: Boolean                -- ^ Is input required
  , disabled :: Boolean                -- ^ Is input disabled
    -- ARIA
  , ariaRole :: String                 -- ^ ARIA role (textbox, searchbox)
  , ariaLive :: Maybe String           -- ^ ARIA live region type
  }

-- | Default input semantics.
defaultSemantics :: String -> InputSemantics
defaultSemantics key =
  { purpose: PurposeGeneric
  , uniqueKey: key
  , label: "Input"
  , labelledBy: Nothing
  , helpText: Nothing
  , describedBy: Nothing
  , required: false
  , disabled: false
  , ariaRole: "textbox"
  , ariaLive: Nothing
  }

-- | Email input semantics.
emailSemantics :: String -> InputSemantics
emailSemantics key =
  { purpose: PurposeEmail
  , uniqueKey: key
  , label: "Email"
  , labelledBy: Nothing
  , helpText: Just "Enter your email address"
  , describedBy: Nothing
  , required: false
  , disabled: false
  , ariaRole: "textbox"
  , ariaLive: Nothing
  }

-- | Password input semantics.
passwordSemantics :: String -> InputSemantics
passwordSemantics key =
  { purpose: PurposePassword
  , uniqueKey: key
  , label: "Password"
  , labelledBy: Nothing
  , helpText: Nothing
  , describedBy: Nothing
  , required: false
  , disabled: false
  , ariaRole: "textbox"
  , ariaLive: Nothing
  }

-- | Search input semantics.
searchSemantics :: String -> InputSemantics
searchSemantics key =
  { purpose: PurposeSearch
  , uniqueKey: key
  , label: "Search"
  , labelledBy: Nothing
  , helpText: Nothing
  , describedBy: Nothing
  , required: false
  , disabled: false
  , ariaRole: "searchbox"
  , ariaLive: Just "polite"  -- Announce search results
  }

-- | URL input semantics.
urlSemantics :: String -> InputSemantics
urlSemantics key =
  { purpose: PurposeUrl
  , uniqueKey: key
  , label: "URL"
  , labelledBy: Nothing
  , helpText: Just "Enter a valid URL"
  , describedBy: Nothing
  , required: false
  , disabled: false
  , ariaRole: "textbox"
  , ariaLive: Nothing
  }

-- | Phone input semantics.
phoneSemantics :: String -> InputSemantics
phoneSemantics key =
  { purpose: PurposePhone
  , uniqueKey: key
  , label: "Phone"
  , labelledBy: Nothing
  , helpText: Just "Enter your phone number"
  , describedBy: Nothing
  , required: false
  , disabled: false
  , ariaRole: "textbox"
  , ariaLive: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get purpose.
getPurpose :: InputSemantics -> InputPurpose
getPurpose s = s.purpose

-- | Get label.
getLabel :: InputSemantics -> String
getLabel s = s.label

-- | Get help text.
getHelpText :: InputSemantics -> Maybe String
getHelpText s = s.helpText

-- | Get error element ID for aria-describedby.
getErrorId :: InputSemantics -> String
getErrorId s = s.uniqueKey <> "-error"

-- | Get ARIA role.
getAriaRole :: InputSemantics -> String
getAriaRole s = s.ariaRole

-- | Is input required?
isRequired :: InputSemantics -> Boolean
isRequired s = s.required

-- | Is input disabled?
isDisabled :: InputSemantics -> Boolean
isDisabled s = s.disabled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set purpose.
setPurpose :: InputPurpose -> InputSemantics -> InputSemantics
setPurpose p s = s { purpose = p }

-- | Set label.
setLabel :: String -> InputSemantics -> InputSemantics
setLabel l s = s { label = l }

-- | Set help text.
setHelpText :: String -> InputSemantics -> InputSemantics
setHelpText h s = s { helpText = Just h }

-- | Set required.
setRequired :: Boolean -> InputSemantics -> InputSemantics
setRequired r s = s { required = r }

-- | Set disabled.
setDisabled :: Boolean -> InputSemantics -> InputSemantics
setDisabled d s = s { disabled = d }

-- | Set aria-describedby ID.
setAriaDescribedBy :: String -> InputSemantics -> InputSemantics
setAriaDescribedBy id s = s { describedBy = Just id }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // uuid5 identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate deterministic UUID5 for an input.
-- |
-- | Identity is derived from:
-- | - uniqueKey
-- | - purpose
-- | - label
-- |
-- | Same inputs = same UUID5. Always. Everywhere.
inputId :: InputSemantics -> UUID5
inputId sem =
  let
    canonical = sem.uniqueKey <> "|" <> show sem.purpose <> "|" <> sem.label
  in
    uuid5 nsInput canonical

-- | Get input UUID5 as string (36 chars with dashes).
inputIdString :: InputSemantics -> String
inputIdString sem = toString (inputId sem)
