-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // element // toggle // semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ToggleSemantics — Purpose, identity, and accessibility atoms.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - ToggleState (Reactive.ButtonSemantics) — ARIA pressed state
-- | - UUID5 (Attestation.UUID5) — Deterministic identity
-- |
-- | ## Toggle Semantics Model
-- |
-- | A toggle control has:
-- | - Purpose: What it controls (setting, feature, mode, etc.)
-- | - ARIA role: Always "switch" for binary toggles
-- | - Label: Accessible name for screen readers
-- | - Description: Optional extended description
-- |
-- | ## Accessibility (WCAG 2.1)
-- |
-- | - role="switch" indicates binary on/off control
-- | - aria-checked indicates current state
-- | - aria-label/aria-labelledby provides accessible name
-- | - aria-describedby links to description
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Reactive.ButtonSemantics (ToggleState)
-- | - Hydrogen.Schema.Attestation.UUID5 (UUID5, nsToggle)

module Hydrogen.Schema.Element.Toggle.Semantics
  ( -- * Toggle Purpose
    TogglePurpose
      ( PurposeSetting
      , PurposeFeature
      , PurposeMode
      , PurposeFilter
      , PurposeVisibility
      , PurposeNotification
      , PurposePrivacy
      , PurposeSync
      , PurposeCustom
      )
  , purposeToString
  , purposeDefaultLabel
  
  -- * Toggle Semantics Record
  , ToggleSemantics
  , defaultSemantics
  , settingSemantics
  , featureSemantics
  , visibilitySemantics
  , notificationSemantics
  
  -- * Semantics Accessors
  , getPurpose
  , getLabel
  , getDescription
  , getAriaRole
  , isDisabled
  
  -- * Semantics Modifiers
  , setPurpose
  , setLabel
  , setDescription
  , setDisabled
  , setAriaDescribedBy
  , setAriaControls
  
  -- * UUID5 Identity
  , toggleId
  , toggleIdString
  
  -- * Re-exports
  , module Hydrogen.Schema.Reactive.ButtonSemantics
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

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.ButtonSemantics
  ( ToggleState(Pressed, Unpressed, Mixed)
  , toggleStateToAria
  , isPressed
  )

import Hydrogen.Schema.Attestation.UUID5
  ( UUID5
  , uuid5
  , toString
  , nsToggle
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // toggle purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toggle purpose — what kind of control is this toggle?
-- |
-- | Purpose determines:
-- | - Default labeling
-- | - Expected interaction patterns
-- | - Integration with settings systems
data TogglePurpose
  = PurposeSetting      -- ^ App/system setting (e.g., "Dark mode")
  | PurposeFeature      -- ^ Feature flag (e.g., "Enable beta features")
  | PurposeMode         -- ^ Mode switch (e.g., "Edit mode")
  | PurposeFilter       -- ^ Filter toggle (e.g., "Show archived")
  | PurposeVisibility   -- ^ Show/hide toggle (e.g., "Show password")
  | PurposeNotification -- ^ Notification toggle (e.g., "Email alerts")
  | PurposePrivacy      -- ^ Privacy setting (e.g., "Share analytics")
  | PurposeSync         -- ^ Sync toggle (e.g., "Auto-sync")
  | PurposeCustom String -- ^ Custom purpose with description

derive instance eqTogglePurpose :: Eq TogglePurpose
derive instance ordTogglePurpose :: Ord TogglePurpose

instance showTogglePurpose :: Show TogglePurpose where
  show PurposeSetting = "setting"
  show PurposeFeature = "feature"
  show PurposeMode = "mode"
  show PurposeFilter = "filter"
  show PurposeVisibility = "visibility"
  show PurposeNotification = "notification"
  show PurposePrivacy = "privacy"
  show PurposeSync = "sync"
  show (PurposeCustom s) = "custom:" <> s

-- | Convert purpose to string for data attributes.
purposeToString :: TogglePurpose -> String
purposeToString = show

-- | Get default label for a purpose.
-- |
-- | These are fallback labels — specific toggles should override.
purposeDefaultLabel :: TogglePurpose -> String
purposeDefaultLabel = case _ of
  PurposeSetting -> "Toggle setting"
  PurposeFeature -> "Toggle feature"
  PurposeMode -> "Toggle mode"
  PurposeFilter -> "Toggle filter"
  PurposeVisibility -> "Toggle visibility"
  PurposeNotification -> "Toggle notifications"
  PurposePrivacy -> "Toggle privacy setting"
  PurposeSync -> "Toggle sync"
  PurposeCustom s -> "Toggle " <> s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // toggle semantics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete toggle semantics — purpose, identity, and accessibility.
-- |
-- | ## ARIA Attributes
-- |
-- | - role="switch" (always, for binary toggles)
-- | - aria-checked (maps to ToggleState)
-- | - aria-label (or aria-labelledby)
-- | - aria-describedby (optional, for extended description)
-- |
-- | ## UUID5 Identity
-- |
-- | Toggle identity is derived from:
-- | - Purpose
-- | - Label
-- | - Optional unique key
-- |
-- | Same configuration = same UUID = deterministic identity.
type ToggleSemantics =
  { -- Purpose and identity
    purpose :: TogglePurpose          -- ^ What kind of toggle
  , uniqueKey :: String               -- ^ Unique identifier for UUID5
    -- Labels
  , label :: String                   -- ^ Visible or ARIA label
  , labelledBy :: Maybe String        -- ^ ID of labelling element
  , description :: Maybe String       -- ^ Extended description
  , describedBy :: Maybe String       -- ^ ID of describing element
    -- State
  , disabled :: Boolean               -- ^ Is toggle disabled
    -- Relationships
  , ariaControls :: Maybe String      -- ^ ID of controlled element
  }

-- | Default toggle semantics.
-- |
-- | Setting purpose, "Toggle" label, not disabled.
defaultSemantics :: String -> ToggleSemantics
defaultSemantics key =
  { purpose: PurposeSetting
  , uniqueKey: key
  , label: "Toggle"
  , labelledBy: Nothing
  , description: Nothing
  , describedBy: Nothing
  , disabled: false
  , ariaControls: Nothing
  }

-- | Setting toggle semantics.
settingSemantics :: String -> String -> ToggleSemantics
settingSemantics key label =
  { purpose: PurposeSetting
  , uniqueKey: key
  , label: label
  , labelledBy: Nothing
  , description: Nothing
  , describedBy: Nothing
  , disabled: false
  , ariaControls: Nothing
  }

-- | Feature flag toggle semantics.
featureSemantics :: String -> String -> String -> ToggleSemantics
featureSemantics key label description =
  { purpose: PurposeFeature
  , uniqueKey: key
  , label: label
  , labelledBy: Nothing
  , description: Just description
  , describedBy: Nothing
  , disabled: false
  , ariaControls: Nothing
  }

-- | Visibility toggle semantics (show/hide).
visibilitySemantics :: String -> String -> String -> ToggleSemantics
visibilitySemantics key label controlsId =
  { purpose: PurposeVisibility
  , uniqueKey: key
  , label: label
  , labelledBy: Nothing
  , description: Nothing
  , describedBy: Nothing
  , disabled: false
  , ariaControls: Just controlsId
  }

-- | Notification toggle semantics.
notificationSemantics :: String -> String -> ToggleSemantics
notificationSemantics key label =
  { purpose: PurposeNotification
  , uniqueKey: key
  , label: label
  , labelledBy: Nothing
  , description: Nothing
  , describedBy: Nothing
  , disabled: false
  , ariaControls: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get purpose.
getPurpose :: ToggleSemantics -> TogglePurpose
getPurpose s = s.purpose

-- | Get label.
getLabel :: ToggleSemantics -> String
getLabel s = s.label

-- | Get description.
getDescription :: ToggleSemantics -> Maybe String
getDescription s = s.description

-- | Get ARIA role (always "switch" for toggles).
getAriaRole :: ToggleSemantics -> String
getAriaRole _ = "switch"

-- | Is toggle disabled?
isDisabled :: ToggleSemantics -> Boolean
isDisabled s = s.disabled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set purpose.
setPurpose :: TogglePurpose -> ToggleSemantics -> ToggleSemantics
setPurpose p s = s { purpose = p }

-- | Set label.
setLabel :: String -> ToggleSemantics -> ToggleSemantics
setLabel l s = s { label = l }

-- | Set description.
setDescription :: String -> ToggleSemantics -> ToggleSemantics
setDescription d s = s { description = Just d }

-- | Set disabled state.
setDisabled :: Boolean -> ToggleSemantics -> ToggleSemantics
setDisabled d s = s { disabled = d }

-- | Set aria-describedby ID.
setAriaDescribedBy :: String -> ToggleSemantics -> ToggleSemantics
setAriaDescribedBy id s = s { describedBy = Just id }

-- | Set aria-controls ID.
setAriaControls :: String -> ToggleSemantics -> ToggleSemantics
setAriaControls id s = s { ariaControls = Just id }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // uuid5 identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate deterministic UUID5 for a toggle.
-- |
-- | Identity is derived from:
-- | - uniqueKey
-- | - purpose
-- | - label
-- |
-- | Same inputs = same UUID5. Always. Everywhere.
toggleId :: ToggleSemantics -> UUID5
toggleId sem =
  let
    canonical = sem.uniqueKey <> "|" <> show sem.purpose <> "|" <> sem.label
  in
    uuid5 nsToggle canonical

-- | Get toggle UUID5 as string (36 chars with dashes).
toggleIdString :: ToggleSemantics -> String
toggleIdString sem = toString (toggleId sem)
