-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // ui // cta-button // utilities
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CTAButton Utilities — Helper functions
-- |
-- | This module provides utility functions for working with CTA buttons:
-- | - String conversion functions (show helpers)
-- | - Parsing functions (string to variant)
-- | - Validation functions
-- | - Identity/UUID generation
-- | - ARIA helper functions

module Hydrogen.UI.CTAButton.Utilities
  ( showVariant
  , showSize
  , showAnimation
  , variantFromString
  , isInteractive
  , validateConfig
  , buttonUUID
  , toggleStateLabel
  , popupTypeAria
  ) where

import Prelude
  ( class Show
  , show
  , (>>>)
  , not
  , (&&)
  )

import Data.Maybe (Maybe(Nothing), fromMaybe, isJust)
import Data.String (toUpper)
import Data.Unit (Unit, unit)

import Hydrogen.UI.CTAButton.Types
  ( CTAVariant(Primary, Secondary, Tertiary, Destructive, Success, Warning, Info, Outline, Ghost, Link)
  , CTASize
  , CTAAnimation
  )

import Hydrogen.UI.CTAButton.Config (CTAConfig)

import Hydrogen.Schema.Reactive.ButtonSemantics
  ( ButtonPurpose
  , ToggleState(Pressed, Unpressed, Mixed)
  , PopupType(MenuPopup, ListboxPopup, TreePopup, GridPopup, DialogPopup)
  , buttonIdentity
  , buttonIdString
  ) as ButtonSemantics

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // string conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show variant as string
-- |
-- | Uses the Show instance to convert CTAVariant to String.
showVariant :: CTAVariant -> String
showVariant v = show v

-- | Show size as string
-- |
-- | Uses the Show instance to convert CTASize to String.
showSize :: CTASize -> String
showSize s = show s

-- | Show animation as string
-- |
-- | Uses the Show instance to convert CTAAnimation to String.
showAnimation :: CTAAnimation -> String
showAnimation a = show a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // parsing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse variant from string
-- |
-- | Accepts case-insensitive input and returns the matching CTAVariant.
-- | Returns Primary for unrecognized inputs.
variantFromString :: String -> CTAVariant
variantFromString = toUpper >>> parseVariant
  where
    parseVariant :: String -> CTAVariant
    parseVariant "PRIMARY" = Primary
    parseVariant "SECONDARY" = Secondary
    parseVariant "TERTIARY" = Tertiary
    parseVariant "DESTRUCTIVE" = Destructive
    parseVariant "SUCCESS" = Success
    parseVariant "WARNING" = Warning
    parseVariant "INFO" = Info
    parseVariant "OUTLINE" = Outline
    parseVariant "GHOST" = Ghost
    parseVariant "LINK" = Link
    parseVariant _ = Primary

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if config represents an interactive button
-- |
-- | A button is interactive when:
-- | - Not disabled
-- | - Not in loading state
-- | - Has a click handler attached
isInteractive :: forall msg. CTAConfig msg -> Boolean
isInteractive cfg = 
  not cfg.disabled && not cfg.loading && isJust cfg.onClick

-- | Validate button configuration
-- |
-- | Currently validates all configs as valid by type construction.
-- | The type system enforces valid configurations at compile time.
-- | Returns Unit to indicate successful validation.
validateConfig :: forall msg. CTAConfig msg -> Unit
validateConfig _cfg = unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate deterministic UUID5 for button identity
-- |
-- | Creates a reproducible identifier based on:
-- | - Button purpose (semantic role)
-- | - Aria label (or default "cta-button")
-- |
-- | This UUID is stable across renders given the same configuration,
-- | enabling deterministic diffing and caching.
buttonUUID :: forall msg. CTAConfig msg -> String
buttonUUID cfg = 
  let 
    label = fromMaybe "cta-button" cfg.ariaLabel
    identity = ButtonSemantics.buttonIdentity cfg.purpose label Nothing Nothing
  in 
    ButtonSemantics.buttonIdString identity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // aria helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get human-readable label for toggle state
-- |
-- | Maps ToggleState to user-friendly description:
-- | - Pressed -> "Enabled"
-- | - Unpressed -> "Disabled"
-- | - Mixed -> "Partially enabled"
toggleStateLabel :: ButtonSemantics.ToggleState -> String
toggleStateLabel ButtonSemantics.Pressed = "Enabled"
toggleStateLabel ButtonSemantics.Unpressed = "Disabled"
toggleStateLabel ButtonSemantics.Mixed = "Partially enabled"

-- | Get ARIA attribute value for popup type
-- |
-- | Maps PopupType to the corresponding aria-haspopup value:
-- | - MenuPopup -> "menu"
-- | - ListboxPopup -> "listbox"
-- | - TreePopup -> "tree"
-- | - GridPopup -> "grid"
-- | - DialogPopup -> "dialog"
popupTypeAria :: ButtonSemantics.PopupType -> String
popupTypeAria ButtonSemantics.MenuPopup = "menu"
popupTypeAria ButtonSemantics.ListboxPopup = "listbox"
popupTypeAria ButtonSemantics.TreePopup = "tree"
popupTypeAria ButtonSemantics.GridPopup = "grid"
popupTypeAria ButtonSemantics.DialogPopup = "dialog"
