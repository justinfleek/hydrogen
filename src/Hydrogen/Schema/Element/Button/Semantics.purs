-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // element // button // semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ButtonSemantics — purpose, identity, and accessibility atoms.
-- |
-- | ## Atoms Included
-- |
-- | - ButtonPurpose (action, submit, toggle, media, etc.)
-- | - ButtonIdentity (UUID5 deterministic identity)
-- | - Toggle state (for toggle buttons)
-- | - Popup type (for menu/dialog triggers)
-- | - ARIA attributes

module Hydrogen.Schema.Element.Button.Semantics
  ( -- * Button Semantics Record
    ButtonSemantics
  , defaultSemantics
    -- * Purpose-Specific Semantics (12 types)
  , actionSemantics
  , ctaSemantics
  , submitSemantics
  , resetSemantics
  , navigationSemantics
  , mediaSemantics
  , toggleSemantics
  , menuSemantics
  , dialogSemantics
  , disclosureSemantics
  , dangerSemantics
  , iconSemantics
  , fabSemantics
  , emailSemantics
    -- * Accessors
  , semPurpose
  , semLabel
  , semToggleState
  , semDisabled
  , semPopupType
  , semAriaDescribedBy
  , semAriaControls
    -- * Modifiers
  , setDisabled
  , setLoading
  , setToggleState
  , setPopupType
  , setAriaDescribedBy
  , setAriaControls
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.ButtonSemantics
  ( ButtonPurpose
      ( ActionButton
      , FormSubmit
      , FormReset
      , NavigationButton
      , MediaControl
      , ToggleControl
      , MenuTrigger
      , DialogTrigger
      , DisclosureTrigger
      , DangerAction
      , IconAction
      , FloatingAction
      )
  , ToggleState(Pressed, Unpressed)
  , PopupType(MenuPopup, DialogPopup)
  ) as Sem

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // button semantics
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Semantics atoms for button purpose and accessibility.
-- |
-- | What the button DOES, not how it looks.
type ButtonSemantics =
  { -- Purpose
    purpose :: Sem.ButtonPurpose         -- ^ Semantic purpose
  , label :: String                      -- ^ Visible or ARIA label
    -- State
  , toggleState :: Maybe Sem.ToggleState -- ^ For toggle buttons
  , popupType :: Maybe Sem.PopupType     -- ^ For menu/dialog triggers
    -- Flags
  , disabled :: Boolean                  -- ^ Is button disabled?
  , loading :: Boolean                   -- ^ Is button in loading state?
    -- Accessibility
  , ariaDescribedBy :: Maybe String      -- ^ ID of describing element
  , ariaControls :: Maybe String         -- ^ ID of controlled element
  }

-- | Default semantics: action button with label.
defaultSemantics :: String -> ButtonSemantics
defaultSemantics lbl =
  { purpose: Sem.ActionButton
  , label: lbl
  , toggleState: Nothing
  , popupType: Nothing
  , disabled: false
  , loading: false
  , ariaDescribedBy: Nothing
  , ariaControls: Nothing
  }

-- | Action button semantics (general purpose).
actionSemantics :: String -> ButtonSemantics
actionSemantics = defaultSemantics

-- | Submit button semantics (form submission).
submitSemantics :: String -> ButtonSemantics
submitSemantics lbl = (defaultSemantics lbl) { purpose = Sem.FormSubmit }

-- | Toggle button semantics (on/off state).
toggleSemantics :: String -> Boolean -> ButtonSemantics
toggleSemantics lbl isOn = (defaultSemantics lbl)
  { purpose = Sem.ToggleControl
  , toggleState = Just (if isOn then Sem.Pressed else Sem.Unpressed)
  }

-- | CTA (Call-to-Action) button semantics.
-- |
-- | High-impact conversion button with strong visual weight.
-- | Used for primary marketing actions.
ctaSemantics :: String -> ButtonSemantics
ctaSemantics lbl = (defaultSemantics lbl)
  { purpose = Sem.ActionButton
  }

-- | Reset button semantics (form reset).
resetSemantics :: String -> ButtonSemantics
resetSemantics lbl = (defaultSemantics lbl)
  { purpose = Sem.FormReset
  }

-- | Navigation button semantics (route change).
-- |
-- | Link-like behavior, changes application route.
navigationSemantics :: String -> ButtonSemantics
navigationSemantics lbl = (defaultSemantics lbl)
  { purpose = Sem.NavigationButton
  }

-- | Media control button semantics (play/pause/etc).
-- |
-- | Icon-only media controls with ARIA label requirement.
mediaSemantics :: String -> ButtonSemantics
mediaSemantics lbl = (defaultSemantics lbl)
  { purpose = Sem.MediaControl
  }

-- | Menu trigger semantics (opens dropdown/menu).
-- |
-- | Has popup indicator, aria-haspopup="menu".
menuSemantics :: String -> ButtonSemantics
menuSemantics lbl = (defaultSemantics lbl)
  { purpose = Sem.MenuTrigger
  , popupType = Just Sem.MenuPopup
  }

-- | Dialog trigger semantics (opens modal/dialog).
-- |
-- | Has popup indicator, aria-haspopup="dialog".
dialogSemantics :: String -> ButtonSemantics
dialogSemantics lbl = (defaultSemantics lbl)
  { purpose = Sem.DialogTrigger
  , popupType = Just Sem.DialogPopup
  }

-- | Disclosure trigger semantics (expand/collapse).
-- |
-- | Accordion-style content toggle, uses aria-expanded.
disclosureSemantics :: String -> Boolean -> ButtonSemantics
disclosureSemantics lbl isExpanded = (defaultSemantics lbl)
  { purpose = Sem.DisclosureTrigger
  , toggleState = Just (if isExpanded then Sem.Pressed else Sem.Unpressed)
  }

-- | Danger action semantics (destructive).
-- |
-- | Requires confirmation pattern, styled with warning colors.
dangerSemantics :: String -> ButtonSemantics
dangerSemantics lbl = (defaultSemantics lbl)
  { purpose = Sem.DangerAction
  }

-- | Icon action semantics (icon-only button).
-- |
-- | MUST have aria-label for accessibility.
iconSemantics :: String -> ButtonSemantics
iconSemantics lbl = (defaultSemantics lbl)
  { purpose = Sem.IconAction
  }

-- | FAB (Floating Action Button) semantics.
-- |
-- | Prominent floating action, typically icon-only with aria-label.
fabSemantics :: String -> ButtonSemantics
fabSemantics lbl = (defaultSemantics lbl)
  { purpose = Sem.FloatingAction
  }

-- | Email/Contact button semantics.
-- |
-- | Communication trigger (mailto, contact form, etc).
emailSemantics :: String -> ButtonSemantics
emailSemantics lbl = (defaultSemantics lbl)
  { purpose = Sem.ActionButton  -- Uses ActionButton purpose with email context
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get purpose.
semPurpose :: ButtonSemantics -> Sem.ButtonPurpose
semPurpose s = s.purpose

-- | Get label.
semLabel :: ButtonSemantics -> String
semLabel s = s.label

-- | Get toggle state.
semToggleState :: ButtonSemantics -> Maybe Sem.ToggleState
semToggleState s = s.toggleState

-- | Get popup type.
semPopupType :: ButtonSemantics -> Maybe Sem.PopupType
semPopupType s = s.popupType

-- | Get disabled flag.
semDisabled :: ButtonSemantics -> Boolean
semDisabled s = s.disabled

-- | Get aria-describedby.
semAriaDescribedBy :: ButtonSemantics -> Maybe String
semAriaDescribedBy s = s.ariaDescribedBy

-- | Get aria-controls.
semAriaControls :: ButtonSemantics -> Maybe String
semAriaControls s = s.ariaControls

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // modifiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set disabled state.
setDisabled :: Boolean -> ButtonSemantics -> ButtonSemantics
setDisabled d s = s { disabled = d }

-- | Set loading state.
setLoading :: Boolean -> ButtonSemantics -> ButtonSemantics
setLoading l s = s { loading = l }

-- | Set toggle state.
setToggleState :: Sem.ToggleState -> ButtonSemantics -> ButtonSemantics
setToggleState t s = s { toggleState = Just t }

-- | Set popup type.
setPopupType :: Sem.PopupType -> ButtonSemantics -> ButtonSemantics
setPopupType p s = s { popupType = Just p }

-- | Set aria-describedby.
setAriaDescribedBy :: String -> ButtonSemantics -> ButtonSemantics
setAriaDescribedBy id s = s { ariaDescribedBy = Just id }

-- | Set aria-controls.
setAriaControls :: String -> ButtonSemantics -> ButtonSemantics
setAriaControls id s = s { ariaControls = Just id }
