-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // focus
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Focus management utilities
-- |
-- | Type-safe focus management for accessibility.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.A11y.Focus as Focus
-- |
-- | -- Focus ring styles
-- | Focus.focusRing          -- "focus:outline-none focus:ring-2..."
-- | Focus.focusRingInset     -- With inset ring
-- |
-- | -- Focus trap container
-- | Focus.focusTrap []
-- |   [ dialogContent ]
-- |
-- | -- Skip link
-- | Focus.skipLink "Skip to content" "#main"
-- | ```
module Hydrogen.A11y.Focus
  ( -- * Focus Ring Styles
    focusRing
  , focusRingInset
  , focusVisible
  , focusWithin
    -- * Focus Utilities
  , focusTrap
  , skipLink
  , focusableProps
    -- * Tab Index
  , TabIndex(..)
  , tabIndex
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // focus ring styles
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Standard focus ring classes
-- |
-- | Includes ring color, offset, and outline removal
focusRing :: String
focusRing = "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2 focus:ring-offset-background"

-- | Inset focus ring (inside element)
focusRingInset :: String
focusRingInset = "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-inset"

-- | Focus visible only (keyboard focus)
focusVisible :: String
focusVisible = "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2"

-- | Focus within (child has focus)
focusWithin :: String
focusWithin = "focus-within:outline-none focus-within:ring-2 focus-within:ring-ring focus-within:ring-offset-2"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // focus utilities
-- ═══════════════════════════════════════════════════════════════════════════════

type FocusTrapProps = { className :: String }
type FocusTrapProp = FocusTrapProps -> FocusTrapProps

defaultFocusTrapProps :: FocusTrapProps
defaultFocusTrapProps = { className: "" }

-- | Focus trap container
-- |
-- | Note: Actual focus trapping requires JavaScript.
-- | This provides the semantic container with proper ARIA attributes.
focusTrap :: forall w i. Array FocusTrapProp -> Array (HH.HTML w i) -> HH.HTML w i
focusTrap propMods children =
  let props = foldl (\p f -> f p) defaultFocusTrapProps propMods
  in HH.div
    [ cls [ props.className ]
    , HP.attr (HH.AttrName "data-focus-trap") "true"
    ]
    children

-- | Skip link for keyboard navigation
-- |
-- | Allows keyboard users to skip navigation and jump to main content.
skipLink :: forall w i. String -> String -> HH.HTML w i
skipLink label href =
  HH.a
    [ cls [ "sr-only focus:not-sr-only focus:absolute focus:z-50 focus:top-4 focus:left-4 focus:px-4 focus:py-2 focus:bg-background focus:text-foreground focus:rounded-md", focusRing ]
    , HP.href href
    ]
    [ HH.text label ]

-- | Props to make an element focusable
-- |
-- | Returns an array of properties that can be spread onto elements
-- | to make them keyboard-focusable.
focusableProps :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
focusableProps children =
  HH.div
    [ HP.tabIndex 0
    , HP.attr (HH.AttrName "role") "button"
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // tab index
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tab index values
data TabIndex
  = TabIndexAuto      -- Natural tab order (no attribute)
  | TabIndexFocusable -- 0 - In tab order
  | TabIndexNot       -- -1 - Focusable but not in tab order
  | TabIndexCustom Int -- Custom value

derive instance eqTabIndex :: Eq TabIndex

-- | Convert to Halogen property
tabIndex :: forall r i. TabIndex -> HH.IProp (tabIndex :: Int | r) i
tabIndex = case _ of
  TabIndexAuto -> HP.tabIndex 0
  TabIndexFocusable -> HP.tabIndex 0
  TabIndexNot -> HP.tabIndex (-1)
  TabIndexCustom n -> HP.tabIndex n
