-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // badge
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Badge component with variants
-- |
-- | Small status badges inspired by shadcn/ui.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Badge as Badge
-- |
-- | -- Default badge
-- | Badge.badge [] [ HH.text "New" ]
-- |
-- | -- With variant
-- | Badge.badge [ Badge.variant Badge.Success ] [ HH.text "Active" ]
-- |
-- | -- Outline style
-- | Badge.badge [ Badge.variant Badge.Outline ] [ HH.text "Draft" ]
-- | ```
module Hydrogen.Component.Badge
  ( -- * Badge Component
    badge
    -- * Props
  , BadgeProps
  , BadgeProp
  , variant
  , className
    -- * Variants
  , BadgeVariant(..)
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Badge variants
data BadgeVariant
  = Default
  | Secondary
  | Destructive
  | Outline
  | Success
  | Warning

derive instance eqBadgeVariant :: Eq BadgeVariant

-- | Get variant classes
variantClasses :: BadgeVariant -> String
variantClasses = case _ of
  Default ->
    "border-transparent bg-primary text-primary-foreground hover:bg-primary/80"
  Secondary ->
    "border-transparent bg-secondary text-secondary-foreground hover:bg-secondary/80"
  Destructive ->
    "border-transparent bg-destructive text-destructive-foreground hover:bg-destructive/80"
  Outline ->
    "text-foreground"
  Success ->
    "border-transparent bg-green-500 text-white hover:bg-green-600"
  Warning ->
    "border-transparent bg-yellow-500 text-white hover:bg-yellow-600"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type BadgeProps = { variant :: BadgeVariant, className :: String }
type BadgeProp = BadgeProps -> BadgeProps

defaultProps :: BadgeProps
defaultProps = { variant: Default, className: "" }

-- | Set variant
variant :: BadgeVariant -> BadgeProp
variant v props = props { variant = v }

-- | Add custom class
className :: String -> BadgeProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base badge classes
baseClasses :: String
baseClasses =
  "inline-flex items-center rounded-full border px-2.5 py-0.5 text-xs font-semibold transition-colors focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2"

-- | Render a badge
badge :: forall w i. Array BadgeProp -> Array (HH.HTML w i) -> HH.HTML w i
badge propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ baseClasses, variantClasses props.variant, props.className ] ]
    children
