-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // alert
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Alert component with variants
-- |
-- | Alert messages for important information.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Alert as Alert
-- | import Hydrogen.Icon.Lucide as Icon
-- |
-- | -- Default alert
-- | Alert.alert []
-- |   [ Alert.alertTitle [] [ HH.text "Heads up!" ]
-- |   , Alert.alertDescription [] [ HH.text "You can add components here." ]
-- |   ]
-- |
-- | -- Destructive alert
-- | Alert.alert [ Alert.variant Alert.Destructive ]
-- |   [ Icon.alertCircle []
-- |   , Alert.alertTitle [] [ HH.text "Error" ]
-- |   , Alert.alertDescription [] [ HH.text "Something went wrong." ]
-- |   ]
-- | ```
module Hydrogen.Component.Alert
  ( -- * Alert Components
    alert
  , alertTitle
  , alertDescription
    -- * Props
  , AlertProps
  , AlertProp
  , variant
  , className
    -- * Variants
  , AlertVariant(..)
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Alert variants
data AlertVariant
  = Default
  | Destructive
  | Success
  | Warning

derive instance eqAlertVariant :: Eq AlertVariant

-- | Get variant classes
variantClasses :: AlertVariant -> String
variantClasses = case _ of
  Default ->
    "bg-background text-foreground"
  Destructive ->
    "border-destructive/50 text-destructive dark:border-destructive [&>svg]:text-destructive"
  Success ->
    "border-green-500/50 text-green-700 dark:text-green-400 [&>svg]:text-green-500"
  Warning ->
    "border-yellow-500/50 text-yellow-700 dark:text-yellow-400 [&>svg]:text-yellow-500"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type AlertProps = { variant :: AlertVariant, className :: String }
type AlertProp = AlertProps -> AlertProps

defaultProps :: AlertProps
defaultProps = { variant: Default, className: "" }

-- | Set variant
variant :: AlertVariant -> AlertProp
variant v props = props { variant = v }

-- | Add custom class
className :: String -> AlertProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base alert classes
baseClasses :: String
baseClasses =
  "relative w-full rounded-lg border p-4 [&>svg~*]:pl-7 [&>svg+div]:translate-y-[-3px] [&>svg]:absolute [&>svg]:left-4 [&>svg]:top-4 [&>svg]:text-foreground"

-- | Render an alert
alert :: forall w i. Array AlertProp -> Array (HH.HTML w i) -> HH.HTML w i
alert propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ baseClasses, variantClasses props.variant, props.className ]
    , ARIA.role "alert"
    ]
    children

-- | Alert title
alertTitle :: forall w i. Array AlertProp -> Array (HH.HTML w i) -> HH.HTML w i
alertTitle propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.h5
    [ cls [ "mb-1 font-medium leading-none tracking-tight", props.className ] ]
    children

-- | Alert description
alertDescription :: forall w i. Array AlertProp -> Array (HH.HTML w i) -> HH.HTML w i
alertDescription propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "text-sm [&_p]:leading-relaxed", props.className ] ]
    children
