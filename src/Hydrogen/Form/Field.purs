-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // field
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Form field components
-- |
-- | Pre-composed form fields with labels, hints, and error display.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Form.Field as Field
-- |
-- | Field.field
-- |   { label: "Email"
-- |   , hint: Just "We'll never share your email"
-- |   , error: if state.emailError then Just "Invalid email" else Nothing
-- |   , required: true
-- |   }
-- |   [ Input.input [ Input.type_ Input.Email, Input.value state.email ] ]
-- | ```
module Hydrogen.Form.Field
  ( -- * Field Component
    field
  , FieldConfig
    -- * Field Parts
  , fieldLabel
  , fieldHint
  , fieldError
  , fieldRequired
    -- * Form Group
  , formGroup
  , formRow
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // field component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Field configuration
type FieldConfig =
  { label :: String
  , hint :: Maybe String
  , error :: Maybe String
  , required :: Boolean
  , id :: Maybe String
  }

-- | Complete form field with label, input, hint, and error
field :: forall w i. FieldConfig -> Array (HH.HTML w i) -> HH.HTML w i
field config children =
  HH.div
    [ cls [ "space-y-2" ] ]
    ( [ fieldLabel config ]
      <> children
      <> case config.hint of
          Just h | config.error == Nothing -> [ fieldHint h ]
          _ -> []
      <> case config.error of
          Just e -> [ fieldError e ]
          Nothing -> []
    )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // field parts
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Field label
fieldLabel :: forall w i. FieldConfig -> HH.HTML w i
fieldLabel config =
  HH.label
    ( [ cls [ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]
      ] <> case config.id of
        Just i -> [ HP.for i ]
        Nothing -> []
    )
    [ HH.text config.label
    , if config.required then fieldRequired else HH.text ""
    ]

-- | Required indicator
fieldRequired :: forall w i. HH.HTML w i
fieldRequired =
  HH.span
    [ cls [ "text-destructive ml-1" ] ]
    [ HH.text "*" ]

-- | Field hint text
fieldHint :: forall w i. String -> HH.HTML w i
fieldHint hint =
  HH.p
    [ cls [ "text-sm text-muted-foreground" ] ]
    [ HH.text hint ]

-- | Field error message
fieldError :: forall w i. String -> HH.HTML w i
fieldError err =
  HH.p
    [ cls [ "text-sm text-destructive" ] ]
    [ HH.text err ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // form layout
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Vertical form group with spacing
formGroup :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
formGroup children =
  HH.div
    [ cls [ "space-y-4" ] ]
    children

-- | Horizontal form row
formRow :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
formRow children =
  HH.div
    [ cls [ "flex flex-col sm:flex-row gap-4" ] ]
    children
