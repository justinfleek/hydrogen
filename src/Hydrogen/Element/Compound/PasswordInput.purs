-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // password-input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PasswordInput — Schema-native password input with visibility toggle and
-- | strength indicator.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars.
-- | When an atom is `Nothing`, no style is emitted — the element inherits
-- | from its parent or browser defaults.
-- |
-- | **No hardcoded CSS values.** The BrandSchema provides all visual atoms.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background-color        |
-- | | textColor             | Color      | Color.RGB                 | color                   |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | placeholderColor      | Color      | Color.RGB                 | ::placeholder color     |
-- | | focusBorderColor      | Color      | Color.RGB                 | :focus border-color     |
-- | | focusRingColor        | Color      | Color.RGB                 | :focus outline          |
-- | | toggleButtonColor     | Color      | Color.RGB                 | toggle icon color       |
-- | | strengthVeryWeakColor | Color      | Color.RGB                 | very weak bar color     |
-- | | strengthWeakColor     | Color      | Color.RGB                 | weak bar color          |
-- | | strengthFairColor     | Color      | Color.RGB                 | fair bar color          |
-- | | strengthStrongColor   | Color      | Color.RGB                 | strong bar color        |
-- | | strengthVeryStrongColor | Color    | Color.RGB                 | very strong bar color   |
-- | | strengthLabelColor    | Color      | Color.RGB                 | strength label color    |
-- | | strengthBarBgColor    | Color      | Color.RGB                 | strength bar background |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | height                | Dimension  | Device.Pixel              | height                  |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | iconSize              | Dimension  | Device.Pixel              | icon width/height       |
-- | | fontSize              | Typography | FontSize.FontSize         | font-size               |
-- | | transitionDuration    | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.PasswordInput as PasswordInput
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic password input (inherits all visual properties from context)
-- | PasswordInput.passwordInput
-- |   [ PasswordInput.passwordValue state.password
-- |   , PasswordInput.onPasswordInput UpdatePassword
-- |   ]
-- |
-- | -- With visibility toggle
-- | PasswordInput.passwordInput
-- |   [ PasswordInput.passwordValue state.password
-- |   , PasswordInput.showToggle true
-- |   , PasswordInput.passwordVisible state.showPassword
-- |   , PasswordInput.onToggle ToggleVisibility
-- |   , PasswordInput.toggleButtonColor brand.mutedForeground
-- |   ]
-- |
-- | -- With strength indicator using brand colors
-- | PasswordInput.passwordInput
-- |   [ PasswordInput.passwordValue state.password
-- |   , PasswordInput.showStrength true
-- |   , PasswordInput.strengthVeryWeakColor brand.destructive
-- |   , PasswordInput.strengthStrongColor brand.success
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | - `Types` — PasswordStrength type and calculation
-- | - `Props` — Property types and defaults
-- | - `Builders` — Property modifier functions
-- | - `Render` — Main components
-- | - `Icons` — SVG icons

module Hydrogen.Element.Compound.PasswordInput
  ( -- * Re-exported modules
    module Types
  , module Props
  , module Builders
  , module Render
  ) where

-- Re-export from submodules

import Hydrogen.Element.Compound.PasswordInput.Types
  ( PasswordStrength(VeryWeak, Weak, Fair, Strong, VeryStrong)
  , calculateStrength
  , strengthLabel
  ) as Types

import Hydrogen.Element.Compound.PasswordInput.Props
  ( PasswordInputProps
  , PasswordInputProp
  , defaultProps
  ) as Props

import Hydrogen.Element.Compound.PasswordInput.Builders
  ( passwordValue
  , passwordVisible
  , showToggle
  , showStrength
  , placeholder
  , passwordDisabled
  , passwordRequired
  , autoComplete
  , passwordMinLength
  , passwordMaxLength
  , passwordId
  , passwordName
  , passwordAriaLabel
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , focusRingColor
  , toggleButtonColor
  , strengthVeryWeakColor
  , strengthWeakColor
  , strengthFairColor
  , strengthStrongColor
  , strengthVeryStrongColor
  , strengthLabelColor
  , strengthBarBgColor
  , borderRadius
  , borderWidth
  , height
  , paddingX
  , paddingY
  , iconSize
  , fontSize
  , strengthLabelFontSize
  , transitionDuration
  , onPasswordInput
  , onPasswordChange
  , onToggle
  , onPasswordFocus
  , onPasswordBlur
  , extraAttributes
  ) as Builders

import Hydrogen.Element.Compound.PasswordInput.Render
  ( passwordInput
  , passwordStrengthBar
  ) as Render
