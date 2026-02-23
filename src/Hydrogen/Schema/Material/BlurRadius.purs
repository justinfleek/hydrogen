-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // material // blurradius
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BlurRadius - Gaussian blur amount.
-- |
-- | Measured in pixels, representing the radius of the blur kernel.
-- | Used for backdrop blur, shadow blur, and filter effects.
-- |
-- | Range: 0 to finite (clamps at 0, no upper bound but must remain finite)
-- | - **0**: No blur (sharp)
-- | - **10**: Subtle blur
-- | - **50**: Heavy blur
-- | - **100+**: Extreme blur
-- |
-- | Note: Very large values may impact performance significantly.

module Hydrogen.Schema.Material.BlurRadius
  ( BlurRadius
  , blurRadius
  , unwrap
  , toNumber
  , bounds
  , none
  , subtle
  , moderate
  , heavy
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // blurradius
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Blur radius in pixels (0 to finite)
-- |
-- | Represents the radius of a Gaussian blur kernel. Larger values create
-- | more pronounced blurring effects.
newtype BlurRadius = BlurRadius Number

derive instance eqBlurRadius :: Eq BlurRadius
derive instance ordBlurRadius :: Ord BlurRadius

instance showBlurRadius :: Show BlurRadius where
  show (BlurRadius r) = show r <> "px"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a blur radius, clamping to 0 minimum and ensuring finite
blurRadius :: Number -> BlurRadius
blurRadius n = BlurRadius (Bounded.clampNumberMin 0.0 n)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | No blur (sharp)
none :: BlurRadius
none = BlurRadius 0.0

-- | Subtle blur (10px)
subtle :: BlurRadius
subtle = BlurRadius 10.0

-- | Moderate blur (25px)
moderate :: BlurRadius
moderate = BlurRadius 25.0

-- | Heavy blur (50px)
heavy :: BlurRadius
heavy = BlurRadius 50.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: BlurRadius -> Number
unwrap (BlurRadius r) = r

-- | Convert to Number (passthrough for this type)
toNumber :: BlurRadius -> Number
toNumber (BlurRadius r) = r

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1000.0 "blurRadius" "Gaussian blur radius in pixels"
