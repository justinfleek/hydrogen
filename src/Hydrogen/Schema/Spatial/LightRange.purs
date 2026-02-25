-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // spatial // light range
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LightRange Atom — Distance at which light intensity falls to zero.
-- |
-- | Used for Point and Spot lights.
-- | 0.0 typically means "infinite" range (no attenuation) in some engines,
-- | but in physically correct PBR, light always attenuates.
-- | Here, 0.0 represents point source with no hard cutoff.

module Hydrogen.Schema.Spatial.LightRange
  ( LightRange
  , lightRange
  , unsafeLightRange
  , unwrapLightRange
  , infinite
  ) where

import Prelude
import Hydrogen.Schema.Bounded as Bounded

-- | Light attenuation range
newtype LightRange = LightRange Number

derive instance eqLightRange :: Eq LightRange
derive instance ordLightRange :: Ord LightRange

instance showLightRange :: Show LightRange where
  show (LightRange r) = "(LightRange " <> show r <> ")"

-- | Create LightRange (non-negative)
lightRange :: Number -> LightRange
lightRange n
  | n < 0.0 = LightRange 0.0
  | otherwise = LightRange n

unsafeLightRange :: Number -> LightRange
unsafeLightRange = LightRange

unwrapLightRange :: LightRange -> Number
unwrapLightRange (LightRange n) = n

-- | Infinite range (physically correct inverse-square falloff without cutoff)
infinite :: LightRange
infinite = LightRange 0.0
