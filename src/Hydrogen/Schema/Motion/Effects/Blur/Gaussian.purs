-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // motion // blur // gaussian
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gaussian Blur Effect — smooth, bell-curve weighted blur.
-- |
-- | The most common blur type, producing natural-looking softening.
-- | Also includes the Semigroup-based CombinableGaussian wrapper.

module Hydrogen.Schema.Motion.Effects.Blur.Gaussian
  ( -- * Gaussian Blur Effect
    GaussianBlurEffect
  , defaultGaussianBlur
  , mkGaussianBlur
  
  -- * Queries
  , isGaussianNeutral
  , hasVisibleBlur
  
  -- * Validation
  , validateGaussianBlur
  , validateAllGaussianBlurs
  
  -- * Serialization
  , gaussianBlurToString
  
  -- * Comparisons
  , compareBlurIntensity
  , isStrongerBlur
  , isWeakerBlur
  
  -- * Composition
  , combineGaussianBlurs
  
  -- * Scaling
  , scaleGaussianBlur
  
  -- * Transitions
  , lerpGaussianBlur
  
  -- * Functor Operations
  , mapBlurAmount
  
  -- * Combinable Blur (Semigroup)
  , CombinableGaussian(CombinableGaussian)
  , toCombinableGaussian
  , fromCombinableGaussian
  ) where

import Prelude
  ( class Eq
  , class Semigroup
  , class Show
  , show
  , (<>)
  , (||)
  , not
  , (==)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (+)
  , (*)
  , negate
  , compare
  , map
  , pure
  , bind
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Ordering (Ordering)
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Effects.Blur.Types
  ( BlurDimension(BDBoth)
  , BlurValidationError(BlurOutOfRange)
  , blurDimensionToString
  , combineDimensions
  , lerpNum
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // gaussian // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gaussian Blur effect — smooth, bell-curve weighted blur.
-- |
-- | Properties:
-- | - blurriness: Blur radius in pixels (0-1000)
-- | - dimensions: Horizontal, Vertical, or Both
-- | - repeatEdgePixels: Prevents edge transparency
type GaussianBlurEffect =
  { blurriness :: Number         -- ^ Blur radius in pixels (0-1000)
  , dimensions :: BlurDimension  -- ^ Direction of blur
  , repeatEdgePixels :: Boolean  -- ^ Extend edge pixels to avoid transparency
  }

defaultGaussianBlur :: GaussianBlurEffect
defaultGaussianBlur =
  { blurriness: 0.0
  , dimensions: BDBoth
  , repeatEdgePixels: true
  }

mkGaussianBlur :: Number -> BlurDimension -> Boolean -> GaussianBlurEffect
mkGaussianBlur blur dim repeat =
  { blurriness: clampNumber 0.0 1000.0 blur
  , dimensions: dim
  , repeatEdgePixels: repeat
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

isGaussianNeutral :: GaussianBlurEffect -> Boolean
isGaussianNeutral effect = effect.blurriness == 0.0

-- | Check if a Gaussian blur has visible effect.
-- | A blur is visible if amount is greater than a small threshold.
hasVisibleBlur :: GaussianBlurEffect -> Boolean
hasVisibleBlur effect = effect.blurriness >= 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate Gaussian blur parameters.
-- | Returns Nothing if valid, Just error if invalid.
validateGaussianBlur :: GaussianBlurEffect -> Maybe BlurValidationError
validateGaussianBlur effect
  | effect.blurriness < 0.0 = Just (BlurOutOfRange "blurriness" effect.blurriness 0.0 1000.0)
  | effect.blurriness > 1000.0 = Just (BlurOutOfRange "blurriness" effect.blurriness 0.0 1000.0)
  | otherwise = Nothing

-- | Validate an array of Gaussian blur effects.
-- | Returns array of errors for any invalid effects.
validateAllGaussianBlurs :: Array GaussianBlurEffect -> Array BlurValidationError
validateAllGaussianBlurs effects = 
  bind effects (\effect -> 
    case validateGaussianBlur effect of
      Nothing -> []
      Just err -> pure err
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Gaussian blur to readable string.
gaussianBlurToString :: GaussianBlurEffect -> String
gaussianBlurToString effect =
  "GaussianBlur(" <> show effect.blurriness <> "px, " <>
  blurDimensionToString effect.dimensions <> 
  (if not effect.repeatEdgePixels then ", no-repeat" else "") <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // comparisons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare blur intensity of two Gaussian blurs.
-- | Returns LT if first is weaker, GT if stronger, EQ if equal.
compareBlurIntensity :: GaussianBlurEffect -> GaussianBlurEffect -> Ordering
compareBlurIntensity a b = compare a.blurriness b.blurriness

-- | Check if first Gaussian blur is stronger than second.
isStrongerBlur :: GaussianBlurEffect -> GaussianBlurEffect -> Boolean
isStrongerBlur a b = a.blurriness > b.blurriness

-- | Check if first Gaussian blur is weaker than second.
isWeakerBlur :: GaussianBlurEffect -> GaussianBlurEffect -> Boolean
isWeakerBlur a b = a.blurriness < b.blurriness

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two Gaussian blurs by adding their blur amounts.
-- | Resulting blur is clamped to valid range.
combineGaussianBlurs :: GaussianBlurEffect -> GaussianBlurEffect -> GaussianBlurEffect
combineGaussianBlurs a b =
  { blurriness: clampNumber 0.0 1000.0 (a.blurriness + b.blurriness)
  , dimensions: combineDimensions a.dimensions b.dimensions
  , repeatEdgePixels: a.repeatEdgePixels || b.repeatEdgePixels
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // scaling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale a Gaussian blur by a factor.
-- | Negative factors are negated (blur cannot be negative).
scaleGaussianBlur :: Number -> GaussianBlurEffect -> GaussianBlurEffect
scaleGaussianBlur factor effect =
  let scaleFactor = if factor < 0.0 then negate factor else factor
  in effect { blurriness = clampNumber 0.0 1000.0 (effect.blurriness * scaleFactor) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two Gaussian blurs.
-- | t=0 returns from, t=1 returns to.
lerpGaussianBlur :: Number -> GaussianBlurEffect -> GaussianBlurEffect -> GaussianBlurEffect
lerpGaussianBlur t from to =
  let t' = clampNumber 0.0 1.0 t
  in { blurriness: lerpNum t' from.blurriness to.blurriness
     , dimensions: if t' <= 0.5 then from.dimensions else to.dimensions
     , repeatEdgePixels: if t' <= 0.5 then from.repeatEdgePixels else to.repeatEdgePixels
     }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // functor operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map over blur amounts in an array of Gaussian effects.
-- | Applies a transformation function to each blur's blurriness.
mapBlurAmount :: (Number -> Number) -> Array GaussianBlurEffect -> Array GaussianBlurEffect
mapBlurAmount f effects = map (transformGaussianBlur f) effects
  where
  transformGaussianBlur :: (Number -> Number) -> GaussianBlurEffect -> GaussianBlurEffect
  transformGaussianBlur g effect = 
    effect { blurriness = clampNumber 0.0 1000.0 (g effect.blurriness) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // combinable // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wrapper for Gaussian blur that can be combined with Semigroup.
-- |
-- | Combining two blurs:
-- | - Adds blur amounts (clamped to max 1000)
-- | - Takes the wider dimension (Both wins over Horizontal/Vertical)
-- | - Preserves edge repetition if either has it
-- |
-- | This allows: blur1 <> blur2 <> blur3 for accumulating blur effects.
newtype CombinableGaussian = CombinableGaussian GaussianBlurEffect

derive instance eqCombinableGaussian :: Eq CombinableGaussian

instance semigroupCombinableGaussian :: Semigroup CombinableGaussian where
  append (CombinableGaussian a) (CombinableGaussian b) =
    CombinableGaussian
      { blurriness: clampNumber 0.0 1000.0 (a.blurriness + b.blurriness)
      , dimensions: combineDimensions a.dimensions b.dimensions
      , repeatEdgePixels: a.repeatEdgePixels || b.repeatEdgePixels
      }

instance showCombinableGaussian :: Show CombinableGaussian where
  show (CombinableGaussian g) = "CombinableGaussian(" <> gaussianBlurToString g <> ")"

-- | Wrap a Gaussian blur for combination.
toCombinableGaussian :: GaussianBlurEffect -> CombinableGaussian
toCombinableGaussian = CombinableGaussian

-- | Unwrap a combined Gaussian blur.
fromCombinableGaussian :: CombinableGaussian -> GaussianBlurEffect
fromCombinableGaussian (CombinableGaussian g) = g
