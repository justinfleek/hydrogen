-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // motion // blur // box
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Box Blur Effect — uniform-weighted rectangular blur.
-- |
-- | Faster than Gaussian but produces harsher edges.
-- | Multiple iterations approach Gaussian quality.

module Hydrogen.Schema.Motion.Effects.Blur.Box
  ( -- * Box Blur Effect
    BoxBlurEffect
  , defaultBoxBlur
  , mkBoxBlur
  
  -- * Queries
  , isBoxNeutral
  
  -- * Validation
  , validateBoxBlur
  
  -- * Serialization
  , boxBlurToString
  ) where

import Prelude
  ( class Show
  , show
  , (<>)
  , (==)
  , (<)
  , (>)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Effects.Blur.Types
  ( BlurDimension(BDBoth)
  , BlurValidationError(BlurOutOfRange, InvalidIterations)
  , blurDimensionToString
  , clampInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // box // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Box Blur effect — uniform-weighted rectangular blur.
-- |
-- | Faster than Gaussian but produces harsher edges.
-- | Multiple iterations approach Gaussian quality.
type BoxBlurEffect =
  { blurRadius :: Number         -- ^ Blur radius in pixels (0-1000)
  , iterations :: Int            -- ^ Number of passes (1-10)
  , dimensions :: BlurDimension  -- ^ Direction of blur
  , repeatEdgePixels :: Boolean  -- ^ Extend edge pixels
  }

defaultBoxBlur :: BoxBlurEffect
defaultBoxBlur =
  { blurRadius: 0.0
  , iterations: 1
  , dimensions: BDBoth
  , repeatEdgePixels: true
  }

mkBoxBlur :: Number -> Int -> BlurDimension -> Boolean -> BoxBlurEffect
mkBoxBlur radius iter dim repeat =
  { blurRadius: clampNumber 0.0 1000.0 radius
  , iterations: clampInt 1 10 iter
  , dimensions: dim
  , repeatEdgePixels: repeat
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

isBoxNeutral :: BoxBlurEffect -> Boolean
isBoxNeutral effect = effect.blurRadius == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate Box blur parameters.
validateBoxBlur :: BoxBlurEffect -> Maybe BlurValidationError
validateBoxBlur effect
  | effect.blurRadius < 0.0 = Just (BlurOutOfRange "blurRadius" effect.blurRadius 0.0 1000.0)
  | effect.blurRadius > 1000.0 = Just (BlurOutOfRange "blurRadius" effect.blurRadius 0.0 1000.0)
  | effect.iterations < 1 = Just (InvalidIterations effect.iterations)
  | effect.iterations > 10 = Just (InvalidIterations effect.iterations)
  | otherwise = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Box blur to readable string.
boxBlurToString :: BoxBlurEffect -> String
boxBlurToString effect =
  "BoxBlur(" <> show effect.blurRadius <> "px, " <>
  show effect.iterations <> "x, " <>
  blurDimensionToString effect.dimensions <> ")"
