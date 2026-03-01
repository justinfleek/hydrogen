-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // motion // blur // radial
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Radial Blur Effect — spin or zoom blur around a center point.

module Hydrogen.Schema.Motion.Effects.Blur.Radial
  ( -- * Radial Blur Effect
    RadialBlurEffect
  , defaultRadialBlur
  , mkRadialBlur
  
  -- * Queries
  , isRadialNeutral
  
  -- * Validation
  , validateRadialBlur
  
  -- * Serialization
  , radialBlurToString
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
  ( RadialBlurType(RBTSpin)
  , AntialiasingQuality(AAQHigh)
  , BlurValidationError(BlurOutOfRange, InvalidCenter)
  , radialBlurTypeToString
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // radial // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radial Blur effect — spin or zoom blur around a center point.
type RadialBlurEffect =
  { amount :: Number              -- ^ Blur intensity (0-100)
  , centerX :: Number             -- ^ Center X position (0-1 normalized)
  , centerY :: Number             -- ^ Center Y position (0-1 normalized)
  , blurType :: RadialBlurType    -- ^ Spin or Zoom
  , quality :: AntialiasingQuality -- ^ Render quality
  }

defaultRadialBlur :: RadialBlurEffect
defaultRadialBlur =
  { amount: 0.0
  , centerX: 0.5
  , centerY: 0.5
  , blurType: RBTSpin
  , quality: AAQHigh
  }

mkRadialBlur :: Number -> Number -> Number -> RadialBlurType -> AntialiasingQuality -> RadialBlurEffect
mkRadialBlur amt cx cy bt qual =
  { amount: clampNumber 0.0 100.0 amt
  , centerX: clampNumber 0.0 1.0 cx
  , centerY: clampNumber 0.0 1.0 cy
  , blurType: bt
  , quality: qual
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

isRadialNeutral :: RadialBlurEffect -> Boolean
isRadialNeutral effect = effect.amount == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate Radial blur parameters.
validateRadialBlur :: RadialBlurEffect -> Maybe BlurValidationError
validateRadialBlur effect
  | effect.amount < 0.0 = Just (BlurOutOfRange "amount" effect.amount 0.0 100.0)
  | effect.amount > 100.0 = Just (BlurOutOfRange "amount" effect.amount 0.0 100.0)
  | effect.centerX < 0.0 = Just (InvalidCenter effect.centerX effect.centerY)
  | effect.centerX > 1.0 = Just (InvalidCenter effect.centerX effect.centerY)
  | effect.centerY < 0.0 = Just (InvalidCenter effect.centerX effect.centerY)
  | effect.centerY > 1.0 = Just (InvalidCenter effect.centerX effect.centerY)
  | otherwise = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Radial blur to readable string.
radialBlurToString :: RadialBlurEffect -> String
radialBlurToString effect =
  "RadialBlur(" <> show effect.amount <> "%, " <>
  radialBlurTypeToString effect.blurType <> ", center=" <>
  show effect.centerX <> "," <> show effect.centerY <> ")"
