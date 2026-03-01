-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // motion // blur // sharpen
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sharpen Effects — Sharpen and Unsharp Mask.
-- |
-- | These effects increase local contrast to enhance edges and detail.
-- | The opposite of blur effects.

module Hydrogen.Schema.Motion.Effects.Blur.Sharpen
  ( -- * Sharpen Effect
    SharpenEffect
  , defaultSharpen
  , mkSharpen
  , isSharpenNeutral
  , sharpenToString
  
  -- * Unsharp Mask Effect
  , UnsharpMaskEffect
  , defaultUnsharpMask
  , mkUnsharpMask
  , isUnsharpMaskNeutral
  , unsharpMaskToString
  ) where

import Prelude
  ( class Show
  , show
  , (<>)
  , (==)
  )

import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // sharpen
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sharpen effect — basic sharpening.
-- |
-- | Increases contrast between adjacent pixels to enhance edges.
-- | Simple but effective for subtle sharpening.
-- |
-- | AE Properties:
-- | - Sharpen Amount: Intensity of sharpening (0-500)
type SharpenEffect =
  { sharpenAmount :: Number  -- ^ Sharpening intensity (0-500)
  }

defaultSharpen :: SharpenEffect
defaultSharpen =
  { sharpenAmount: 0.0
  }

mkSharpen :: Number -> SharpenEffect
mkSharpen amt =
  { sharpenAmount: clampNumber 0.0 500.0 amt
  }

isSharpenNeutral :: SharpenEffect -> Boolean
isSharpenNeutral effect = effect.sharpenAmount == 0.0

-- | Serialize Sharpen to readable string.
sharpenToString :: SharpenEffect -> String
sharpenToString effect =
  "Sharpen(" <> show effect.sharpenAmount <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // unsharp // mask
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unsharp Mask effect — professional sharpening with controls.
-- |
-- | Uses the classic unsharp masking technique: subtracts a blurred version
-- | of the image to enhance edges. More control than basic Sharpen.
-- |
-- | AE Properties:
-- | - Amount: Sharpening intensity as percentage (0-500%)
-- | - Radius: Size of sharpening halo in pixels (0.1-250)
-- | - Threshold: Minimum brightness change to sharpen (0-255)
-- |   Lower values sharpen more of the image including noise.
type UnsharpMaskEffect =
  { amount :: Number     -- ^ Sharpening intensity (0-500%)
  , radius :: Number     -- ^ Halo radius in pixels (0.1-250)
  , threshold :: Number  -- ^ Minimum contrast to sharpen (0-255)
  }

defaultUnsharpMask :: UnsharpMaskEffect
defaultUnsharpMask =
  { amount: 100.0
  , radius: 1.0
  , threshold: 0.0
  }

mkUnsharpMask :: Number -> Number -> Number -> UnsharpMaskEffect
mkUnsharpMask amt rad thresh =
  { amount: clampNumber 0.0 500.0 amt
  , radius: clampNumber 0.1 250.0 rad
  , threshold: clampNumber 0.0 255.0 thresh
  }

isUnsharpMaskNeutral :: UnsharpMaskEffect -> Boolean
isUnsharpMaskNeutral effect = effect.amount == 0.0

-- | Serialize Unsharp Mask to readable string.
unsharpMaskToString :: UnsharpMaskEffect -> String
unsharpMaskToString effect =
  "UnsharpMask(" <> show effect.amount <> "%, r=" <>
  show effect.radius <> ", thresh=" <> show effect.threshold <> ")"
