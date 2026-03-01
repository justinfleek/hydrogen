-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // blur // misc
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Miscellaneous Blur Effects — Compound Blur and Fast Blur.
-- |
-- | - Compound Blur: Variable blur based on a control layer
-- | - Fast Blur: Legacy blur optimized for performance

module Hydrogen.Schema.Motion.Effects.Blur.Misc
  ( -- * Compound Blur Effect
    CompoundBlurEffect
  , defaultCompoundBlur
  , mkCompoundBlur
  
  -- * Fast Blur Effect
  , FastBlurEffect
  , defaultFastBlur
  , mkFastBlur
  ) where

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Effects.Blur.Types
  ( BlurDimension(BDBoth)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // compound // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compound Blur effect — variable blur based on a control layer.
-- |
-- | Uses another layer's luminance to control blur amount per-pixel.
type CompoundBlurEffect =
  { maxBlur :: Number             -- ^ Maximum blur amount (0-500)
  , stretchMapToFit :: Boolean    -- ^ Stretch blur map to layer size
  , invertBlur :: Boolean         -- ^ Invert blur map values
  }

defaultCompoundBlur :: CompoundBlurEffect
defaultCompoundBlur =
  { maxBlur: 20.0
  , stretchMapToFit: true
  , invertBlur: false
  }

mkCompoundBlur :: Number -> Boolean -> Boolean -> CompoundBlurEffect
mkCompoundBlur maxB stretch invert =
  { maxBlur: clampNumber 0.0 500.0 maxB
  , stretchMapToFit: stretch
  , invertBlur: invert
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // fast // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fast Blur effect — legacy blur for performance.
-- |
-- | Similar to Gaussian but optimized for speed.
type FastBlurEffect =
  { blurriness :: Number         -- ^ Blur amount (0-1000)
  , dimensions :: BlurDimension  -- ^ Direction
  , repeatEdgePixels :: Boolean  -- ^ Edge handling
  }

defaultFastBlur :: FastBlurEffect
defaultFastBlur =
  { blurriness: 0.0
  , dimensions: BDBoth
  , repeatEdgePixels: true
  }

mkFastBlur :: Number -> BlurDimension -> Boolean -> FastBlurEffect
mkFastBlur blur dim repeat =
  { blurriness: clampNumber 0.0 1000.0 blur
  , dimensions: dim
  , repeatEdgePixels: repeat
  }
