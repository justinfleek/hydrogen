-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // gpu // compute-kernel/distortion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel/Distortion — GPU Distortion Effect Kernel Types
-- |
-- | Spatial distortion operations:
-- | - Displacement: Texture-driven pixel offset
-- | - Warp: Geometric deformation (sphere, pinch, twirl)
-- | - Ripple: Animated wave distortion

module Hydrogen.GPU.ComputeKernel.Distortion
  ( -- * Distortion Types
    DistortionKernel(DistortDisplacement, DistortWarp, DistortRipple)
  , DisplacementChannel(DisplaceRed, DisplaceGreen, DisplaceBlue, DisplaceAlpha, DisplaceLuminance)
  , WarpType(WarpSphere, WarpPinch, WarpTwirl, WarpWave)
  
  -- * Specific Kernels
  , DisplacementKernel(DisplacementKernel)
  , WarpKernel(WarpKernel)
  , RippleKernel(RippleKernel)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.GPU.ComputeKernel.Core
  ( KernelConfig
  , KernelInput
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // distortion kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distortion kernel variants
-- |
-- | Each variant maps to a WebGPU compute shader with workgroup 16x16x1.
data DistortionKernel
  = DistortDisplacement DisplacementKernel
  | DistortWarp WarpKernel
  | DistortRipple RippleKernel

derive instance eqDistortionKernel :: Eq DistortionKernel

instance showDistortionKernel :: Show DistortionKernel where
  show (DistortDisplacement k) = "(DistortDisplacement " <> show k <> ")"
  show (DistortWarp k) = "(DistortWarp " <> show k <> ")"
  show (DistortRipple k) = "(DistortRipple " <> show k <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // displacement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Displacement map kernel
-- |
-- | Uses a texture to drive per-pixel offset.
newtype DisplacementKernel = DisplacementKernel
  { mapInput :: KernelInput    -- Displacement map source
  , scaleX :: Number           -- X displacement scale
  , scaleY :: Number           -- Y displacement scale
  , channel :: DisplacementChannel
  , config :: KernelConfig
  }

derive instance eqDisplacementKernel :: Eq DisplacementKernel

instance showDisplacementKernel :: Show DisplacementKernel where
  show (DisplacementKernel k) = "(DisplacementKernel scaleX:" <> show k.scaleX <> ")"

-- | Channel to use for displacement
-- |
-- | Determines which channel of the displacement map drives the offset.
data DisplacementChannel
  = DisplaceRed
  | DisplaceGreen
  | DisplaceBlue
  | DisplaceAlpha
  | DisplaceLuminance          -- Grayscale from RGB

derive instance eqDisplacementChannel :: Eq DisplacementChannel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // warp
-- ═════════════════════════════════════════════════════════════════════════════

-- | Warp kernel (mesh deformation)
-- |
-- | Applies geometric distortion around a center point.
newtype WarpKernel = WarpKernel
  { warpType :: WarpType
  , strength :: Number         -- Warp strength
  , centerX :: Number          -- Warp center X (0.0-1.0)
  , centerY :: Number          -- Warp center Y (0.0-1.0)
  , config :: KernelConfig
  }

derive instance eqWarpKernel :: Eq WarpKernel

instance showWarpKernel :: Show WarpKernel where
  show (WarpKernel k) = "(WarpKernel " <> show k.warpType <> ")"

-- | Warp types
-- |
-- | Different geometric distortion modes:
-- | - Sphere: Push/pull as if wrapped on sphere
-- | - Pinch: Squeeze toward/from center
-- | - Twirl: Rotate around center with falloff
-- | - Wave: Sinusoidal displacement
data WarpType
  = WarpSphere               -- Spherize
  | WarpPinch                -- Pinch/bulge
  | WarpTwirl                -- Twirl/swirl
  | WarpWave                 -- Wave distortion

derive instance eqWarpType :: Eq WarpType

instance showWarpType :: Show WarpType where
  show WarpSphere = "WarpSphere"
  show WarpPinch = "WarpPinch"
  show WarpTwirl = "WarpTwirl"
  show WarpWave = "WarpWave"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // ripple
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ripple kernel
-- |
-- | Creates circular wave distortion emanating from center.
-- | Animate `phase` for water-like effects.
newtype RippleKernel = RippleKernel
  { amplitude :: Number        -- Wave amplitude
  , frequency :: Number        -- Wave frequency
  , phase :: Number            -- Phase offset (for animation)
  , centerX :: Number
  , centerY :: Number
  , damping :: Number          -- Distance falloff
  , config :: KernelConfig
  }

derive instance eqRippleKernel :: Eq RippleKernel

instance showRippleKernel :: Show RippleKernel where
  show (RippleKernel k) = "(RippleKernel amplitude:" <> show k.amplitude <> ")"
