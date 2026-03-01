-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // composition // effect // distort
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Distortion Effects — Displacement, Warp, Bulge, Ripple, Twirl.
-- |
-- | Distortion effects modify pixel positions without changing color values.
-- | All parameters are bounded to prevent invalid spatial transformations.

module Hydrogen.Composition.Effect.Distort
  ( DisplacementSpec
  , WarpSpec
  , WarpType
      ( WarpArc
      , WarpBulge
      , WarpFlag
      , WarpWave
      , WarpFish
      , WarpInflate
      )
  , BulgeSpec
  , RippleSpec
  , TwirlSpec
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // displacement
-- ═══════════════════════════════════════════════════════════════════════════════

type DisplacementSpec =
  { mapSource :: String   -- Asset reference for displacement map
  , horizontalScale :: Number  -- -1000 to 1000
  , verticalScale :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // warp
-- ═══════════════════════════════════════════════════════════════════════════════

data WarpType
  = WarpArc | WarpBulge | WarpFlag | WarpWave | WarpFish | WarpInflate

derive instance eqWarpType :: Eq WarpType

instance showWarpType :: Show WarpType where
  show WarpArc = "arc"
  show WarpBulge = "bulge"
  show WarpFlag = "flag"
  show WarpWave = "wave"
  show WarpFish = "fish"
  show WarpInflate = "inflate"

type WarpSpec =
  { warpType :: WarpType
  , bend :: Number        -- -100 to 100
  , horizontalDistortion :: Number
  , verticalDistortion :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // bulge
-- ═══════════════════════════════════════════════════════════════════════════════

type BulgeSpec =
  { centerX :: Number     -- 0-1
  , centerY :: Number
  , radius :: Number      -- 0-1000
  , amount :: Number      -- -100 to 100
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // ripple
-- ═══════════════════════════════════════════════════════════════════════════════

type RippleSpec =
  { centerX :: Number
  , centerY :: Number
  , radius :: Number
  , wavelength :: Number  -- 1-500
  , amplitude :: Number   -- 0-500
  , phase :: Number       -- 0-360 (animatable)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // twirl
-- ═══════════════════════════════════════════════════════════════════════════════

type TwirlSpec =
  { centerX :: Number
  , centerY :: Number
  , radius :: Number
  , angle :: Number       -- -3600 to 3600 degrees
  }
