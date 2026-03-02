-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // engineering // tolerance // fit
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ISO fit classes and surface finish specifications.
-- |
-- | ## Fit Classes
-- |
-- | ISO fit classes for hole/shaft systems:
-- | - **Clearance fits**: H11/c11, H9/d9, H8/f7, H7/g6, H7/h6
-- | - **Transition fits**: H7/k6, H7/m6, H7/n6
-- | - **Interference fits**: H7/p6, H7/s6, H7/u6
-- |
-- | ## Surface Finish
-- |
-- | Surface roughness Ra in micrometers, from mirror polish to as-cast.

module Hydrogen.Schema.Engineering.Tolerance.Fit
  ( -- * Fit Classes
    FitClass(H11c11, H9d9, H8f7, H7g6, H7h6, H7k6, H7m6, H7n6, H7p6, H7s6, H7u6)
  , allFitClasses
  , fitDescription
  , fitTolerance
  
  -- * Surface Finish
  , SurfaceFinish
  , surfaceFinish
  , surfaceFinishUnsafe
  , unwrapFinish
  , finishBounds
  , roughnessRa
  
  -- * Surface Finish Constants
  , finishMirror
  , finishGround
  , finishMachined
  , finishRough
  , finishCast
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // fit // classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | ISO fit classes for hole/shaft systems.
data FitClass
  -- Clearance fits
  = H11c11  -- ^ Loose running fit
  | H9d9    -- ^ Free running fit
  | H8f7    -- ^ Close running fit
  | H7g6    -- ^ Sliding fit
  | H7h6    -- ^ Locational clearance fit
  -- Transition fits
  | H7k6    -- ^ Locational transition fit
  | H7m6    -- ^ Locational transition fit (tighter)
  | H7n6    -- ^ Locational transition fit (tightest)
  -- Interference fits
  | H7p6    -- ^ Locational interference fit
  | H7s6    -- ^ Medium drive fit
  | H7u6    -- ^ Force fit

derive instance eqFitClass :: Eq FitClass
derive instance ordFitClass :: Ord FitClass

instance showFitClass :: Show FitClass where
  show H11c11 = "H11/c11"
  show H9d9 = "H9/d9"
  show H8f7 = "H8/f7"
  show H7g6 = "H7/g6"
  show H7h6 = "H7/h6"
  show H7k6 = "H7/k6"
  show H7m6 = "H7/m6"
  show H7n6 = "H7/n6"
  show H7p6 = "H7/p6"
  show H7s6 = "H7/s6"
  show H7u6 = "H7/u6"

-- | All fit classes for enumeration.
allFitClasses :: Array FitClass
allFitClasses = 
  [H11c11, H9d9, H8f7, H7g6, H7h6, H7k6, H7m6, H7n6, H7p6, H7s6, H7u6]

-- | Description of fit class.
fitDescription :: FitClass -> String
fitDescription H11c11 = "Loose running fit - large clearance"
fitDescription H9d9 = "Free running fit - general purpose"
fitDescription H8f7 = "Close running fit - accurate location"
fitDescription H7g6 = "Sliding fit - accurate location, free movement"
fitDescription H7h6 = "Locational clearance fit - minimal clearance"
fitDescription H7k6 = "Locational transition fit - may have slight clearance/interference"
fitDescription H7m6 = "Locational transition fit - tighter"
fitDescription H7n6 = "Locational transition fit - tightest transition"
fitDescription H7p6 = "Locational interference fit - light press"
fitDescription H7s6 = "Medium drive fit - assembly by press"
fitDescription H7u6 = "Force fit - permanent assembly"

-- | Approximate tolerance grade for a 25mm nominal (mm).
fitTolerance :: FitClass -> Number
fitTolerance H11c11 = 0.130
fitTolerance H9d9 = 0.052
fitTolerance H8f7 = 0.033
fitTolerance H7g6 = 0.021
fitTolerance H7h6 = 0.021
fitTolerance H7k6 = 0.021
fitTolerance H7m6 = 0.021
fitTolerance H7n6 = 0.021
fitTolerance H7p6 = 0.021
fitTolerance H7s6 = 0.021
fitTolerance H7u6 = 0.021

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // surface // finish
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surface roughness Ra in micrometers [0.01, 50.0].
-- |
-- | Ra = arithmetic average roughness.
newtype SurfaceFinish = SurfaceFinish Number

derive instance eqSurfaceFinish :: Eq SurfaceFinish
derive instance ordSurfaceFinish :: Ord SurfaceFinish

instance showSurfaceFinish :: Show SurfaceFinish where
  show (SurfaceFinish n) = "Ra " <> show n <> " um"

-- | Safe constructor with clamping.
surfaceFinish :: Number -> SurfaceFinish
surfaceFinish n = SurfaceFinish (Bounded.clampNumber 0.01 50.0 n)

-- | Unsafe constructor for known-valid values.
surfaceFinishUnsafe :: Number -> SurfaceFinish
surfaceFinishUnsafe = SurfaceFinish

-- | Extract raw value.
unwrapFinish :: SurfaceFinish -> Number
unwrapFinish (SurfaceFinish n) = n

-- | Valid bounds documentation.
finishBounds :: Bounded.NumberBounds
finishBounds = Bounded.numberBounds 0.01 50.0 Bounded.Clamps "surfaceFinish" "Surface roughness Ra in um"

-- | Get roughness in micrometers (identity).
roughnessRa :: SurfaceFinish -> Number
roughnessRa = unwrapFinish

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // surface finish // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mirror finish (Ra 0.05 um).
finishMirror :: SurfaceFinish
finishMirror = SurfaceFinish 0.05

-- | Ground finish (Ra 0.4 um).
finishGround :: SurfaceFinish
finishGround = SurfaceFinish 0.4

-- | Machined finish (Ra 1.6 um).
finishMachined :: SurfaceFinish
finishMachined = SurfaceFinish 1.6

-- | Rough finish (Ra 6.3 um).
finishRough :: SurfaceFinish
finishRough = SurfaceFinish 6.3

-- | Cast finish (Ra 25.0 um).
finishCast :: SurfaceFinish
finishCast = SurfaceFinish 25.0
