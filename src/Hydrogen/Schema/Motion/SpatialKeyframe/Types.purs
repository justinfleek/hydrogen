-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // spatial-keyframe // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyframe Types — Flags, interpolation modes, and dimension configuration.
-- |
-- | These types control how keyframes behave during animation:
-- |
-- | - **KeyframeFlags**: Roving, locked, continuous bezier, auto bezier
-- | - **SpatialInterpolation**: Linear, bezier, or auto path curves
-- | - **TemporalInterpolation**: Linear, bezier, hold, or auto easing
-- | - **DimensionMode**: Unified (single 2D/3D property) or separated (X/Y/Z)

module Hydrogen.Schema.Motion.SpatialKeyframe.Types
  ( -- * Keyframe Flags
    KeyframeFlags
  , defaultKeyframeFlags
  , setRoving
  , setLockToTime
  , setContinuousBezier
  , setAutoBezier
  
  -- * Spatial Interpolation Type
  , SpatialInterpolation(..)
  , spatialInterpolationToString
  , spatialInterpolationFromString
  
  -- * Temporal Interpolation Type  
  , TemporalInterpolation(..)
  , temporalInterpolationToString
  , temporalInterpolationFromString
  
  -- * Dimension Mode
  , DimensionMode(..)
  , dimensionModeToString
  , dimensionModeFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , not
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // keyframe // flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyframe behavior flags.
-- |
-- | - roving: Auto-adjust time for uniform speed
-- | - lockToTime: Prevent temporal adjustment
-- | - continuousBezier: Tangents are continuous (smooth)
-- | - autoBezier: System calculates tangents automatically
type KeyframeFlags =
  { roving :: Boolean            -- ^ Roving keyframe (auto-time adjustment)
  , lockToTime :: Boolean        -- ^ Locked to specific time
  , continuousBezier :: Boolean  -- ^ Continuous bezier tangents
  , autoBezier :: Boolean        -- ^ Auto-calculated tangents
  }

-- | Default keyframe flags.
defaultKeyframeFlags :: KeyframeFlags
defaultKeyframeFlags =
  { roving: not true
  , lockToTime: not true
  , continuousBezier: not true
  , autoBezier: not true
  }

-- | Set roving flag.
setRoving :: Boolean -> KeyframeFlags -> KeyframeFlags
setRoving r flags = flags { roving = r }

-- | Set lock to time flag.
setLockToTime :: Boolean -> KeyframeFlags -> KeyframeFlags
setLockToTime l flags = flags { lockToTime = l }

-- | Set continuous bezier flag.
setContinuousBezier :: Boolean -> KeyframeFlags -> KeyframeFlags
setContinuousBezier c flags = flags { continuousBezier = c }

-- | Set auto bezier flag.
setAutoBezier :: Boolean -> KeyframeFlags -> KeyframeFlags
setAutoBezier a flags = flags { autoBezier = a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // spatial // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spatial interpolation type (motion path shape).
data SpatialInterpolation
  = SILinear      -- ^ Straight line between keyframes
  | SIBezier      -- ^ Curved path with spatial handles
  | SIAuto        -- ^ Auto-calculated smooth path

derive instance eqSpatialInterpolation :: Eq SpatialInterpolation
derive instance ordSpatialInterpolation :: Ord SpatialInterpolation

instance showSpatialInterpolation :: Show SpatialInterpolation where
  show SILinear = "linear"
  show SIBezier = "bezier"
  show SIAuto = "auto"

spatialInterpolationToString :: SpatialInterpolation -> String
spatialInterpolationToString = show

spatialInterpolationFromString :: String -> Maybe SpatialInterpolation
spatialInterpolationFromString "linear" = Just SILinear
spatialInterpolationFromString "bezier" = Just SIBezier
spatialInterpolationFromString "auto" = Just SIAuto
spatialInterpolationFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // temporal // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal interpolation type (speed curve shape).
data TemporalInterpolation
  = TILinear      -- ^ Constant speed
  | TIBezier      -- ^ Curved speed with temporal handles
  | TIHold        -- ^ No interpolation (instant jump)
  | TIAuto        -- ^ Auto-calculated smooth easing

derive instance eqTemporalInterpolation :: Eq TemporalInterpolation
derive instance ordTemporalInterpolation :: Ord TemporalInterpolation

instance showTemporalInterpolation :: Show TemporalInterpolation where
  show TILinear = "linear"
  show TIBezier = "bezier"
  show TIHold = "hold"
  show TIAuto = "auto"

temporalInterpolationToString :: TemporalInterpolation -> String
temporalInterpolationToString = show

temporalInterpolationFromString :: String -> Maybe TemporalInterpolation
temporalInterpolationFromString "linear" = Just TILinear
temporalInterpolationFromString "bezier" = Just TIBezier
temporalInterpolationFromString "hold" = Just TIHold
temporalInterpolationFromString "auto" = Just TIAuto
temporalInterpolationFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // dimension // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How position dimensions are animated.
data DimensionMode
  = DMUnified      -- ^ Single property with spatial handles
  | DMSeparated    -- ^ X, Y, Z as separate properties

derive instance eqDimensionMode :: Eq DimensionMode
derive instance ordDimensionMode :: Ord DimensionMode

instance showDimensionMode :: Show DimensionMode where
  show DMUnified = "unified"
  show DMSeparated = "separated"

dimensionModeToString :: DimensionMode -> String
dimensionModeToString = show

dimensionModeFromString :: String -> Maybe DimensionMode
dimensionModeFromString "unified" = Just DMUnified
dimensionModeFromString "separated" = Just DMSeparated
dimensionModeFromString _ = Nothing
