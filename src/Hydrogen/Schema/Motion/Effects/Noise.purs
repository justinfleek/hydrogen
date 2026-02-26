-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // motion // effects // noise
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Noise effect enums for motion graphics.
-- |
-- | Defines fractal noise types and base noise types.

module Hydrogen.Schema.Motion.Effects.Noise
  ( -- * Fractal Type
    FractalType(..)
  , allFractalTypes
  , fractalTypeToString
  , fractalTypeFromString
  
    -- * Noise Type
  , NoiseType(..)
  , allNoiseTypes
  , noiseTypeToString
  , noiseTypeFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // fractal // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of fractal noise generation.
data FractalType
  = FTBasic          -- ^ Basic fractal noise
  | FTTurbulentBasic -- ^ Turbulent (absolute value)
  | FTSoftLinear     -- ^ Soft linear interpolation
  | FTTurbulentSoft  -- ^ Turbulent with soft interp

derive instance eqFractalType :: Eq FractalType
derive instance ordFractalType :: Ord FractalType

instance showFractalType :: Show FractalType where
  show FTBasic = "FTBasic"
  show FTTurbulentBasic = "FTTurbulentBasic"
  show FTSoftLinear = "FTSoftLinear"
  show FTTurbulentSoft = "FTTurbulentSoft"

-- | All fractal types for enumeration
allFractalTypes :: Array FractalType
allFractalTypes = [ FTBasic, FTTurbulentBasic, FTSoftLinear, FTTurbulentSoft ]

fractalTypeToString :: FractalType -> String
fractalTypeToString FTBasic = "basic"
fractalTypeToString FTTurbulentBasic = "turbulent-basic"
fractalTypeToString FTSoftLinear = "soft-linear"
fractalTypeToString FTTurbulentSoft = "turbulent-soft"

fractalTypeFromString :: String -> Maybe FractalType
fractalTypeFromString "basic" = Just FTBasic
fractalTypeFromString "turbulent-basic" = Just FTTurbulentBasic
fractalTypeFromString "soft-linear" = Just FTSoftLinear
fractalTypeFromString "turbulent-soft" = Just FTTurbulentSoft
fractalTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // noise // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of base noise.
data NoiseType
  = NTBlock       -- ^ Block/cell noise
  | NTLinear      -- ^ Linear interpolated
  | NTSoftLinear  -- ^ Soft linear
  | NTSpline      -- ^ Spline interpolated

derive instance eqNoiseType :: Eq NoiseType
derive instance ordNoiseType :: Ord NoiseType

instance showNoiseType :: Show NoiseType where
  show NTBlock = "NTBlock"
  show NTLinear = "NTLinear"
  show NTSoftLinear = "NTSoftLinear"
  show NTSpline = "NTSpline"

-- | All noise types for enumeration
allNoiseTypes :: Array NoiseType
allNoiseTypes = [ NTBlock, NTLinear, NTSoftLinear, NTSpline ]

noiseTypeToString :: NoiseType -> String
noiseTypeToString NTBlock = "block"
noiseTypeToString NTLinear = "linear"
noiseTypeToString NTSoftLinear = "soft-linear"
noiseTypeToString NTSpline = "spline"

noiseTypeFromString :: String -> Maybe NoiseType
noiseTypeFromString "block" = Just NTBlock
noiseTypeFromString "linear" = Just NTLinear
noiseTypeFromString "soft-linear" = Just NTSoftLinear
noiseTypeFromString "spline" = Just NTSpline
noiseTypeFromString _ = Nothing
