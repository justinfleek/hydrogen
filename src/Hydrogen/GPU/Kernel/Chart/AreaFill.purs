-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // kernel // chart // areafill
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Area Fill Kernel — Filled Area Charts
-- |
-- | ## Purpose
-- |
-- | Area fill rendering for:
-- | - Stacked area charts
-- | - Range visualization
-- | - Gradient fills under lines
-- |
-- | ## Fill Modes
-- |
-- | - ToZero: Fill from line to zero baseline
-- | - ToMin: Fill from line to minimum value
-- | - Between: Fill between two series
-- | - Gradient: Gradient fill with direction

module Hydrogen.GPU.Kernel.Chart.AreaFill
  ( -- * Types
    AreaFillKernel(AreaFillKernel)
  , FillMode
      ( FillToZero
      , FillToMin
      , FillBetween
      , FillGradient
      )
  , GradientDirection
      ( GradientVertical
      , GradientHorizontal
      )
  
  -- * Constructor
  , mkAreaFillKernel
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

import Hydrogen.GPU.Kernel.Chart.Types
  ( ChartColor
  , ChartKernelConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // area fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fill mode for area charts
data FillMode
  = FillToZero             -- Fill from line to zero
  | FillToMin              -- Fill from line to minimum
  | FillBetween            -- Fill between two series
  | FillGradient           -- Gradient fill

derive instance eqFillMode :: Eq FillMode

instance showFillMode :: Show FillMode where
  show FillToZero = "FillToZero"
  show FillToMin = "FillToMin"
  show FillBetween = "FillBetween"
  show FillGradient = "FillGradient"

-- | Gradient direction
data GradientDirection
  = GradientVertical       -- Top to bottom
  | GradientHorizontal     -- Left to right

derive instance eqGradientDirection :: Eq GradientDirection

instance showGradientDirection :: Show GradientDirection where
  show GradientVertical = "GradientVertical"
  show GradientHorizontal = "GradientHorizontal"

-- | Area fill kernel
newtype AreaFillKernel = AreaFillKernel
  { fillMode :: FillMode
  , primaryColor :: ChartColor
  , secondaryColor :: ChartColor  -- For gradient or fill-between
  , gradientDirection :: GradientDirection
  , opacity :: Number
  , seriesIndex :: Int           -- Which series to fill
  , secondSeriesIndex :: Int     -- For fill-between mode
  , config :: ChartKernelConfig
  }

derive instance eqAreaFillKernel :: Eq AreaFillKernel

instance showAreaFillKernel :: Show AreaFillKernel where
  show (AreaFillKernel k) = 
    "(AreaFillKernel mode:" <> show k.fillMode <> ")"

-- | Create area fill kernel
mkAreaFillKernel 
  :: FillMode 
  -> ChartColor 
  -> Number 
  -> ChartKernelConfig 
  -> AreaFillKernel
mkAreaFillKernel fillMode primaryColor opacity config =
  AreaFillKernel
    { fillMode
    , primaryColor
    , secondaryColor: primaryColor { a = 0.0 }
    , gradientDirection: GradientVertical
    , opacity
    , seriesIndex: 0
    , secondSeriesIndex: 1
    , config
    }
