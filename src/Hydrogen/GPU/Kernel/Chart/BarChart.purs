-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // kernel // chart // barchart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bar Chart Kernel — Categorical Data Visualization
-- |
-- | ## Purpose
-- |
-- | Bar chart rendering for:
-- | - Category comparisons
-- | - Distribution visualization
-- | - Spectrum analyzers
-- |
-- | ## Orientations
-- |
-- | - Vertical: Standard bar chart
-- | - Horizontal: Rotated bar chart
-- |
-- | ## Grouping Modes
-- |
-- | - Stacked: Bars stacked on top of each other
-- | - Grouped: Bars side by side
-- | - Overlapped: Semi-transparent overlap

module Hydrogen.GPU.Kernel.Chart.BarChart
  ( -- * Types
    BarChartKernel(BarChartKernel)
  , BarOrientation
      ( BarVertical
      , BarHorizontal
      )
  , BarGrouping
      ( BarStacked
      , BarGrouped
      , BarOverlapped
      )
  
  -- * Constructor
  , mkBarChartKernel
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
--                                                                  // bar chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bar orientation
data BarOrientation
  = BarVertical            -- Vertical bars
  | BarHorizontal          -- Horizontal bars

derive instance eqBarOrientation :: Eq BarOrientation

instance showBarOrientation :: Show BarOrientation where
  show BarVertical = "BarVertical"
  show BarHorizontal = "BarHorizontal"

-- | Bar grouping mode
data BarGrouping
  = BarStacked             -- Stacked bars
  | BarGrouped             -- Grouped side-by-side
  | BarOverlapped          -- Overlapping with transparency

derive instance eqBarGrouping :: Eq BarGrouping

instance showBarGrouping :: Show BarGrouping where
  show BarStacked = "BarStacked"
  show BarGrouped = "BarGrouped"
  show BarOverlapped = "BarOverlapped"

-- | Bar chart kernel
newtype BarChartKernel = BarChartKernel
  { orientation :: BarOrientation
  , grouping :: BarGrouping
  , barColors :: Array ChartColor
  , barWidth :: Number           -- Width as fraction of available space
  , barSpacing :: Number         -- Space between bars
  , cornerRadius :: Number       -- Rounded corners
  , showValues :: Boolean        -- Show value labels
  , categoryCount :: Int         -- Number of categories
  , seriesCount :: Int           -- Number of series
  , config :: ChartKernelConfig
  }

derive instance eqBarChartKernel :: Eq BarChartKernel

instance showBarChartKernel :: Show BarChartKernel where
  show (BarChartKernel k) = 
    "(BarChartKernel orientation:" <> show k.orientation <> 
    " grouping:" <> show k.grouping <> ")"

-- | Create bar chart kernel
mkBarChartKernel 
  :: BarOrientation 
  -> BarGrouping 
  -> Array ChartColor 
  -> Int 
  -> Int 
  -> ChartKernelConfig 
  -> BarChartKernel
mkBarChartKernel orientation grouping barColors categoryCount seriesCount config =
  BarChartKernel
    { orientation
    , grouping
    , barColors
    , barWidth: 0.8
    , barSpacing: 0.1
    , cornerRadius: 0.0
    , showValues: false
    , categoryCount
    , seriesCount
    , config
    }
