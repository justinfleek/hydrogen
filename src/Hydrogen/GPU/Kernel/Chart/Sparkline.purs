-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // gpu // kernel // chart // sparkline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sparkline Kernel — Inline Mini Charts
-- |
-- | ## Purpose
-- |
-- | Compact inline charts for:
-- | - Dashboard KPI indicators
-- | - Table cell trends
-- | - Inline data visualization
-- |
-- | ## Display Styles
-- |
-- | - Line: Simple trend line
-- | - Area: Filled area chart
-- | - Bar: Mini bar chart
-- | - WinLoss: Binary up/down indicators

module Hydrogen.GPU.Kernel.Chart.Sparkline
  ( -- * Types
    SparklineKernel(SparklineKernel)
  , SparklineStyle
      ( SparklineLine
      , SparklineArea
      , SparklineBar
      , SparklineWinLoss
      )
  , SparklineConfig
  
  -- * Constructor
  , mkSparklineKernel
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
--                                                                  // sparkline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sparkline display style
data SparklineStyle
  = SparklineLine          -- Simple line chart
  | SparklineArea          -- Filled area chart
  | SparklineBar           -- Mini bar chart
  | SparklineWinLoss       -- Binary up/down bars

derive instance eqSparklineStyle :: Eq SparklineStyle

instance showSparklineStyle :: Show SparklineStyle where
  show SparklineLine = "SparklineLine"
  show SparklineArea = "SparklineArea"
  show SparklineBar = "SparklineBar"
  show SparklineWinLoss = "SparklineWinLoss"

-- | Sparkline configuration
type SparklineConfig =
  { dataPoints :: Int            -- Number of data points
  , showMinMax :: Boolean        -- Highlight min/max points
  , showLast :: Boolean          -- Highlight last point
  , normalizeRange :: Boolean    -- Auto-scale to data range
  }

-- | Sparkline kernel
newtype SparklineKernel = SparklineKernel
  { style :: SparklineStyle
  , sparklineConfig :: SparklineConfig
  , lineColor :: ChartColor
  , fillColor :: ChartColor
  , minColor :: ChartColor       -- Color for minimum point
  , maxColor :: ChartColor       -- Color for maximum point
  , lastColor :: ChartColor      -- Color for last point
  , config :: ChartKernelConfig
  }

derive instance eqSparklineKernel :: Eq SparklineKernel

instance showSparklineKernel :: Show SparklineKernel where
  show (SparklineKernel k) = 
    "(SparklineKernel style:" <> show k.style <> 
    " points:" <> show k.sparklineConfig.dataPoints <> ")"

-- | Create sparkline kernel
mkSparklineKernel 
  :: SparklineStyle 
  -> SparklineConfig 
  -> ChartColor 
  -> ChartKernelConfig 
  -> SparklineKernel
mkSparklineKernel style sparklineConfig lineColor config =
  SparklineKernel
    { style
    , sparklineConfig
    , lineColor
    , fillColor: lineColor { a = 0.3 }
    , minColor: { r: 1.0, g: 0.0, b: 0.0, a: 1.0 }
    , maxColor: { r: 0.0, g: 1.0, b: 0.0, a: 1.0 }
    , lastColor: { r: 0.0, g: 0.5, b: 1.0, a: 1.0 }
    , config
    }
