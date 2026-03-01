-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // kernel // chart // lineplot
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Line Plot Kernel — Multi-Series Line Charts
-- |
-- | ## Purpose
-- |
-- | Multi-series line chart rendering for:
-- | - Time series data
-- | - Comparative analysis
-- | - Trend visualization
-- |
-- | ## Interpolation Styles
-- |
-- | - Solid/Dashed/Dotted line styles
-- | - Step functions (before/after)
-- | - Cardinal spline interpolation
-- | - Monotone cubic interpolation

module Hydrogen.GPU.Kernel.Chart.LinePlot
  ( -- * Types
    LinePlotKernel(LinePlotKernel)
  , LineStyle
      ( LineSolid
      , LineDashed
      , LineDotted
      , LineStepBefore
      , LineStepAfter
      , LineCardinal
      , LineMonotone
      )
  , SeriesConfig
  
  -- * Constructor
  , mkLinePlotKernel
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

import Data.Array as Array
import Data.Int as Int

import Hydrogen.GPU.Kernel.Chart.Types
  ( ChartColor
  , ChartKernelConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // line plot
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line interpolation style
data LineStyle
  = LineSolid              -- Solid line
  | LineDashed             -- Dashed line
  | LineDotted             -- Dotted line
  | LineStepBefore         -- Step function (value before point)
  | LineStepAfter          -- Step function (value after point)
  | LineCardinal           -- Cardinal spline interpolation
  | LineMonotone           -- Monotone cubic interpolation

derive instance eqLineStyle :: Eq LineStyle

instance showLineStyle :: Show LineStyle where
  show LineSolid = "LineSolid"
  show LineDashed = "LineDashed"
  show LineDotted = "LineDotted"
  show LineStepBefore = "LineStepBefore"
  show LineStepAfter = "LineStepAfter"
  show LineCardinal = "LineCardinal"
  show LineMonotone = "LineMonotone"

-- | Series configuration for multi-line plots
type SeriesConfig =
  { seriesId :: Int              -- Unique series identifier
  , label :: String              -- Series name
  , color :: ChartColor          -- Line color
  , lineStyle :: LineStyle       -- Line style
  , lineWidth :: Number          -- Line thickness
  , showPoints :: Boolean        -- Show data points
  , pointRadius :: Number        -- Data point size
  }

-- | Line plot kernel
newtype LinePlotKernel = LinePlotKernel
  { series :: Array SeriesConfig
  , dataPointCount :: Int        -- Points per series
  , xAxisMin :: Number           -- X-axis minimum
  , xAxisMax :: Number           -- X-axis maximum
  , yAxisMin :: Number           -- Y-axis minimum
  , yAxisMax :: Number           -- Y-axis maximum
  , antiAliasing :: Boolean
  , config :: ChartKernelConfig
  }

derive instance eqLinePlotKernel :: Eq LinePlotKernel

instance showLinePlotKernel :: Show LinePlotKernel where
  show (LinePlotKernel k) = 
    "(LinePlotKernel series:" <> show (Array.length k.series) <> 
    " points:" <> show k.dataPointCount <> ")"

-- | Create line plot kernel
mkLinePlotKernel 
  :: Array SeriesConfig 
  -> Int 
  -> ChartKernelConfig 
  -> LinePlotKernel
mkLinePlotKernel series dataPointCount config =
  LinePlotKernel
    { series
    , dataPointCount
    , xAxisMin: 0.0
    , xAxisMax: Int.toNumber dataPointCount
    , yAxisMin: 0.0
    , yAxisMax: 100.0
    , antiAliasing: true
    , config
    }
