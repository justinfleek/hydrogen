-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // kernel // chart // overlay
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chart Overlay Kernels — Threshold and Grid Overlays
-- |
-- | ## Purpose
-- |
-- | Overlay rendering for:
-- | - Threshold zones (medical alarm limits, trading bands)
-- | - Grid lines (measurement grids, calibration marks)
-- |
-- | ## Threshold Zones
-- |
-- | Color-coded regions indicating:
-- | - Normal: Safe operating range (green)
-- | - Warning: Attention needed (yellow)
-- | - Critical: Immediate attention (orange)
-- | - Danger: Emergency condition (red)
-- |
-- | ## Grid Styles
-- |
-- | - Lines: Solid grid lines
-- | - Dots: Dotted grid pattern
-- | - Dashes: Dashed grid lines

module Hydrogen.GPU.Kernel.Chart.Overlay
  ( -- * Threshold Types
    ThresholdOverlayKernel(ThresholdOverlayKernel)
  , ThresholdZone
  , ThresholdSeverity
      ( SeverityNormal
      , SeverityWarning
      , SeverityCritical
      , SeverityDanger
      )
  
  -- * Grid Types
  , GridOverlayKernel(GridOverlayKernel)
  , GridStyle
      ( GridLines
      , GridDots
      , GridDashes
      )
  , GridDivisions
  
  -- * Constructors
  , mkThresholdOverlayKernel
  , mkGridOverlayKernel
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

import Hydrogen.GPU.Kernel.Chart.Types
  ( ChartColor
  , ChartKernelConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // threshold overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Threshold severity level
data ThresholdSeverity
  = SeverityNormal         -- Normal range (green)
  | SeverityWarning        -- Warning range (yellow)
  | SeverityCritical       -- Critical range (orange)
  | SeverityDanger         -- Danger range (red)

derive instance eqThresholdSeverity :: Eq ThresholdSeverity

instance showThresholdSeverity :: Show ThresholdSeverity where
  show SeverityNormal = "SeverityNormal"
  show SeverityWarning = "SeverityWarning"
  show SeverityCritical = "SeverityCritical"
  show SeverityDanger = "SeverityDanger"

-- | Threshold zone definition
type ThresholdZone =
  { minValue :: Number           -- Zone minimum
  , maxValue :: Number           -- Zone maximum
  , severity :: ThresholdSeverity
  , color :: ChartColor          -- Override color (or use severity default)
  , label :: String              -- Zone label
  , showLabel :: Boolean         -- Display label
  }

-- | Threshold overlay kernel
newtype ThresholdOverlayKernel = ThresholdOverlayKernel
  { zones :: Array ThresholdZone
  , fillOpacity :: Number        -- Zone fill opacity
  , showBorders :: Boolean       -- Show zone borders
  , borderWidth :: Number        -- Border line width
  , animated :: Boolean          -- Animate zone transitions
  , pulseOnViolation :: Boolean  -- Pulse when value in danger zone
  , config :: ChartKernelConfig
  }

derive instance eqThresholdOverlayKernel :: Eq ThresholdOverlayKernel

instance showThresholdOverlayKernel :: Show ThresholdOverlayKernel where
  show (ThresholdOverlayKernel k) = 
    "(ThresholdOverlayKernel zones:" <> show (Array.length k.zones) <> ")"

-- | Create threshold overlay kernel
mkThresholdOverlayKernel 
  :: Array ThresholdZone 
  -> Number 
  -> ChartKernelConfig 
  -> ThresholdOverlayKernel
mkThresholdOverlayKernel zones fillOpacity config =
  ThresholdOverlayKernel
    { zones
    , fillOpacity
    , showBorders: true
    , borderWidth: 1.0
    , animated: false
    , pulseOnViolation: false
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // grid overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid line style
data GridStyle
  = GridLines              -- Solid lines
  | GridDots               -- Dotted lines
  | GridDashes             -- Dashed lines

derive instance eqGridStyle :: Eq GridStyle

instance showGridStyle :: Show GridStyle where
  show GridLines = "GridLines"
  show GridDots = "GridDots"
  show GridDashes = "GridDashes"

-- | Grid divisions
type GridDivisions =
  { majorX :: Int                -- Major divisions on X axis
  , majorY :: Int                -- Major divisions on Y axis
  , minorX :: Int                -- Minor divisions between major X
  , minorY :: Int                -- Minor divisions between major Y
  }

-- | Grid overlay kernel
newtype GridOverlayKernel = GridOverlayKernel
  { style :: GridStyle
  , divisions :: GridDivisions
  , majorColor :: ChartColor
  , minorColor :: ChartColor
  , majorWidth :: Number         -- Major line width
  , minorWidth :: Number         -- Minor line width
  , showLabels :: Boolean        -- Show axis labels
  , labelColor :: ChartColor
  , config :: ChartKernelConfig
  }

derive instance eqGridOverlayKernel :: Eq GridOverlayKernel

instance showGridOverlayKernel :: Show GridOverlayKernel where
  show (GridOverlayKernel k) = 
    "(GridOverlayKernel style:" <> show k.style <> ")"

-- | Create grid overlay kernel
mkGridOverlayKernel 
  :: GridStyle 
  -> GridDivisions 
  -> ChartKernelConfig 
  -> GridOverlayKernel
mkGridOverlayKernel style divisions config =
  GridOverlayKernel
    { style
    , divisions
    , majorColor: { r: 0.5, g: 0.5, b: 0.5, a: 0.5 }
    , minorColor: { r: 0.3, g: 0.3, b: 0.3, a: 0.3 }
    , majorWidth: 1.0
    , minorWidth: 0.5
    , showLabels: true
    , labelColor: { r: 0.7, g: 0.7, b: 0.7, a: 1.0 }
    , config
    }
