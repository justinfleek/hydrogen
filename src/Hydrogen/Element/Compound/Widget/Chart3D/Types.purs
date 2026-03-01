-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // chart3d // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for 3D Chart widgets.
-- |
-- | Defines data structures and configurations for isometric 3D charts.

module Hydrogen.Element.Compound.Widget.Chart3D.Types
  ( -- * 2D Point
    Point2D
    
  -- * 3D Bar Chart Types
  , Bar3DData
  , Bar3DConfig
  , defaultBar3DConfig
  
  -- * 3D Surface Chart Types
  , SurfaceData
  , SurfaceConfig
  , defaultSurfaceConfig
  
  -- * Color Palette
  , defaultBar3DColors
  ) where

import Data.Maybe (Maybe(Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // point2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D point result from isometric projection.
type Point2D = { x :: Number, y :: Number }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // 3d bar types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Data point for 3D bar chart.
type Bar3DData =
  { label :: String
  , value :: Number
  , color :: Maybe String
  }

-- | Configuration for 3D bar chart.
type Bar3DConfig =
  { title :: Maybe String
  , subtitle :: Maybe String
  , width :: Number
  , height :: Number
  , barWidth :: Number
  , barDepth :: Number
  , barSpacing :: Number
  , maxBarHeight :: Number
  , showLabels :: Boolean
  , showValues :: Boolean
  , className :: String
  }

-- | Default configuration for 3D bar chart.
defaultBar3DConfig :: Bar3DConfig
defaultBar3DConfig =
  { title: Nothing
  , subtitle: Nothing
  , width: 500.0
  , height: 400.0
  , barWidth: 40.0
  , barDepth: 25.0
  , barSpacing: 70.0
  , maxBarHeight: 200.0
  , showLabels: true
  , showValues: true
  , className: ""
  }

-- | Default color palette for 3D bars.
defaultBar3DColors :: Array String
defaultBar3DColors =
  [ "#f97316"  -- Orange
  , "#3b82f6"  -- Blue
  , "#10b981"  -- Emerald
  , "#8b5cf6"  -- Violet
  , "#f43f5e"  -- Rose
  , "#fbbf24"  -- Amber
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // 3d surface types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Data for 3D surface chart.
-- |
-- | Provided as a 2D grid of height values (row-major order).
-- | Each value represents the Z-height at that (x, y) grid position.
type SurfaceData =
  { rows :: Int
  , cols :: Int
  , values :: Array Number
  }

-- | Configuration for 3D surface chart.
type SurfaceConfig =
  { title :: Maybe String
  , subtitle :: Maybe String
  , width :: Number
  , height :: Number
  , cellSize :: Number
  , maxHeight :: Number
  , colorMin :: String
  , colorMax :: String
  , showGrid :: Boolean
  , className :: String
  }

-- | Default configuration for 3D surface chart.
defaultSurfaceConfig :: SurfaceConfig
defaultSurfaceConfig =
  { title: Nothing
  , subtitle: Nothing
  , width: 500.0
  , height: 400.0
  , cellSize: 30.0
  , maxHeight: 100.0
  , colorMin: "#3b82f6"   -- Blue (low values)
  , colorMax: "#ef4444"   -- Red (high values)
  , showGrid: true
  , className: ""
  }
