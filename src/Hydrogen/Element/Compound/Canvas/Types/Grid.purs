-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // canvas // types // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Grid Types — Grid rendering and snap behavior.
-- |
-- | ## Scope
-- |
-- | This module defines types for canvas grid and snapping:
-- |
-- | - **GridStyle**: Visual appearance of grid (dots, lines, isometric, etc.)
-- | - **GridConfig**: Complete grid configuration
-- | - **SnapTarget**: What to snap to (grid, objects, guides)
-- | - **SnapConfig**: Complete snap configuration
-- |
-- | ## Grid Rendering
-- |
-- | Grids support multiple visual styles and can show major/minor divisions.
-- | Grid visibility is independent of snap behavior.
-- |
-- | ## Snap Behavior
-- |
-- | Snapping provides alignment assistance during object manipulation.
-- | Multiple snap targets can be active simultaneously.

module Hydrogen.Element.Compound.Canvas.Types.Grid
  ( -- * Grid Types
    GridStyle
    ( GridDots
    , GridLines
    , GridCrosshairs
    , GridIsometric
    , GridPerspective
    )
  , GridConfig
  , defaultGridConfig
  , gridEnabled
  , gridVisible
  , gridSnap
  , withGridSize
  , withGridStyle
  , withGridColor
  , withGridOpacity
  
  -- * Snap Types
  , SnapTarget
    ( SnapGrid
    , SnapObjects
    , SnapGuides
    , SnapPixels
    , SnapKeyObjects
    )
  , SnapConfig
  , defaultSnapConfig
  , snapEnabled
  , snapDistance
  , snapToGrid
  , snapToObjects
  , snapToGuides
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (&&)
  , max
  , min
  )

import Data.Array (elem)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // grid types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual style for the canvas grid.
data GridStyle
  = GridDots          -- ^ Dots at intersections
  | GridLines         -- ^ Full grid lines
  | GridCrosshairs    -- ^ Small crosses at intersections
  | GridIsometric     -- ^ 30° isometric grid
  | GridPerspective   -- ^ Perspective grid with vanishing point

derive instance eqGridStyle :: Eq GridStyle

instance showGridStyle :: Show GridStyle where
  show GridDots = "dots"
  show GridLines = "lines"
  show GridCrosshairs = "crosshairs"
  show GridIsometric = "isometric"
  show GridPerspective = "perspective"

-- | Grid configuration.
type GridConfig =
  { enabled :: Boolean
  , visible :: Boolean
  , snap :: Boolean
  , size :: Number              -- Grid cell size in canvas units
  , subdivisions :: Int         -- Subdivisions per cell
  , style :: GridStyle
  , majorColor :: String        -- Color for major grid lines (hex)
  , minorColor :: String        -- Color for minor grid lines (hex)
  , majorOpacity :: Number      -- 0.0 - 1.0
  , minorOpacity :: Number      -- 0.0 - 1.0
  , majorWidth :: Number        -- Stroke width for major lines
  , minorWidth :: Number        -- Stroke width for minor lines
  }

-- | Default grid configuration.
defaultGridConfig :: GridConfig
defaultGridConfig =
  { enabled: true
  , visible: true
  , snap: true
  , size: 10.0
  , subdivisions: 4
  , style: GridLines
  , majorColor: "#3b82f6"       -- Blue-500
  , minorColor: "#94a3b8"       -- Slate-400
  , majorOpacity: 0.3
  , minorOpacity: 0.1
  , majorWidth: 1.0
  , minorWidth: 0.5
  }

-- | Check if grid is enabled.
gridEnabled :: GridConfig -> Boolean
gridEnabled config = config.enabled

-- | Check if grid is visible.
gridVisible :: GridConfig -> Boolean
gridVisible config = config.enabled && config.visible

-- | Check if snap to grid is active.
gridSnap :: GridConfig -> Boolean
gridSnap config = config.enabled && config.snap

-- | Set grid size.
withGridSize :: Number -> GridConfig -> GridConfig
withGridSize size config = config { size = size }

-- | Set grid style.
withGridStyle :: GridStyle -> GridConfig -> GridConfig
withGridStyle style config = config { style = style }

-- | Set grid color.
withGridColor :: String -> GridConfig -> GridConfig
withGridColor color config = config { majorColor = color }

-- | Set grid opacity.
withGridOpacity :: Number -> GridConfig -> GridConfig
withGridOpacity opacity config = config { majorOpacity = clamp01 opacity }
  where
    clamp01 :: Number -> Number
    clamp01 n = max 0.0 (min 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // snap types
-- ═════════════════════════════════════════════════════════════════════════════

-- | What objects/features to snap to.
data SnapTarget
  = SnapGrid            -- ^ Snap to grid intersections
  | SnapObjects         -- ^ Snap to object bounds/centers
  | SnapGuides          -- ^ Snap to guides
  | SnapPixels          -- ^ Snap to whole pixels
  | SnapKeyObjects      -- ^ Snap to "key" objects (selection centers, etc.)

derive instance eqSnapTarget :: Eq SnapTarget

instance showSnapTarget :: Show SnapTarget where
  show SnapGrid = "grid"
  show SnapObjects = "objects"
  show SnapGuides = "guides"
  show SnapPixels = "pixels"
  show SnapKeyObjects = "key-objects"

-- | Snap configuration.
type SnapConfig =
  { enabled :: Boolean
  , distance :: Number          -- Snap threshold in screen pixels
  , targets :: Array SnapTarget -- What to snap to
  , showIndicators :: Boolean   -- Show snap lines/points
  , indicatorColor :: String    -- Color for snap indicators
  }

-- | Default snap configuration.
defaultSnapConfig :: SnapConfig
defaultSnapConfig =
  { enabled: true
  , distance: 8.0
  , targets: [SnapGrid, SnapObjects, SnapGuides]
  , showIndicators: true
  , indicatorColor: "#f97316"   -- Orange-500
  }

-- | Check if snap is enabled.
snapEnabled :: SnapConfig -> Boolean
snapEnabled config = config.enabled

-- | Get snap distance.
snapDistance :: SnapConfig -> Number
snapDistance config = config.distance

-- | Check if snapping to grid.
snapToGrid :: SnapConfig -> Boolean
snapToGrid config = config.enabled && elem SnapGrid config.targets

-- | Check if snapping to objects.
snapToObjects :: SnapConfig -> Boolean
snapToObjects config = config.enabled && elem SnapObjects config.targets

-- | Check if snapping to guides.
snapToGuides :: SnapConfig -> Boolean
snapToGuides config = config.enabled && elem SnapGuides config.targets
