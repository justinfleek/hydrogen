-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // canvas
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas — The 2D void where everything exists.
-- |
-- | ## Design Philosophy
-- |
-- | The canvas is the universal substrate. It provides:
-- | - **Bounds**: Finite region where content exists
-- | - **Physics**: Device orientation mapped to world gravity
-- | - **Grid**: Cell subdivision for simulation
-- | - **Background**: What the void looks like
-- |
-- | ## Architectural Position
-- |
-- | Canvas is WHERE things exist. It defines the coordinate system and
-- | physics context. Surface defines WHAT things look like. Physics
-- | defines HOW things move. Spatial defines 3D structure.
-- |
-- | ## Paint Flow Model
-- |
-- | When device tilts:
-- | 1. Canvas/Physics converts orientation to gravity vector
-- | 2. Gravity direction is projected onto 2D canvas plane
-- | 3. Physics/Fluid runs simulation on Canvas/Grid cells
-- | 4. Surface/Height tracks paint pile depth
-- | 5. When height exceeds viscosity threshold, flow/topple triggers
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Canvas.Bounds
-- | - Hydrogen.Schema.Canvas.Physics
-- | - Hydrogen.Schema.Canvas.Grid
-- | - Hydrogen.Schema.Canvas.Background

module Hydrogen.Schema.Canvas
  ( -- * Re-exports from Bounds
    module Bounds
    
  -- * Re-exports from Physics
  , module Physics
  
  -- * Re-exports from Grid
  , module Grid
  
  -- * Re-exports from Background
  , module Background
  ) where

import Hydrogen.Schema.Canvas.Bounds
  ( CanvasBounds
  , mkCanvasBounds
  , boundsWidth
  , boundsHeight
  , boundsArea
  , boundsAspectRatio
  , boundsCenter
  , CoordinateSystem(ScreenCoords, CartesianCoords, NormalizedCoords)
  , allCoordinateSystems
  , isInBounds
  , clampToBounds
  , normalizePoint
  , denormalizePoint
  , bounds1080p
  , bounds4K
  , boundsSquare1K
  , boundsA4Portrait
  , boundsA4Landscape
  , subdivideIntoCells
  , cellAtPoint
  , cellCenter
  ) as Bounds

import Hydrogen.Schema.Canvas.Physics
  ( DeviceOrientation
  , mkDeviceOrientation
  , orientationAlpha
  , orientationBeta
  , orientationGamma
  , orientationFlat
  , orientationPortrait
  , orientationLandscapeLeft
  , orientationLandscapeRight
  , orientationUpsideDown
  , GravityVector
  , mkGravityVector
  , gravityX
  , gravityY
  , gravityZ
  , gravityMagnitude
  , gravity2D
  , orientationToGravity
  , projectGravityToCanvas
  , AccelerometerData
  , mkAccelerometerData
  , accelerometerToGravity
  , CanvasPhysics
  , mkCanvasPhysics
  , updateOrientation
  , updateAccelerometer
  , getGravityDirection
  , getGravity2D
  , gravityAngle
  , isGravitySignificant
  , gravityNormalized
  , displayOrientation
  , displayGravity
  , displayPhysics
  , orientationsEqual
  , gravitiesEqual
  , gravityWithinBand
  , gravityStrongerThan
  , GravityOrdering(GravityWeaker, GravityEqual, GravityStronger)
  , compareGravityStrength
  ) as Physics

import Hydrogen.Schema.Canvas.Grid
  ( GridConfig
  , mkGridConfig
  , gridCellsX
  , gridCellsY
  , gridTotalCells
  , CellIndex
  , mkCellIndex
  , cellX
  , cellY
  , cellToLinear
  , linearToCell
  , CanvasGrid
  , mkCanvasGrid
  , gridConfig
  , gridBounds
  , cellWidth
  , cellHeight
  , cellAtPosition
  , cellCenterPosition
  , cellBoundsMin
  , cellBoundsMax
  , positionInCell
  , cellNeighbors4
  , cellNeighbors8
  , cellsInRadius
  , isValidCell
  , allCellIndices
  , cellsInRow
  , cellsInColumn
  , cellsInRect
  , displayCellIndex
  , displayGridConfig
  , cellsEqual
  , isOnBoundary
  , isInterior
  , isWithinBounds
  , buildCellPath
  , BoundaryType(Corner, Edge, Interior)
  , cellBoundaryType
  ) as Grid

import Hydrogen.Schema.Canvas.Background
  ( BackgroundFill(FillSolid, FillGradient, FillPattern, FillTransparent)
  , allBackgroundFills
  , defaultFill
  , SolidBackground
  , mkSolidBackground
  , solidColor
  , GradientType(LinearGradient, RadialGradient, ConicGradient)
  , allGradientTypes
  , GradientStop
  , mkGradientStop
  , GradientBackground
  , mkGradientBackground
  , gradientType
  , gradientStops
  , gradientAngle
  , PatternType(CheckerPattern, GridPattern, DotsPattern, LinesPattern, CrosshatchPattern, NoisePattern)
  , allPatternTypes
  , PatternBackground
  , mkPatternBackground
  , patternType
  , patternScale
  , patternOpacity
  , PaperTexture(SmoothPaper, ColdPressPaper, RoughPaper, ToothPaper, CanvasPaper, VellumPaper)
  , allPaperTextures
  , PaperProperties
  , mkPaperProperties
  , paperTexture
  , paperTooth
  , paperAbsorption
  , paperTint
  , CanvasBackground
  , mkCanvasBackground
  , backgroundFill
  , backgroundPaper
  , whiteCanvas
  , creamCanvas
  , blackCanvas
  , transparentCanvas
  , coldPressWatercolor
  , hotPressWatercolor
  , roughSketch
  , displayBackgroundFill
  , displayPaperTexture
  , solidsEqual
  , isOpaque
  , isTransparent
  , blendColors
  , colorLuminance
  , isLightColor
  , isDarkColor
  , interpolateStops
  , scalePaperTooth
  , scalePaperAbsorption
  ) as Background
