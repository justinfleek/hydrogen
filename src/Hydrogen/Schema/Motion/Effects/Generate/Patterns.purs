-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // effects // generate // patterns
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pattern Effects — procedural pattern generation effects.
-- |
-- | ## Industry Standard
-- |
-- | Implements AE's pattern effects:
-- |
-- | - **Cell Pattern**: Procedural cellular textures
-- | - **Checkerboard**: Checkerboard pattern
-- | - **Grid**: Lines/rectangles grid pattern
-- | - **Fractal**: Fractal noise pattern
-- |
-- | ## GPU Shader Pattern
-- |
-- | Pattern effects are fully procedural, ideal for GPU shaders.

module Hydrogen.Schema.Motion.Effects.Generate.Patterns
  ( -- * Cell Pattern
    CellPatternEffect
  , CellType(CTBubbles, CTPipes, CTCrystals, CTMixed, CTPlates, CTSoft)
  , defaultCellPattern
  , cellPatternWithType
  
  -- * Checkerboard
  , CheckerboardEffect
  , defaultCheckerboard
  , checkerboardWithSize
  
  -- * Grid
  , GridEffect
  , GridType(GTLines, GTRectangles)
  , defaultGrid
  , gridWithSize
  
  -- * Fractal
  , FractalEffect
  , FractalNoiseType(FNTBasic, FNTTurbulentSmooth, FNTTurbulentSharp, FNTDynamic, FNTDynamicTwist, FNTSplineTurbulence)
  , defaultFractal
  , fractalWithComplexity
  
  -- * Serialization
  , cellTypeToString
  , gridTypeToString
  , fractalNoiseTypeToString
  
  -- * Utilities
  , describeCellPattern
  , describeGrid
  , describeFractal
  , cellPatternEffectName
  , checkerboardEffectName
  , gridEffectName
  , fractalEffectName
  , isCellPatternInverted
  , isFractalInverted
  , combineCellEvolution
  , combineFractalEvolution
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (+)
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Dimension.Point2D (Point2D, origin, point2D)
import Hydrogen.Schema.Motion.Composition (BlendMode(BMNormal))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cell // pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cell type — pattern generated.
data CellType
  = CTBubbles          -- ^ Circular cells
  | CTPipes            -- ^ Connected pipe-like cells
  | CTCrystals         -- ^ Angular crystal-like cells
  | CTMixed            -- ^ Mix of cell types
  | CTPlates           -- ^ Flat plate-like cells
  | CTSoft             -- ^ Soft-edged cells

derive instance eqCellType :: Eq CellType
derive instance ordCellType :: Ord CellType

instance showCellType :: Show CellType where
  show CTBubbles = "bubbles"
  show CTPipes = "pipes"
  show CTCrystals = "crystals"
  show CTMixed = "mixed"
  show CTPlates = "plates"
  show CTSoft = "soft"

-- | Cell Pattern Effect — procedural cellular texture.
-- |
-- | ## AE Properties
-- |
-- | - Cell Type: Visual style of cells
-- | - Size: Cell size in pixels
-- | - Offset: Pattern offset for animation
-- | - Evolution: Animate the pattern over time
-- | - Contrast: Cell edge contrast
type CellPatternEffect =
  { cellType :: CellType         -- ^ Type of cell pattern
  , size :: Number               -- ^ Cell size (1-1000)
  , offset :: Point2D            -- ^ Pattern offset
  , evolution :: Number          -- ^ Evolution (0-360 degrees, animatable)
  , contrast :: Number           -- ^ Edge contrast (0-100)
  , randomSeed :: Int            -- ^ Random seed for reproducibility
  , invert :: Boolean            -- ^ Invert output
  }

-- | Default cell pattern: bubbles, size 50.
defaultCellPattern :: CellPatternEffect
defaultCellPattern =
  { cellType: CTBubbles
  , size: 50.0
  , offset: origin
  , evolution: 0.0
  , contrast: 100.0
  , randomSeed: 0
  , invert: false
  }

-- | Create cell pattern with specific type.
cellPatternWithType :: CellType -> Number -> CellPatternEffect
cellPatternWithType ct sz =
  { cellType: ct
  , size: clampNumber 1.0 1000.0 sz
  , offset: origin
  , evolution: 0.0
  , contrast: 100.0
  , randomSeed: 0
  , invert: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // checkerboard
-- ═════════════════════════════════════════════════════════════════════════════

-- | Checkerboard Effect — alternating square pattern.
-- |
-- | ## AE Properties
-- |
-- | - Anchor: Pattern anchor point
-- | - Size: Square size (width, height)
-- | - Feather: Edge softness
-- | - Color: Checker color (alternates with transparent)
-- | - Opacity: Overall opacity
-- | - Blend Mode: How to composite with original
type CheckerboardEffect =
  { anchor :: Point2D            -- ^ Pattern anchor
  , size :: { width :: Number, height :: Number }  -- ^ Square size (1-1000 each)
  , feather :: Number            -- ^ Edge feather (0-100)
  , color :: RGB                 -- ^ Checker color
  , opacity :: Number            -- ^ Opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default checkerboard: 100x100, black.
defaultCheckerboard :: CheckerboardEffect
defaultCheckerboard =
  { anchor: origin
  , size: { width: 100.0, height: 100.0 }
  , feather: 0.0
  , color: rgb 0 0 0
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- | Create checkerboard with specific size.
checkerboardWithSize :: Number -> Number -> RGB -> CheckerboardEffect
checkerboardWithSize w h col =
  { anchor: origin
  , size: { width: clampNumber 1.0 1000.0 w, height: clampNumber 1.0 1000.0 h }
  , feather: 0.0
  , color: col
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid type — line or rectangle grid.
data GridType
  = GTLines           -- ^ Lines only
  | GTRectangles      -- ^ Filled rectangles

derive instance eqGridType :: Eq GridType
derive instance ordGridType :: Ord GridType

instance showGridType :: Show GridType where
  show GTLines = "lines"
  show GTRectangles = "rectangles"

-- | Grid Effect — regular grid pattern.
-- |
-- | ## AE Properties
-- |
-- | - Anchor: Grid anchor point
-- | - Corner: Grid corner (defines size)
-- | - Border: Line thickness (for lines mode)
-- | - Feather: Edge softness
-- | - Color/Opacity: Grid appearance
type GridEffect =
  { anchor :: Point2D            -- ^ Grid anchor
  , corner :: Point2D            -- ^ Grid corner (defines cell size)
  , gridType :: GridType         -- ^ Lines or rectangles
  , border :: Number             -- ^ Line thickness (0-100)
  , feather :: Number            -- ^ Edge feather (0-100)
  , color :: RGB                 -- ^ Grid color
  , opacity :: Number            -- ^ Opacity (0-100)
  , blendMode :: BlendMode       -- ^ Compositing mode
  }

-- | Default grid: 100x100 cells, 1px lines, white.
defaultGrid :: GridEffect
defaultGrid =
  { anchor: origin
  , corner: point2D 100.0 100.0
  , gridType: GTLines
  , border: 1.0
  , feather: 0.0
  , color: rgb 255 255 255
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- | Create grid with specific cell size.
gridWithSize :: Number -> Number -> RGB -> GridEffect
gridWithSize w h col =
  { anchor: origin
  , corner: point2D (clampNumber 1.0 10000.0 w) (clampNumber 1.0 10000.0 h)
  , gridType: GTLines
  , border: 1.0
  , feather: 0.0
  , color: col
  , opacity: 100.0
  , blendMode: BMNormal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // fractal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fractal noise type — algorithm used.
data FractalNoiseType
  = FNTBasic           -- ^ Basic noise
  | FNTTurbulentSmooth -- ^ Turbulent smooth
  | FNTTurbulentSharp  -- ^ Turbulent sharp
  | FNTDynamic         -- ^ Dynamic (evolving)
  | FNTDynamicTwist    -- ^ Dynamic twist
  | FNTSplineTurbulence -- ^ Spline-based

derive instance eqFractalNoiseType :: Eq FractalNoiseType
derive instance ordFractalNoiseType :: Ord FractalNoiseType

instance showFractalNoiseType :: Show FractalNoiseType where
  show FNTBasic = "basic"
  show FNTTurbulentSmooth = "turbulent-smooth"
  show FNTTurbulentSharp = "turbulent-sharp"
  show FNTDynamic = "dynamic"
  show FNTDynamicTwist = "dynamic-twist"
  show FNTSplineTurbulence = "spline-turbulence"

-- | Fractal Effect — procedural fractal noise.
-- |
-- | ## AE Properties
-- |
-- | - Fractal Type: Algorithm type
-- | - Contrast/Brightness: Output adjustment
-- | - Overflow: How to handle values > 1
-- | - Transform: Scale, offset, rotation
-- | - Complexity: Number of octaves
-- | - Evolution: Animation parameter
type FractalEffect =
  { fractalType :: FractalNoiseType  -- ^ Noise algorithm
  , contrast :: Number           -- ^ Output contrast (-200 to 200)
  , brightness :: Number         -- ^ Output brightness (-200 to 200)
  , scale :: Number              -- ^ Pattern scale (1-10000 %)
  , uniformScaling :: Boolean    -- ^ Lock X/Y scale
  , offset :: Point2D            -- ^ Pattern offset
  , rotation :: Number           -- ^ Pattern rotation (0-360)
  , complexity :: Number         -- ^ Octave count (1-20)
  , subInfluence :: Number       -- ^ Sub-octave influence (0-100)
  , evolution :: Number          -- ^ Evolution (0-360, animatable)
  , cycleEvolution :: Boolean    -- ^ Cycle evolution
  , randomSeed :: Int            -- ^ Random seed
  , invert :: Boolean            -- ^ Invert output
  }

-- | Default fractal: basic, medium complexity.
defaultFractal :: FractalEffect
defaultFractal =
  { fractalType: FNTBasic
  , contrast: 100.0
  , brightness: 0.0
  , scale: 100.0
  , uniformScaling: true
  , offset: origin
  , rotation: 0.0
  , complexity: 6.0
  , subInfluence: 70.0
  , evolution: 0.0
  , cycleEvolution: false
  , randomSeed: 0
  , invert: false
  }

-- | Create fractal with specific complexity.
fractalWithComplexity :: FractalNoiseType -> Number -> FractalEffect
fractalWithComplexity ft cmplx =
  { fractalType: ft
  , contrast: 100.0
  , brightness: 0.0
  , scale: 100.0
  , uniformScaling: true
  , offset: origin
  , rotation: 0.0
  , complexity: clampNumber 1.0 20.0 cmplx
  , subInfluence: 70.0
  , evolution: 0.0
  , cycleEvolution: false
  , randomSeed: 0
  , invert: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert CellType to string for serialization.
cellTypeToString :: CellType -> String
cellTypeToString ct = show ct

-- | Convert GridType to string for serialization.
gridTypeToString :: GridType -> String
gridTypeToString gt = show gt

-- | Convert FractalNoiseType to string for serialization.
fractalNoiseTypeToString :: FractalNoiseType -> String
fractalNoiseTypeToString fnt = show fnt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create cell pattern effect description.
describeCellPattern :: CellPatternEffect -> String
describeCellPattern e = 
  "CellPattern(" <> show e.cellType <> ", size: " <> show e.size <> ")"

-- | Create grid effect description.
describeGrid :: GridEffect -> String
describeGrid e = 
  "Grid(" <> show e.gridType <> ", border: " <> show e.border <> ")"

-- | Create fractal effect description.
describeFractal :: FractalEffect -> String
describeFractal e = 
  "Fractal(" <> show e.fractalType <> ", complexity: " <> show e.complexity <> ")"

-- | Create composite effect name from cell pattern.
cellPatternEffectName :: CellPatternEffect -> String
cellPatternEffectName _ = "Cell Pattern"

-- | Create composite effect name from checkerboard.
checkerboardEffectName :: CheckerboardEffect -> String
checkerboardEffectName _ = "Checkerboard"

-- | Create composite effect name from grid.
gridEffectName :: GridEffect -> String
gridEffectName _ = "Grid"

-- | Create composite effect name from fractal.
fractalEffectName :: FractalEffect -> String
fractalEffectName _ = "Fractal"

-- | Check if cell pattern is inverted.
isCellPatternInverted :: CellPatternEffect -> Boolean
isCellPatternInverted e = e.invert

-- | Check if fractal is inverted.
isFractalInverted :: FractalEffect -> Boolean
isFractalInverted e = e.invert

-- | Combine cell pattern evolution values.
combineCellEvolution :: CellPatternEffect -> CellPatternEffect -> Number
combineCellEvolution e1 e2 = clampNumber 0.0 360.0 (e1.evolution + e2.evolution)

-- | Combine fractal evolution values.
combineFractalEvolution :: FractalEffect -> FractalEffect -> Number
combineFractalEvolution e1 e2 = clampNumber 0.0 360.0 (e1.evolution + e2.evolution)
