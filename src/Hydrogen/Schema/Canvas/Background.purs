-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // canvas // background
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Background — What the void looks like.
-- |
-- | ## Design Philosophy
-- |
-- | The background is the substrate everything is painted on.
-- | It can be a solid color, gradient, pattern, or texture.
-- | It responds to light and shadow from paint above it.
-- |
-- | ## Background Types
-- |
-- | - **Solid**: Single color fill
-- | - **Gradient**: Linear or radial color transitions
-- | - **Pattern**: Repeating tile patterns (paper texture, etc.)
-- | - **Transparent**: Alpha channel for compositing
-- |
-- | ## Paper Simulation
-- |
-- | For painting applications, the background simulates paper:
-- | - Texture affects paint absorption
-- | - Tooth affects brush stroke texture
-- | - Color affects wet paint blending
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Maybe

module Hydrogen.Schema.Canvas.Background
  ( -- * Background Fill
    BackgroundFill(..)
  , allBackgroundFills
  , defaultFill
  
  -- * Solid Color
  , SolidBackground
  , mkSolidBackground
  , solidColor
  
  -- * Gradient
  , GradientType(..)
  , allGradientTypes
  , GradientStop
  , mkGradientStop
  , GradientBackground
  , mkGradientBackground
  , gradientType
  , gradientStops
  , gradientAngle
  
  -- * Pattern
  , PatternType(..)
  , allPatternTypes
  , PatternBackground
  , mkPatternBackground
  , patternType
  , patternScale
  , patternOpacity
  
  -- * Paper Properties
  , PaperTexture(..)
  , allPaperTextures
  , PaperProperties
  , mkPaperProperties
  , paperTexture
  , paperTooth
  , paperAbsorption
  , paperTint
  
  -- * Canvas Background
  , CanvasBackground
  , mkCanvasBackground
  , backgroundFill
  , backgroundPaper
  
  -- * Presets
  , whiteCanvas
  , creamCanvas
  , blackCanvas
  , transparentCanvas
  , coldPressWatercolor
  , hotPressWatercolor
  , roughSketch
  
  -- * Display
  , displayBackgroundFill
  , displayPaperTexture
  
  -- * Color Utilities
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
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (&&)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , max
  , min
  , otherwise
  )

import Data.Maybe (Maybe(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // background fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of background fill.
data BackgroundFill
  = FillSolid
  | FillGradient
  | FillPattern
  | FillTransparent

derive instance eqBackgroundFill :: Eq BackgroundFill
derive instance ordBackgroundFill :: Ord BackgroundFill

instance showBackgroundFill :: Show BackgroundFill where
  show FillSolid = "solid"
  show FillGradient = "gradient"
  show FillPattern = "pattern"
  show FillTransparent = "transparent"

-- | All background fill types.
allBackgroundFills :: Array BackgroundFill
allBackgroundFills = [FillSolid, FillGradient, FillPattern, FillTransparent]

-- | Default fill is solid white.
defaultFill :: BackgroundFill
defaultFill = FillSolid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // solid color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Solid color background.
-- |
-- | RGBA values in 0-1 range.
type SolidBackground =
  { r :: Number    -- ^ Red (0-1)
  , g :: Number    -- ^ Green (0-1)
  , b :: Number    -- ^ Blue (0-1)
  , a :: Number    -- ^ Alpha (0-1)
  }

-- | Create solid background with clamped values.
mkSolidBackground :: Number -> Number -> Number -> Number -> SolidBackground
mkSolidBackground r g b a =
  { r: clamp01 r
  , g: clamp01 g
  , b: clamp01 b
  , a: clamp01 a
  }

-- | Get solid color as RGBA record.
solidColor :: SolidBackground -> { r :: Number, g :: Number, b :: Number, a :: Number }
solidColor bg = bg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // gradient
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of gradient.
data GradientType
  = LinearGradient
  | RadialGradient
  | ConicGradient

derive instance eqGradientType :: Eq GradientType
derive instance ordGradientType :: Ord GradientType

instance showGradientType :: Show GradientType where
  show LinearGradient = "linear"
  show RadialGradient = "radial"
  show ConicGradient = "conic"

-- | All gradient types.
allGradientTypes :: Array GradientType
allGradientTypes = [LinearGradient, RadialGradient, ConicGradient]

-- | A stop in a gradient.
type GradientStop =
  { position :: Number    -- ^ Position along gradient (0-1)
  , r :: Number           -- ^ Red (0-1)
  , g :: Number           -- ^ Green (0-1)
  , b :: Number           -- ^ Blue (0-1)
  , a :: Number           -- ^ Alpha (0-1)
  }

-- | Create gradient stop with clamped values.
mkGradientStop :: Number -> Number -> Number -> Number -> Number -> GradientStop
mkGradientStop pos r g b a =
  { position: clamp01 pos
  , r: clamp01 r
  , g: clamp01 g
  , b: clamp01 b
  , a: clamp01 a
  }

-- | Gradient background configuration.
type GradientBackground =
  { gradientType :: GradientType
  , stops :: Array GradientStop
  , angle :: Number              -- ^ Angle in degrees (for linear)
  , centerX :: Number            -- ^ Center X (0-1, for radial)
  , centerY :: Number            -- ^ Center Y (0-1, for radial)
  }

-- | Create gradient background.
mkGradientBackground 
  :: GradientType 
  -> Array GradientStop 
  -> Number 
  -> GradientBackground
mkGradientBackground gtype stops angle =
  { gradientType: gtype
  , stops: stops
  , angle: normalizeAngle angle
  , centerX: 0.5
  , centerY: 0.5
  }

-- | Get gradient type.
gradientType :: GradientBackground -> GradientType
gradientType g = g.gradientType

-- | Get gradient stops.
gradientStops :: GradientBackground -> Array GradientStop
gradientStops g = g.stops

-- | Get gradient angle.
gradientAngle :: GradientBackground -> Number
gradientAngle g = g.angle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of background pattern.
data PatternType
  = CheckerPattern
  | GridPattern
  | DotsPattern
  | LinesPattern
  | CrosshatchPattern
  | NoisePattern

derive instance eqPatternType :: Eq PatternType
derive instance ordPatternType :: Ord PatternType

instance showPatternType :: Show PatternType where
  show CheckerPattern = "checker"
  show GridPattern = "grid"
  show DotsPattern = "dots"
  show LinesPattern = "lines"
  show CrosshatchPattern = "crosshatch"
  show NoisePattern = "noise"

-- | All pattern types.
allPatternTypes :: Array PatternType
allPatternTypes = 
  [ CheckerPattern
  , GridPattern
  , DotsPattern
  , LinesPattern
  , CrosshatchPattern
  , NoisePattern
  ]

-- | Pattern background configuration.
type PatternBackground =
  { patternType :: PatternType
  , scale :: Number           -- ^ Scale factor (1 = 100%)
  , opacity :: Number         -- ^ Pattern opacity (0-1)
  , foreground :: SolidBackground
  , background :: SolidBackground
  }

-- | Create pattern background.
mkPatternBackground 
  :: PatternType 
  -> Number 
  -> Number 
  -> SolidBackground 
  -> SolidBackground 
  -> PatternBackground
mkPatternBackground ptype scale opacity fg bg =
  { patternType: ptype
  , scale: max 0.01 scale
  , opacity: clamp01 opacity
  , foreground: fg
  , background: bg
  }

-- | Get pattern type.
patternType :: PatternBackground -> PatternType
patternType p = p.patternType

-- | Get pattern scale.
patternScale :: PatternBackground -> Number
patternScale p = p.scale

-- | Get pattern opacity.
patternOpacity :: PatternBackground -> Number
patternOpacity p = p.opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // paper properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Paper texture type.
data PaperTexture
  = SmoothPaper        -- ^ Hot press, smooth
  | ColdPressPaper     -- ^ Cold press, medium texture
  | RoughPaper         -- ^ Rough, heavy texture
  | ToothPaper         -- ^ Drawing paper with tooth
  | CanvasPaper        -- ^ Canvas texture
  | VellumPaper        -- ^ Translucent vellum

derive instance eqPaperTexture :: Eq PaperTexture
derive instance ordPaperTexture :: Ord PaperTexture

instance showPaperTexture :: Show PaperTexture where
  show SmoothPaper = "smooth"
  show ColdPressPaper = "cold-press"
  show RoughPaper = "rough"
  show ToothPaper = "tooth"
  show CanvasPaper = "canvas"
  show VellumPaper = "vellum"

-- | All paper textures.
allPaperTextures :: Array PaperTexture
allPaperTextures =
  [ SmoothPaper
  , ColdPressPaper
  , RoughPaper
  , ToothPaper
  , CanvasPaper
  , VellumPaper
  ]

-- | Paper physical properties.
type PaperProperties =
  { texture :: PaperTexture
  , tooth :: Number           -- ^ Surface roughness (0-1)
  , absorption :: Number      -- ^ How quickly paint absorbs (0-1)
  , tint :: SolidBackground   -- ^ Paper color/tint
  }

-- | Create paper properties.
mkPaperProperties 
  :: PaperTexture 
  -> Number 
  -> Number 
  -> SolidBackground 
  -> PaperProperties
mkPaperProperties tex tooth absorp tint =
  { texture: tex
  , tooth: clamp01 tooth
  , absorption: clamp01 absorp
  , tint: tint
  }

-- | Get paper texture.
paperTexture :: PaperProperties -> PaperTexture
paperTexture p = p.texture

-- | Get paper tooth (roughness).
paperTooth :: PaperProperties -> Number
paperTooth p = p.tooth

-- | Get paper absorption rate.
paperAbsorption :: PaperProperties -> Number
paperAbsorption p = p.absorption

-- | Get paper tint color.
paperTint :: PaperProperties -> SolidBackground
paperTint p = p.tint

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // canvas background
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete canvas background configuration.
type CanvasBackground =
  { fill :: BackgroundFill
  , solid :: Maybe SolidBackground
  , gradient :: Maybe GradientBackground
  , pattern :: Maybe PatternBackground
  , paper :: PaperProperties
  }

-- | Create canvas background.
mkCanvasBackground 
  :: BackgroundFill 
  -> PaperProperties 
  -> CanvasBackground
mkCanvasBackground fill paper =
  { fill: fill
  , solid: Nothing
  , gradient: Nothing
  , pattern: Nothing
  , paper: paper
  }

-- | Get background fill type.
backgroundFill :: CanvasBackground -> BackgroundFill
backgroundFill bg = bg.fill

-- | Get paper properties.
backgroundPaper :: CanvasBackground -> PaperProperties
backgroundPaper bg = bg.paper

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard white canvas.
whiteCanvas :: CanvasBackground
whiteCanvas =
  let
    white = mkSolidBackground 1.0 1.0 1.0 1.0
    paper = mkPaperProperties SmoothPaper 0.0 0.5 white
  in
    (mkCanvasBackground FillSolid paper) { solid = Just white }

-- | Cream/off-white canvas.
creamCanvas :: CanvasBackground
creamCanvas =
  let
    cream = mkSolidBackground 0.98 0.96 0.91 1.0
    paper = mkPaperProperties SmoothPaper 0.1 0.5 cream
  in
    (mkCanvasBackground FillSolid paper) { solid = Just cream }

-- | Black canvas.
blackCanvas :: CanvasBackground
blackCanvas =
  let
    black = mkSolidBackground 0.0 0.0 0.0 1.0
    paper = mkPaperProperties SmoothPaper 0.0 0.3 black
  in
    (mkCanvasBackground FillSolid paper) { solid = Just black }

-- | Transparent canvas.
transparentCanvas :: CanvasBackground
transparentCanvas =
  let
    clear = mkSolidBackground 0.0 0.0 0.0 0.0
    paper = mkPaperProperties SmoothPaper 0.0 0.0 clear
  in
    mkCanvasBackground FillTransparent paper

-- | Cold press watercolor paper.
coldPressWatercolor :: CanvasBackground
coldPressWatercolor =
  let
    offWhite = mkSolidBackground 0.97 0.95 0.92 1.0
    paper = mkPaperProperties ColdPressPaper 0.6 0.8 offWhite
  in
    (mkCanvasBackground FillSolid paper) { solid = Just offWhite }

-- | Hot press watercolor paper (smooth).
hotPressWatercolor :: CanvasBackground
hotPressWatercolor =
  let
    white = mkSolidBackground 0.99 0.98 0.97 1.0
    paper = mkPaperProperties SmoothPaper 0.1 0.7 white
  in
    (mkCanvasBackground FillSolid paper) { solid = Just white }

-- | Rough sketch paper.
roughSketch :: CanvasBackground
roughSketch =
  let
    warmGray = mkSolidBackground 0.85 0.83 0.80 1.0
    paper = mkPaperProperties ToothPaper 0.8 0.4 warmGray
  in
    (mkCanvasBackground FillSolid paper) { solid = Just warmGray }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display background fill type.
displayBackgroundFill :: BackgroundFill -> String
displayBackgroundFill fill = show fill <> " fill"

-- | Display paper texture.
displayPaperTexture :: PaperTexture -> String
displayPaperTexture tex = show tex <> " paper"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to 0-1 range.
clamp01 :: Number -> Number
clamp01 n = max 0.0 (min 1.0 n)

-- | Normalize angle to 0-360 range.
normalizeAngle :: Number -> Number
normalizeAngle a
  | a < 0.0 = normalizeAngle (a + 360.0)
  | a >= 360.0 = normalizeAngle (a - 360.0)
  | otherwise = a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // color and fill utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two solid backgrounds are equal.
solidsEqual :: SolidBackground -> SolidBackground -> Boolean
solidsEqual a b = a.r == b.r && a.g == b.g && a.b == b.b && a.a == b.a

-- | Check if a solid background is fully opaque.
isOpaque :: SolidBackground -> Boolean
isOpaque bg = bg.a >= 1.0

-- | Check if a solid background is transparent.
isTransparent :: SolidBackground -> Boolean
isTransparent bg = bg.a <= 0.0

-- | Blend two solid colors by alpha.
-- |
-- | Factor 0 = first color, factor 1 = second color.
blendColors :: SolidBackground -> SolidBackground -> Number -> SolidBackground
blendColors c1 c2 factor =
  let
    t = clamp01 factor
    inv = 1.0 - t
  in
    mkSolidBackground
      (c1.r * inv + c2.r * t)
      (c1.g * inv + c2.g * t)
      (c1.b * inv + c2.b * t)
      (c1.a * inv + c2.a * t)

-- | Calculate luminance of a solid color.
-- |
-- | Uses standard sRGB luminance coefficients.
colorLuminance :: SolidBackground -> Number
colorLuminance bg = 0.2126 * bg.r + 0.7152 * bg.g + 0.0722 * bg.b

-- | Check if a color is light (luminance > 0.5).
isLightColor :: SolidBackground -> Boolean
isLightColor bg = colorLuminance bg > 0.5

-- | Check if a color is dark (luminance <= 0.5).
isDarkColor :: SolidBackground -> Boolean
isDarkColor bg = colorLuminance bg <= 0.5

-- | Interpolate between two gradient stops.
interpolateStops :: GradientStop -> GradientStop -> Number -> GradientStop
interpolateStops s1 s2 t =
  let
    factor = clamp01 t
    inv = 1.0 - factor
  in
    { position: s1.position * inv + s2.position * factor
    , r: s1.r * inv + s2.r * factor
    , g: s1.g * inv + s2.g * factor
    , b: s1.b * inv + s2.b * factor
    , a: s1.a * inv + s2.a * factor
    }

-- | Scale paper tooth by a factor.
scalePaperTooth :: PaperProperties -> Number -> PaperProperties
scalePaperTooth paper factor =
  paper { tooth = clamp01 (paper.tooth * factor) }

-- | Scale paper absorption by a factor.
scalePaperAbsorption :: PaperProperties -> Number -> PaperProperties
scalePaperAbsorption paper factor =
  paper { absorption = clamp01 (paper.absorption * factor) }
