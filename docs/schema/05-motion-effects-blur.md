# Motion Pillar: Blur Effects

> Part of the Motion pillar documentation. See [05-motion.md](./05-motion.md) for index.

## Overview

Complete blur and sharpen effects matching professional compositing blur & sharpen category:

- **Gaussian Blur** — Smooth, bell-curve weighted blur (most common)
- **Box Blur** — Uniform averaging with iteration control
- **Directional Blur** — Motion blur along an angle
- **Radial Blur** — Spin or zoom blur from a center point
- **Camera Lens Blur** — Depth-of-field simulation with bokeh
- **Edge-Preserving** — Bilateral and Smart blur (preserve edges)
- **Channel Blur** — Independent blur per color channel
- **Sharpen** — Edge enhancement and unsharp mask

All blur amounts are in pixels. Effect types include validation, composition 
operations, and Semigroup instances for combining effects.

## Source Files

```
src/Hydrogen/Schema/Motion/Effects/
├── Blur.purs                    # Leader module re-exports (187 lines)
└── Blur/
    ├── Types.purs               # Shared enums and validation (328 lines)
    ├── Gaussian.purs            # Gaussian blur (261 lines)
    ├── Box.purs                 # Box blur
    ├── Directional.purs         # Directional blur
    ├── Radial.purs              # Radial blur
    ├── CameraLens.purs          # Camera lens blur
    ├── EdgePreserving.purs      # Bilateral and Smart blur
    ├── Channel.purs             # Per-channel blur
    ├── Sharpen.purs             # Sharpen effects
    └── Misc.purs                # Compound and Fast blur
```

## Blur Types and Enumerations

**Source**: `Blur/Types.purs` (328 lines)

### BlurDimension

```purescript
data BlurDimension
  = BDHorizontal  -- Blur only horizontally
  | BDVertical    -- Blur only vertically
  | BDBoth        -- Blur in both directions

allBlurDimensions       :: Array BlurDimension
blurDimensionToString   :: BlurDimension -> String
blurDimensionFromString :: String -> Maybe BlurDimension
combineDimensions       :: BlurDimension -> BlurDimension -> BlurDimension
```

### RadialBlurType

```purescript
data RadialBlurType
  = RBTSpin   -- Rotational blur around center
  | RBTZoom   -- Zoom blur from center
```

### IrisShape (Bokeh)

```purescript
data IrisShape
  = IrisTriangle | IrisSquare | IrisPentagon | IrisHexagon
  | IrisHeptagon | IrisOctagon | IrisDecagon | IrisCircle
```

### Quality and Mode Enums

```purescript
data AntialiasingQuality = AAQLow | AAQMedium | AAQHigh

data SmartBlurMode = SBMNormal | SBMEdgeOnly | SBMOverlay

data SmartBlurQuality = SBQLow | SBQMedium | SBQHigh

data DepthMapChannel 
  = DepthLuminance | DepthRed | DepthGreen | DepthBlue | DepthAlpha
```

### Validation

```purescript
data BlurValidationError
  = BlurOutOfRange String Number Number Number  -- field, value, min, max
  | InvalidIterations Int
  | InvalidCenter Number Number
```

## Gaussian Blur

**Source**: `Blur/Gaussian.purs` (261 lines)

The most common blur type, producing smooth, natural-looking softening.

```purescript
type GaussianBlurEffect =
  { blurriness :: Number         -- Blur radius in pixels (0-1000)
  , dimensions :: BlurDimension  -- Horizontal, Vertical, or Both
  , repeatEdgePixels :: Boolean  -- Extend edge pixels to avoid transparency
  }

-- Construction
defaultGaussianBlur :: GaussianBlurEffect
mkGaussianBlur :: Number -> BlurDimension -> Boolean -> GaussianBlurEffect

-- Queries
isGaussianNeutral :: GaussianBlurEffect -> Boolean  -- blurriness == 0
hasVisibleBlur    :: GaussianBlurEffect -> Boolean  -- blurriness >= 0.5

-- Validation
validateGaussianBlur     :: GaussianBlurEffect -> Maybe BlurValidationError
validateAllGaussianBlurs :: Array GaussianBlurEffect -> Array BlurValidationError

-- Comparisons
compareBlurIntensity :: GaussianBlurEffect -> GaussianBlurEffect -> Ordering
isStrongerBlur       :: GaussianBlurEffect -> GaussianBlurEffect -> Boolean
isWeakerBlur         :: GaussianBlurEffect -> GaussianBlurEffect -> Boolean

-- Operations
combineGaussianBlurs :: GaussianBlurEffect -> GaussianBlurEffect -> GaussianBlurEffect
scaleGaussianBlur    :: Number -> GaussianBlurEffect -> GaussianBlurEffect
lerpGaussianBlur     :: Number -> GaussianBlurEffect -> GaussianBlurEffect -> GaussianBlurEffect
mapBlurAmount        :: (Number -> Number) -> Array GaussianBlurEffect -> Array GaussianBlurEffect
```

### CombinableGaussian (Semigroup)

```purescript
newtype CombinableGaussian = CombinableGaussian GaussianBlurEffect

instance Semigroup CombinableGaussian  -- Adds blur amounts, widens dimensions

toCombinableGaussian   :: GaussianBlurEffect -> CombinableGaussian
fromCombinableGaussian :: CombinableGaussian -> GaussianBlurEffect

-- Usage: blur1 <> blur2 <> blur3
```

## Box Blur

**Source**: `Blur/Box.purs`

Uniform-weighted rectangular blur. Faster than Gaussian but produces harsher edges.
Multiple iterations approach Gaussian quality.

```purescript
type BoxBlurEffect =
  { blurRadius :: Number         -- Blur radius in pixels (0-1000)
  , iterations :: Int            -- Number of passes (1-10)
  , dimensions :: BlurDimension  -- Direction of blur
  , repeatEdgePixels :: Boolean  -- Extend edge pixels
  }

defaultBoxBlur :: BoxBlurEffect
mkBoxBlur      :: Number -> Int -> BlurDimension -> Boolean -> BoxBlurEffect
isBoxNeutral   :: BoxBlurEffect -> Boolean
validateBoxBlur :: BoxBlurEffect -> Maybe BlurValidationError
boxBlurToString :: BoxBlurEffect -> String
```

## Directional Blur

**Source**: `Blur/Directional.purs`

Motion blur along a specific angle. Simulates camera or object movement.

```purescript
type DirectionalBlurEffect =
  { direction :: Number  -- Blur angle in degrees (0-360)
  , blurLength :: Number -- Length of blur in pixels (0-1000)
  }

defaultDirectionalBlur :: DirectionalBlurEffect
mkDirectionalBlur      :: Number -> Number -> DirectionalBlurEffect
isDirectionalNeutral   :: DirectionalBlurEffect -> Boolean
directionalBlurToString :: DirectionalBlurEffect -> String

-- Operations
negateDirectionalBlur :: DirectionalBlurEffect -> DirectionalBlurEffect  -- Reverse 180°
scaleDirectionalBlur  :: Number -> DirectionalBlurEffect -> DirectionalBlurEffect
lerpDirectionalBlur   :: Number -> DirectionalBlurEffect -> DirectionalBlurEffect -> DirectionalBlurEffect
```

## Radial Blur

**Source**: `Blur/Radial.purs`

Spin or zoom blur around a center point.

```purescript
type RadialBlurEffect =
  { amount :: Number              -- Blur intensity (0-100)
  , centerX :: Number             -- Center X position (0-1 normalized)
  , centerY :: Number             -- Center Y position (0-1 normalized)
  , blurType :: RadialBlurType    -- Spin or Zoom
  , quality :: AntialiasingQuality -- Render quality
  }

defaultRadialBlur  :: RadialBlurEffect
mkRadialBlur       :: Number -> Number -> Number -> RadialBlurType -> AntialiasingQuality -> RadialBlurEffect
isRadialNeutral    :: RadialBlurEffect -> Boolean
validateRadialBlur :: RadialBlurEffect -> Maybe BlurValidationError
radialBlurToString :: RadialBlurEffect -> String
```

## Camera Lens Blur

**Source**: `Blur/CameraLens.purs`

Depth-of-field simulation with realistic bokeh shapes.

```purescript
type CameraLensBlurEffect =
  { blurRadius :: Number           -- Blur amount (0-500)
  , irisShape :: IrisShape         -- Bokeh shape (hexagon, circle, etc.)
  , irisRotation :: Number         -- Rotation of iris shape (0-360)
  , irisDiffraction :: Number      -- Fringe highlights (0-100)
  , focusDistance :: Number        -- Focal plane (0-1)
  , blurFocal :: Number            -- Blur at focal (typically 0)
  , specularBrightness :: Number   -- Highlight boost (0-100)
  , specularThreshold :: Number    -- Threshold for highlights (0-255)
  , depthMapChannel :: DepthMapChannel  -- Which channel for depth
  }

defaultCameraLensBlur  :: CameraLensBlurEffect
mkCameraLensBlur       :: ... -> CameraLensBlurEffect
isCameraLensNeutral    :: CameraLensBlurEffect -> Boolean
validateCameraLensBlur :: CameraLensBlurEffect -> Maybe BlurValidationError
```

## Edge-Preserving Blurs

**Source**: `Blur/EdgePreserving.purs`

### Bilateral Blur

Smooths surfaces while preserving edges. Essential for skin retouching.

```purescript
type BilateralBlurEffect =
  { radius :: Number         -- Blur radius (0-100)
  , threshold :: Number      -- Edge threshold (0-100)
  , colorspace :: String     -- RGB or Lab
  }

defaultBilateralBlur  :: BilateralBlurEffect
mkBilateralBlur       :: Number -> Number -> String -> BilateralBlurEffect
isBilateralNeutral    :: BilateralBlurEffect -> Boolean
bilateralBlurToString :: BilateralBlurEffect -> String
```

### Smart Blur

Simplified edge-preserving blur with mode options.

```purescript
type SmartBlurEffect =
  { radius :: Number            -- Blur radius (0-100)
  , threshold :: Number         -- Edge detection threshold (0-100)
  , mode :: SmartBlurMode       -- Normal, Edge Only, or Overlay
  , quality :: SmartBlurQuality -- Low, Medium, or High
  }

defaultSmartBlur   :: SmartBlurEffect
mkSmartBlur        :: Number -> Number -> SmartBlurMode -> SmartBlurQuality -> SmartBlurEffect
isSmartBlurNeutral :: SmartBlurEffect -> Boolean
```

## Channel Blur

**Source**: `Blur/Channel.purs`

Independent blur per color channel. Useful for chromatic aberration effects.

```purescript
type ChannelBlurEffect =
  { red :: Number     -- Red channel blur (0-500)
  , green :: Number   -- Green channel blur (0-500)
  , blue :: Number    -- Blue channel blur (0-500)
  , alpha :: Number   -- Alpha channel blur (0-500)
  , dimensions :: BlurDimension
  , repeatEdgePixels :: Boolean
  }

defaultChannelBlur    :: ChannelBlurEffect
mkChannelBlur         :: Number -> Number -> Number -> Number -> BlurDimension -> Boolean -> ChannelBlurEffect
isChannelBlurNeutral  :: ChannelBlurEffect -> Boolean
hasChannelDifference  :: ChannelBlurEffect -> Boolean  -- Different values per channel?
isUniformChannelBlur  :: ChannelBlurEffect -> Boolean  -- All channels same?
channelBlurToString   :: ChannelBlurEffect -> String
invertChannelBlur     :: ChannelBlurEffect -> ChannelBlurEffect
applyToAllChannels    :: Number -> ChannelBlurEffect -> ChannelBlurEffect
normalizeChannelBlur  :: ChannelBlurEffect -> ChannelBlurEffect
mapChannelBlurs       :: (Number -> Number) -> ChannelBlurEffect -> ChannelBlurEffect
```

## Sharpen Effects

**Source**: `Blur/Sharpen.purs`

### Sharpen

Simple edge enhancement.

```purescript
type SharpenEffect =
  { amount :: Number  -- Sharpening intensity (0-500)
  }

defaultSharpen   :: SharpenEffect
mkSharpen        :: Number -> SharpenEffect
isSharpenNeutral :: SharpenEffect -> Boolean
sharpenToString  :: SharpenEffect -> String
```

### Unsharp Mask

Professional sharpening with radius and threshold control.

```purescript
type UnsharpMaskEffect =
  { amount :: Number     -- Sharpening intensity (0-500%)
  , radius :: Number     -- Blur radius for edge detection (0-250)
  , threshold :: Number  -- Level threshold to ignore (0-255)
  }

defaultUnsharpMask   :: UnsharpMaskEffect
mkUnsharpMask        :: Number -> Number -> Number -> UnsharpMaskEffect
isUnsharpMaskNeutral :: UnsharpMaskEffect -> Boolean
unsharpMaskToString  :: UnsharpMaskEffect -> String
```

## Miscellaneous Blur Effects

**Source**: `Blur/Misc.purs`

### Compound Blur

Uses another layer as a blur map for variable blur.

```purescript
type CompoundBlurEffect =
  { maxBlur :: Number       -- Maximum blur radius (0-500)
  , blurLayer :: String     -- Layer ID to use as blur map
  , invertBlurMap :: Boolean
  , stretchToFit :: Boolean
  }

defaultCompoundBlur :: CompoundBlurEffect
mkCompoundBlur      :: Number -> String -> Boolean -> Boolean -> CompoundBlurEffect
```

### Fast Blur

GPU-optimized blur with less precision but higher performance.

```purescript
type FastBlurEffect =
  { blurriness :: Number         -- Blur amount (0-500)
  , dimensions :: BlurDimension
  , repeatEdgePixels :: Boolean
  }

defaultFastBlur :: FastBlurEffect
mkFastBlur      :: Number -> BlurDimension -> Boolean -> FastBlurEffect
```

