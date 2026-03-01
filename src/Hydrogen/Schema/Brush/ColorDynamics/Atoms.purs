-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // brush // colordynamics // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color Dynamics Atoms — Bounded numeric parameters for color variation.
-- |
-- | ## Design Philosophy
-- |
-- | Color dynamics atoms represent the bounded numeric primitives for
-- | controlling how brush color varies during a stroke. Each jitter parameter
-- | specifies a percentage of maximum variation, with deterministic bounds.
-- |
-- | ## HSB Jitter Model
-- |
-- | Color variation operates in HSB (Hue, Saturation, Brightness) space:
-- |
-- | - **Hue Jitter**: ±180° around the color wheel at 100%
-- | - **Saturation Jitter**: 0% to base saturation at 100%
-- | - **Brightness Jitter**: 0% to base brightness at 100%
-- |
-- | This model matches traditional painting software behavior and provides
-- | intuitive control over color variation.
-- |
-- | ## Foreground/Background Position
-- |
-- | When source is ForegroundBackground, a position value (0-1) determines
-- | the interpolation between the two colors. This can be controlled by
-- | pressure, tilt, velocity, or stroke distance.
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.ColorDynamics.Atoms
  ( -- * HueJitter (0 to 100)
    HueJitter(HueJitter)
  , hueJitter
  , hueJitterBounds
  , unwrapHueJitter
  , noHueJitter
  , subtleHueJitter
  , moderateHueJitter
  , fullHueJitter
  , hueJitterDebugInfo
  
  -- * SaturationJitter (0 to 100)
  , SaturationJitter(SaturationJitter)
  , saturationJitter
  , saturationJitterBounds
  , unwrapSaturationJitter
  , noSaturationJitter
  , subtleSaturationJitter
  , moderateSaturationJitter
  , fullSaturationJitter
  , saturationJitterDebugInfo
  
  -- * BrightnessJitter (0 to 100)
  , BrightnessJitter(BrightnessJitter)
  , brightnessJitter
  , brightnessJitterBounds
  , unwrapBrightnessJitter
  , noBrightnessJitter
  , subtleBrightnessJitter
  , moderateBrightnessJitter
  , fullBrightnessJitter
  , brightnessJitterDebugInfo
  
  -- * Purity (0 to 100)
  , Purity(Purity)
  , purity
  , purityBounds
  , unwrapPurity
  , grayscalePurity
  , desaturatedPurity
  , standardPurity
  , vibrantPurity
  , purityDebugInfo
  
  -- * FGBGPosition (0 to 1)
  , FGBGPosition(FGBGPosition)
  , fgbgPosition
  , fgbgPositionBounds
  , unwrapFGBGPosition
  , atForeground
  , atMidpoint
  , atBackground
  , fgbgPositionDebugInfo
  
  -- * MixRatio (0 to 100)
  , MixRatio(MixRatio)
  , mixRatio
  , mixRatioBounds
  , unwrapMixRatio
  , noMixing
  , lightMixing
  , heavyMixing
  , fullMixing
  , mixRatioDebugInfo
  
  -- * PaintLoad (0 to 100)
  , PaintLoad(PaintLoad)
  , paintLoad
  , paintLoadBounds
  , unwrapPaintLoad
  , emptyBrush
  , lightLoad
  , standardLoad
  , heavyLoad
  , paintLoadDebugInfo
  
  -- * Range Queries
  , hasSignificantHueJitter
  , hasSignificantSaturationJitter
  , hasSignificantBrightnessJitter
  , hasAnyColorJitter
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (*)
  , (>=)
  , (||)
  )

import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , NumberBounds
  , clampNumber
  , numberBounds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // hue jitter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hue jitter percentage (0-100).
-- |
-- | Random variation in hue per dab. At 100%, hue varies ±180° around
-- | the color wheel (all colors possible). At 50%, ±90°. At 0%, no variation.
-- |
-- | This is percentage of maximum variation, not degrees.
-- | Clamps to bounds.
newtype HueJitter = HueJitter Number

derive instance eqHueJitter :: Eq HueJitter
derive instance ordHueJitter :: Ord HueJitter

instance showHueJitter :: Show HueJitter where
  show (HueJitter n) = "(HueJitter " <> show n <> "%)"

-- | Bounds for HueJitter: 0 to 100, clamps.
hueJitterBounds :: NumberBounds
hueJitterBounds = numberBounds 0.0 100.0 Clamps "hueJitter" "Random hue variation percentage"

-- | Smart constructor that clamps to bounds.
hueJitter :: Number -> HueJitter
hueJitter n = HueJitter (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapHueJitter :: HueJitter -> Number
unwrapHueJitter (HueJitter n) = n

-- | No hue variation.
noHueJitter :: HueJitter
noHueJitter = HueJitter 0.0

-- | Subtle hue variation (±18° at this setting).
subtleHueJitter :: HueJitter
subtleHueJitter = HueJitter 10.0

-- | Moderate hue variation (±90° at this setting).
moderateHueJitter :: HueJitter
moderateHueJitter = HueJitter 50.0

-- | Full hue variation (±180°, all colors).
fullHueJitter :: HueJitter
fullHueJitter = HueJitter 100.0

-- | Generate debug info string.
hueJitterDebugInfo :: HueJitter -> String
hueJitterDebugInfo h =
  show h <> " [bounds: 0-100%, ±" <> show (unwrapHueJitter h * 1.8) <> "°]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // saturation jitter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Saturation jitter percentage (0-100).
-- |
-- | Random variation in saturation per dab. At 100%, saturation can drop
-- | from base to 0% (grayscale). At 0%, no variation.
-- | Clamps to bounds.
newtype SaturationJitter = SaturationJitter Number

derive instance eqSaturationJitter :: Eq SaturationJitter
derive instance ordSaturationJitter :: Ord SaturationJitter

instance showSaturationJitter :: Show SaturationJitter where
  show (SaturationJitter n) = "(SaturationJitter " <> show n <> "%)"

-- | Bounds for SaturationJitter: 0 to 100, clamps.
saturationJitterBounds :: NumberBounds
saturationJitterBounds = numberBounds 0.0 100.0 Clamps "saturationJitter" "Random saturation variation percentage"

-- | Smart constructor that clamps to bounds.
saturationJitter :: Number -> SaturationJitter
saturationJitter n = SaturationJitter (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapSaturationJitter :: SaturationJitter -> Number
unwrapSaturationJitter (SaturationJitter n) = n

-- | No saturation variation.
noSaturationJitter :: SaturationJitter
noSaturationJitter = SaturationJitter 0.0

-- | Subtle saturation variation.
subtleSaturationJitter :: SaturationJitter
subtleSaturationJitter = SaturationJitter 15.0

-- | Moderate saturation variation.
moderateSaturationJitter :: SaturationJitter
moderateSaturationJitter = SaturationJitter 50.0

-- | Full saturation variation (can go grayscale).
fullSaturationJitter :: SaturationJitter
fullSaturationJitter = SaturationJitter 100.0

-- | Generate debug info string.
saturationJitterDebugInfo :: SaturationJitter -> String
saturationJitterDebugInfo s =
  show s <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // brightness jitter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Brightness jitter percentage (0-100).
-- |
-- | Random variation in brightness per dab. At 100%, brightness can drop
-- | from base to 0% (black). At 0%, no variation.
-- | Clamps to bounds.
newtype BrightnessJitter = BrightnessJitter Number

derive instance eqBrightnessJitter :: Eq BrightnessJitter
derive instance ordBrightnessJitter :: Ord BrightnessJitter

instance showBrightnessJitter :: Show BrightnessJitter where
  show (BrightnessJitter n) = "(BrightnessJitter " <> show n <> "%)"

-- | Bounds for BrightnessJitter: 0 to 100, clamps.
brightnessJitterBounds :: NumberBounds
brightnessJitterBounds = numberBounds 0.0 100.0 Clamps "brightnessJitter" "Random brightness variation percentage"

-- | Smart constructor that clamps to bounds.
brightnessJitter :: Number -> BrightnessJitter
brightnessJitter n = BrightnessJitter (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapBrightnessJitter :: BrightnessJitter -> Number
unwrapBrightnessJitter (BrightnessJitter n) = n

-- | No brightness variation.
noBrightnessJitter :: BrightnessJitter
noBrightnessJitter = BrightnessJitter 0.0

-- | Subtle brightness variation.
subtleBrightnessJitter :: BrightnessJitter
subtleBrightnessJitter = BrightnessJitter 15.0

-- | Moderate brightness variation.
moderateBrightnessJitter :: BrightnessJitter
moderateBrightnessJitter = BrightnessJitter 50.0

-- | Full brightness variation (can go black).
fullBrightnessJitter :: BrightnessJitter
fullBrightnessJitter = BrightnessJitter 100.0

-- | Generate debug info string.
brightnessJitterDebugInfo :: BrightnessJitter -> String
brightnessJitterDebugInfo b =
  show b <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // purity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color purity percentage (0-100).
-- |
-- | How saturated/pure the applied color is. At 0%, color is grayscale.
-- | At 100%, color is fully saturated. This is a global multiplier applied
-- | after other color dynamics.
-- | Clamps to bounds.
newtype Purity = Purity Number

derive instance eqPurity :: Eq Purity
derive instance ordPurity :: Ord Purity

instance showPurity :: Show Purity where
  show (Purity n) = "(Purity " <> show n <> "%)"

-- | Bounds for Purity: 0 to 100, clamps.
purityBounds :: NumberBounds
purityBounds = numberBounds 0.0 100.0 Clamps "purity" "Color saturation multiplier percentage"

-- | Smart constructor that clamps to bounds.
purity :: Number -> Purity
purity n = Purity (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapPurity :: Purity -> Number
unwrapPurity (Purity n) = n

-- | Grayscale output.
grayscalePurity :: Purity
grayscalePurity = Purity 0.0

-- | Desaturated output.
desaturatedPurity :: Purity
desaturatedPurity = Purity 50.0

-- | Standard full color.
standardPurity :: Purity
standardPurity = Purity 100.0

-- | Alias for standard (fully saturated).
vibrantPurity :: Purity
vibrantPurity = Purity 100.0

-- | Generate debug info string.
purityDebugInfo :: Purity -> String
purityDebugInfo p =
  show p <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // fgbg position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Foreground/Background position (0-1).
-- |
-- | Position along the FG-BG gradient. 0 = pure foreground, 1 = pure
-- | background, 0.5 = midpoint blend. This value can be dynamically
-- | controlled by pressure, tilt, velocity, or stroke position.
-- | Clamps to bounds.
newtype FGBGPosition = FGBGPosition Number

derive instance eqFGBGPosition :: Eq FGBGPosition
derive instance ordFGBGPosition :: Ord FGBGPosition

instance showFGBGPosition :: Show FGBGPosition where
  show (FGBGPosition n) = "(FGBGPosition " <> show n <> ")"

-- | Bounds for FGBGPosition: 0 to 1, clamps.
fgbgPositionBounds :: NumberBounds
fgbgPositionBounds = numberBounds 0.0 1.0 Clamps "fgbgPosition" "Foreground to background interpolation"

-- | Smart constructor that clamps to bounds.
fgbgPosition :: Number -> FGBGPosition
fgbgPosition n = FGBGPosition (clampNumber 0.0 1.0 n)

-- | Extract the raw Number value.
unwrapFGBGPosition :: FGBGPosition -> Number
unwrapFGBGPosition (FGBGPosition n) = n

-- | Pure foreground color.
atForeground :: FGBGPosition
atForeground = FGBGPosition 0.0

-- | Midpoint between FG and BG.
atMidpoint :: FGBGPosition
atMidpoint = FGBGPosition 0.5

-- | Pure background color.
atBackground :: FGBGPosition
atBackground = FGBGPosition 1.0

-- | Generate debug info string.
fgbgPositionDebugInfo :: FGBGPosition -> String
fgbgPositionDebugInfo pos =
  show pos <> " [bounds: 0-1, 0=FG, 1=BG]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // mix ratio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Canvas color mix ratio percentage (0-100).
-- |
-- | How much existing canvas color mixes into the brush color. At 0%,
-- | brush applies pure color. At 100%, brush picks up and blends with
-- | canvas color (like wet paint mixing). This simulates oil/watercolor
-- | wet-in-wet techniques.
-- | Clamps to bounds.
newtype MixRatio = MixRatio Number

derive instance eqMixRatio :: Eq MixRatio
derive instance ordMixRatio :: Ord MixRatio

instance showMixRatio :: Show MixRatio where
  show (MixRatio n) = "(MixRatio " <> show n <> "%)"

-- | Bounds for MixRatio: 0 to 100, clamps.
mixRatioBounds :: NumberBounds
mixRatioBounds = numberBounds 0.0 100.0 Clamps "mixRatio" "Canvas color pickup percentage"

-- | Smart constructor that clamps to bounds.
mixRatio :: Number -> MixRatio
mixRatio n = MixRatio (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapMixRatio :: MixRatio -> Number
unwrapMixRatio (MixRatio n) = n

-- | No color pickup from canvas.
noMixing :: MixRatio
noMixing = MixRatio 0.0

-- | Light color mixing (30%).
lightMixing :: MixRatio
lightMixing = MixRatio 30.0

-- | Heavy color mixing (70%).
heavyMixing :: MixRatio
heavyMixing = MixRatio 70.0

-- | Full color mixing (pure wet blending).
fullMixing :: MixRatio
fullMixing = MixRatio 100.0

-- | Generate debug info string.
mixRatioDebugInfo :: MixRatio -> String
mixRatioDebugInfo m =
  show m <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // paint load
-- ═════════════════════════════════════════════════════════════════════════════

-- | Paint load percentage (0-100).
-- |
-- | How much paint is loaded on the brush. At 100%, full paint reservoir.
-- | Paint depletes during stroke, affecting opacity and color mixing.
-- | When paint runs low, more canvas color shows through.
-- | Clamps to bounds.
newtype PaintLoad = PaintLoad Number

derive instance eqPaintLoad :: Eq PaintLoad
derive instance ordPaintLoad :: Ord PaintLoad

instance showPaintLoad :: Show PaintLoad where
  show (PaintLoad n) = "(PaintLoad " <> show n <> "%)"

-- | Bounds for PaintLoad: 0 to 100, clamps.
paintLoadBounds :: NumberBounds
paintLoadBounds = numberBounds 0.0 100.0 Clamps "paintLoad" "Paint reservoir amount percentage"

-- | Smart constructor that clamps to bounds.
paintLoad :: Number -> PaintLoad
paintLoad n = PaintLoad (clampNumber 0.0 100.0 n)

-- | Extract the raw Number value.
unwrapPaintLoad :: PaintLoad -> Number
unwrapPaintLoad (PaintLoad n) = n

-- | Empty brush (dry brush effect).
emptyBrush :: PaintLoad
emptyBrush = PaintLoad 0.0

-- | Lightly loaded brush.
lightLoad :: PaintLoad
lightLoad = PaintLoad 30.0

-- | Standard paint load.
standardLoad :: PaintLoad
standardLoad = PaintLoad 100.0

-- | Heavy paint load (impasto).
heavyLoad :: PaintLoad
heavyLoad = PaintLoad 100.0

-- | Generate debug info string.
paintLoadDebugInfo :: PaintLoad -> String
paintLoadDebugInfo p =
  show p <> " [bounds: 0-100%, clamps]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // range queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if hue jitter is significant (>= 5%).
hasSignificantHueJitter :: HueJitter -> Boolean
hasSignificantHueJitter (HueJitter n) = n >= 5.0

-- | Check if saturation jitter is significant (>= 5%).
hasSignificantSaturationJitter :: SaturationJitter -> Boolean
hasSignificantSaturationJitter (SaturationJitter n) = n >= 5.0

-- | Check if brightness jitter is significant (>= 5%).
hasSignificantBrightnessJitter :: BrightnessJitter -> Boolean
hasSignificantBrightnessJitter (BrightnessJitter n) = n >= 5.0

-- | Check if any color jitter is enabled.
hasAnyColorJitter :: HueJitter -> SaturationJitter -> BrightnessJitter -> Boolean
hasAnyColorJitter h s b =
  hasSignificantHueJitter h ||
  hasSignificantSaturationJitter s ||
  hasSignificantBrightnessJitter b
