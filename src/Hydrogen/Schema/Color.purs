-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // schema // color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color pillar - complete color science foundation for autonomous agents.
-- |
-- | **ATOMIC COMPOSITION ARCHITECTURE:**
-- | Built from atoms → molecules → compounds for zero ambiguity at billion-agent scale.
-- |
-- | ## Color Spaces (all bidirectionally convertible)
-- |
-- | **Device-dependent (display colors):**
-- | - **RGB** - Red, Green, Blue (0-255 per channel) - sRGB display colors
-- | - **HSL** - Hue (0-360°), Saturation (0-100%), Lightness (0-100%) - intuitive color wheel
-- | - **CMYK** - Cyan, Magenta, Yellow, Key/Black (0-100% ink) - print colors
-- |
-- | **Device-independent (bridging space):**
-- | - **XYZ** - CIE 1931 tristimulus values - the mathematical bridge between all spaces
-- |
-- | **Perceptually uniform (accurate "10% lighter" operations):**
-- | - **LAB** - L*a*b* perceptual color space - industry standard for color math
-- | - **LCH** - L*C*h° cylindrical LAB - perceptually correct color wheel
-- |
-- | **Specialized:**
-- | - **Kelvin** - Color temperature (1000-40000K) - warm/cool light
-- | - **Hex** - Web colors (#FF0000) - human-readable codes
-- |
-- | ## Accessibility (8% males, 0.5% females affected)
-- |
-- | - **CVD** - Color Vision Deficiency simulation for all types (Protanopia, Deuteranopia, etc.)
-- | - **Contrast** - WCAG compliance checking with deltaE calculations
-- | - **Accurate prevalence data** - cited from authoritative sources (NEI, Colour Blind Awareness)
-- |
-- | ## Compositing & Effects
-- |
-- | - **BlendMode** - 36 blend modes (Photoshop/After Effects parity, trade dress compliant)
-- | - **Glow** - Atomic glow effects (color + intensity + spread)
-- |
-- | ## Professional Color Grading
-- |
-- | - **WhiteBalance** - Temperature + tint correction with presets (Daylight, Tungsten, etc.)
-- | - **ColorWheels** - Lift/Gamma/Gain for shadows/midtones/highlights
-- |
-- | ## Design Tools
-- |
-- | - **Harmony** - Color wheel relationships (complementary, triadic, analogous, etc.)
-- | - **Palette** - Systematic palette generation (tints, shades, tones, semantic roles)
-- | - **Conversion** - Bidirectional sync for color picker integration
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Color as Color
-- |
-- | -- RGB color
-- | primary = Color.rgb 59 130 246
-- |
-- | -- Serialize for backend
-- | json = Color.rgbToRecord primary
-- |
-- | -- Deserialize from backend
-- | color = Color.rgbFromRecord { r: 59, g: 130, b: 246 }
-- |
-- | -- Convert to perceptually uniform space
-- | lab = Color.rgbToLab primary
-- | ```

module Hydrogen.Schema.Color
  ( -- * RGB Color Space
    RGB
  , RGBA
  , rgb
  , rgba
  , fromChannels
  , red
  , green
  , blue
  , alpha
  , invert
  , blend
  , add
  , multiply
  , screen
  , toCss
  , toHex
  , toCssA
  , toRGBA
  , fromRGBA
  
  -- * HSL Color Space
  , HSL
  , hsl
  , fromComponents
  , hue
  , saturation
  , lightness
  
  -- * CMYK Color Space
  , CMYK
  , cmyk
  , cmykFromComponents
  , cyan
  , magenta
  , yellow
  , key
  , cmykToCss
  
  -- * LAB Color Space (Perceptually Uniform)
  , LAB
  , LabL
  , LabA
  , LabB
  , lab
  , labL
  , labA
  , labB
  , deltaE
  
  -- * LCH Color Space (Perceptually Uniform Cylindrical)
  , LCH
  , LchL
  , LchC
  , LchH
  , lch
  , lchL
  , lchC
  , lchH
  
  -- * XYZ Color Space (Device Independent)
  , XYZ
  , XComponent
  , YComponent
  , ZComponent
  , xyz
  , xComponent
  , yComponent
  , zComponent
  , d65White
  
  -- * Color Space Conversions
  , hslToRgb
  , rgbToHsl
  , rgbToCmyk
  , cmykToRgb
  , rgbToHex
  , hexToRgb
  , rgbToXyz
  , xyzToRgb
  , xyzToLab
  , labToXyz
  , rgbToLab
  , labToRgb
  , rgbToLch
  , lchToRgb
  , kelvinToRgb
  
  -- * Record Serialization (Backend Persistence)
  , rgbToRecord
  , rgbFromRecord
  , hslToRecord
  , hslFromRecord
  , cmykToRecord
  , cmykFromRecord
  , labToRecord
  , labFromRecord
  , lchToRecord
  , lchFromRecord
  , xyzToRecord
  , xyzFromRecord
  
  -- * Blend Modes
  , BlendMode(..)
  , blendRGBA
  , blendChannel
  , CompositeOp(..)
  , composite
  , mixRGB
  , mixRGBA
  , lerpRGB
  , blendModeToCss
  , compositeOpToCss
  
  -- * Glow Effects
  , Glow
  , glow
  , glowFromRecord
  , glowColor
  , glowIntensity
  , glowSpread
  , glowToRecord
  , glowToRgb
  , glowToCss
  , withColor
  , withIntensity
  , withSpread
  , warmGlow
  , coolGlow
  , neutralGlow
  
  -- * Color Vision Deficiency
  , CVDType(..)
  , cvdPrevalence
  , AccessibilityIssue
  , AccessibilityReport
  , simulateCVD
  , isDistinguishable
  , checkAccessibility
  , suggestAccessibleAlternative
  , ensureAccessible
  , cvdSafeContrast
  
  -- * Contrast & WCAG
  , WCAGLevel(..)
  , Contrast
  , contrastRatio
  , contrastBetween
  , meetsWCAG
  , suggestForeground
  , luminanceRGB
  , relativeLuminance
  
  -- * Color Harmony
  , Harmony(..)
  , HarmonyConfig
  , generateHarmony
  
  -- * Color Properties
  , colorfulness
  , chroma
  , brightness
  , value
  , perceivedLightness
  , labLightness
  
  -- * Color Temperature
  , Temperature(..)
  , temperatureFromHSL
  , kelvin
  
  -- * Color Mood
  , Mood(..)
  , moodFromHSL
  , moodDescription
  
  -- * White Balance
  , WhiteBalance
  , Preset(..)
  , whiteBalance
  , fromPreset
  , temperature
  , tint
  , whiteBalanceApplyToRgb
  , withTemperature
  , withTint
  
  -- * Color Wheels (Lift/Gamma/Gain)
  , ColorWheels
  , WheelAdjustment
  , colorWheels
  , neutralWheels
  , wheelAdjustment
  , neutralAdjustment
  , lift
  , gamma
  , gain
  , colorWheelsApplyToRgb
  , withLift
  , withGamma
  , withGain
  ) where

import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.CMYK as CMYK
import Hydrogen.Schema.Color.LAB as LAB
import Hydrogen.Schema.Color.LCH as LCH
import Hydrogen.Schema.Color.XYZ as XYZ
import Hydrogen.Schema.Color.Conversion as Conversion
import Hydrogen.Schema.Color.Blend as Blend
import Hydrogen.Schema.Color.Glow as Glow
import Hydrogen.Schema.Color.CVD as CVD
import Hydrogen.Schema.Color.Contrast as Contrast
import Hydrogen.Schema.Color.Harmony as Harmony
import Hydrogen.Schema.Color.Properties as Properties
import Hydrogen.Schema.Color.Temperature as Temperature
import Hydrogen.Schema.Color.Mood as Mood
import Hydrogen.Schema.Color.WhiteBalance as WhiteBalance
import Hydrogen.Schema.Color.ColorWheels as ColorWheels

-- RGB
type RGB = RGB.RGB
type RGBA = RGB.RGBA
rgb = RGB.rgb
rgba = RGB.rgba
fromChannels = RGB.fromChannels
red = RGB.red
green = RGB.green
blue = RGB.blue
alpha = RGB.alpha
invert = RGB.invert
blend = RGB.blend
add = RGB.add
multiply = RGB.multiply
screen = RGB.screen
toCss = RGB.toLegacyCss
toHex = RGB.toHex
toCssA = RGB.toLegacyCssA
toRGBA = RGB.toRGBA
fromRGBA = RGB.fromRGBA

-- HSL
type HSL = HSL.HSL
hsl = HSL.hsl
fromComponents = HSL.fromComponents
hue = HSL.hue
saturation = HSL.saturation
lightness = HSL.lightness

-- CMYK
type CMYK = CMYK.CMYK
cmyk = CMYK.cmyk
cmykFromComponents = CMYK.cmykFromComponents
cyan = CMYK.cyan
magenta = CMYK.magenta
yellow = CMYK.yellow
key = CMYK.key
cmykToCss = CMYK.cmykToCss

-- LAB
type LAB = LAB.LAB
type LabL = LAB.LabL
type LabA = LAB.LabA
type LabB = LAB.LabB
lab = LAB.lab
labL = LAB.labL
labA = LAB.labA
labB = LAB.labB
deltaE = LAB.deltaE

-- LCH
type LCH = LCH.LCH
type LchL = LCH.LchL
type LchC = LCH.LchC
type LchH = LCH.LchH
lch = LCH.lch
lchL = LCH.lchL
lchC = LCH.lchC
lchH = LCH.lchH

-- XYZ
type XYZ = XYZ.XYZ
type XComponent = XYZ.XComponent
type YComponent = XYZ.YComponent
type ZComponent = XYZ.ZComponent
xyz = XYZ.xyz
xComponent = XYZ.xComponent
yComponent = XYZ.yComponent
zComponent = XYZ.zComponent
d65White = XYZ.d65White

-- Conversions
hslToRgb = Conversion.hslToRgb
rgbToHsl = Conversion.rgbToHsl
rgbToCmyk = Conversion.rgbToCmyk
cmykToRgb = Conversion.cmykToRgb
rgbToHex = Conversion.rgbToHex
hexToRgb = Conversion.hexToRgb
rgbToXyz = Conversion.rgbToXyz
xyzToRgb = Conversion.xyzToRgb
xyzToLab = Conversion.xyzToLab
labToXyz = Conversion.labToXyz
rgbToLab = Conversion.rgbToLab
labToRgb = Conversion.labToRgb
rgbToLch = Conversion.rgbToLch
lchToRgb = Conversion.lchToRgb
kelvinToRgb = Conversion.kelvinToRgb
rgbToRecord = Conversion.rgbToRecord
rgbFromRecord = Conversion.rgbFromRecord
hslToRecord = Conversion.hslToRecord
hslFromRecord = Conversion.hslFromRecord
cmykToRecord = Conversion.cmykToRecord
cmykFromRecord = Conversion.cmykFromRecord
labToRecord = Conversion.labToRecord
labFromRecord = Conversion.labFromRecord
lchToRecord = Conversion.lchToRecord
lchFromRecord = Conversion.lchFromRecord
xyzToRecord = Conversion.xyzToRecord
xyzFromRecord = Conversion.xyzFromRecord

-- Blend
type BlendMode = Blend.BlendMode
blendRGBA = Blend.blendRGBA
blendChannel = Blend.blendChannel
type CompositeOp = Blend.CompositeOp
composite = Blend.composite
mixRGB = Blend.mixRGB
mixRGBA = Blend.mixRGBA
lerpRGB = Blend.lerpRGB
blendModeToCss = Blend.blendModeToCss
compositeOpToCss = Blend.compositeOpToCss

-- Glow
type Glow = Glow.Glow
glow = Glow.glow
glowFromRecord = Glow.glowFromRecord
glowColor = Glow.glowColor
glowIntensity = Glow.glowIntensity
glowSpread = Glow.glowSpread
glowToRecord = Glow.glowToRecord
glowToRgb = Glow.glowToRgb
glowToCss = Glow.glowToCss
withColor = Glow.withColor
withIntensity = Glow.withIntensity
withSpread = Glow.withSpread
warmGlow = Glow.warmGlow
coolGlow = Glow.coolGlow
neutralGlow = Glow.neutralGlow

-- CVD
type CVDType = CVD.CVDType
cvdPrevalence = CVD.cvdPrevalence
type AccessibilityIssue = CVD.AccessibilityIssue
type AccessibilityReport = CVD.AccessibilityReport
simulateCVD = CVD.simulateCVD
isDistinguishable = CVD.isDistinguishable
checkAccessibility = CVD.checkAccessibility
suggestAccessibleAlternative = CVD.suggestAccessibleAlternative
ensureAccessible = CVD.ensureAccessible
cvdSafeContrast = CVD.cvdSafeContrast

-- Contrast
type WCAGLevel = Contrast.WCAGLevel
type Contrast = Contrast.Contrast
contrastRatio = Contrast.contrastRatio
contrastBetween = Contrast.contrastBetween
meetsWCAG = Contrast.meetsWCAG
suggestForeground = Contrast.suggestForeground
luminanceRGB = Contrast.luminanceRGB
relativeLuminance = Contrast.relativeLuminance

-- Harmony
type Harmony = Harmony.Harmony
type HarmonyConfig = Harmony.HarmonyConfig
generateHarmony = Harmony.generateHarmony

-- Properties
colorfulness = Properties.colorfulness
chroma = Properties.chroma
brightness = Properties.brightness
value = Properties.value
perceivedLightness = Properties.perceivedLightness
labLightness = Properties.labLightness

-- Temperature
type Temperature = Temperature.Temperature
temperatureFromHSL = Temperature.temperatureFromHSL
kelvin = Temperature.kelvin

-- Mood
type Mood = Mood.Mood
moodFromHSL = Mood.moodFromHSL
moodDescription = Mood.moodDescription

-- WhiteBalance
type WhiteBalance = WhiteBalance.WhiteBalance
type Preset = WhiteBalance.Preset
whiteBalance = WhiteBalance.whiteBalance
fromPreset = WhiteBalance.fromPreset
temperature = WhiteBalance.temperature
tint = WhiteBalance.tint
whiteBalanceApplyToRgb = WhiteBalance.applyToRgb  -- Renamed to avoid conflict
withTemperature = WhiteBalance.withTemperature
withTint = WhiteBalance.withTint

-- ColorWheels
type ColorWheels = ColorWheels.ColorWheels
type WheelAdjustment = ColorWheels.WheelAdjustment
colorWheels = ColorWheels.colorWheels
neutralWheels = ColorWheels.neutralWheels
wheelAdjustment = ColorWheels.wheelAdjustment
neutralAdjustment = ColorWheels.neutralAdjustment
lift = ColorWheels.lift
gamma = ColorWheels.gamma
gain = ColorWheels.gain
colorWheelsApplyToRgb = ColorWheels.applyToRgb  -- Renamed to avoid conflict
withLift = ColorWheels.withLift
withGamma = ColorWheels.withGamma
withGain = ColorWheels.withGain
