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
  , toLegacyCss
  , toHex
  , toLegacyCssA
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
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.Opacity as Op
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.Cyan as Cy
import Hydrogen.Schema.Color.Magenta as Mg
import Hydrogen.Schema.Color.Yellow as Yw
import Hydrogen.Schema.Color.Key as Key
import Hydrogen.Schema.Color.Kelvin as Kelvin
import Hydrogen.Schema.Color.Luminance as Luminance
import Data.Maybe (Maybe)
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

rgb :: Int -> Int -> Int -> RGB
rgb = RGB.rgb

rgba :: Int -> Int -> Int -> Int -> RGBA
rgba = RGB.rgba

fromChannels :: Ch.Channel -> Ch.Channel -> Ch.Channel -> RGB
fromChannels = RGB.fromChannels

red :: RGB -> Ch.Channel
red = RGB.red

green :: RGB -> Ch.Channel
green = RGB.green

blue :: RGB -> Ch.Channel
blue = RGB.blue

alpha :: RGBA -> Op.Opacity
alpha = RGB.alpha

invert :: RGB -> RGB
invert = RGB.invert

blend :: Number -> RGB -> RGB -> RGB
blend = RGB.blend

add :: RGB -> RGB -> RGB
add = RGB.add

multiply :: RGB -> RGB -> RGB
multiply = RGB.multiply

screen :: RGB -> RGB -> RGB
screen = RGB.screen

toLegacyCss :: RGB -> String
toLegacyCss = RGB.toLegacyCss

toHex :: RGB -> String
toHex = RGB.toHex

toLegacyCssA :: RGBA -> String
toLegacyCssA = RGB.toLegacyCssA

toRGBA :: RGB -> RGBA
toRGBA = RGB.toRGBA

fromRGBA :: RGBA -> RGB
fromRGBA = RGB.fromRGBA

-- HSL
type HSL = HSL.HSL

hsl :: Int -> Int -> Int -> HSL
hsl = HSL.hsl

fromComponents :: Hue.Hue -> Sat.Saturation -> Light.Lightness -> HSL
fromComponents = HSL.fromComponents

hue :: HSL -> Hue.Hue
hue = HSL.hue

saturation :: HSL -> Sat.Saturation
saturation = HSL.saturation

lightness :: HSL -> Light.Lightness
lightness = HSL.lightness

-- CMYK
type CMYK = CMYK.CMYK

cmyk :: Int -> Int -> Int -> Int -> CMYK
cmyk = CMYK.cmyk

cmykFromComponents :: Cy.Cyan -> Mg.Magenta -> Yw.Yellow -> Key.Key -> CMYK
cmykFromComponents = CMYK.cmykFromComponents

cyan :: CMYK -> Cy.Cyan
cyan = CMYK.cyan

magenta :: CMYK -> Mg.Magenta
magenta = CMYK.magenta

yellow :: CMYK -> Yw.Yellow
yellow = CMYK.yellow

key :: CMYK -> Key.Key
key = CMYK.key

cmykToCss :: CMYK -> String
cmykToCss = CMYK.cmykToCss

-- LAB
type LAB = LAB.LAB
type LabL = LAB.LabL
type LabA = LAB.LabA
type LabB = LAB.LabB

lab :: Number -> Number -> Number -> LAB
lab = LAB.lab

labL :: LAB -> LabL
labL = LAB.labL

labA :: LAB -> LabA
labA = LAB.labA

labB :: LAB -> LabB
labB = LAB.labB

deltaE :: LAB -> LAB -> Number
deltaE = LAB.deltaE

-- LCH
type LCH = LCH.LCH
type LchL = LCH.LchL
type LchC = LCH.LchC
type LchH = LCH.LchH

lch :: Number -> Number -> Number -> LCH
lch = LCH.lch

lchL :: LCH -> LchL
lchL = LCH.lchL

lchC :: LCH -> LchC
lchC = LCH.lchC

lchH :: LCH -> LchH
lchH = LCH.lchH

-- XYZ
type XYZ = XYZ.XYZ
type XComponent = XYZ.XComponent
type YComponent = XYZ.YComponent
type ZComponent = XYZ.ZComponent

xyz :: Number -> Number -> Number -> XYZ
xyz = XYZ.xyz

xComponent :: XYZ -> XComponent
xComponent = XYZ.xComponent

yComponent :: XYZ -> YComponent
yComponent = XYZ.yComponent

zComponent :: XYZ -> ZComponent
zComponent = XYZ.zComponent

d65White :: XYZ
d65White = XYZ.d65White

-- Conversions
hslToRgb :: HSL -> RGB
hslToRgb = Conversion.hslToRgb

rgbToHsl :: RGB -> HSL
rgbToHsl = Conversion.rgbToHsl

rgbToCmyk :: RGB -> CMYK
rgbToCmyk = Conversion.rgbToCmyk

cmykToRgb :: CMYK -> RGB
cmykToRgb = Conversion.cmykToRgb

rgbToHex :: RGB -> String
rgbToHex = Conversion.rgbToHex

hexToRgb :: String -> RGB
hexToRgb = Conversion.hexToRgb

rgbToXyz :: RGB -> XYZ
rgbToXyz = Conversion.rgbToXyz

xyzToRgb :: XYZ -> RGB
xyzToRgb = Conversion.xyzToRgb

xyzToLab :: XYZ -> LAB
xyzToLab = Conversion.xyzToLab

labToXyz :: LAB -> XYZ
labToXyz = Conversion.labToXyz

rgbToLab :: RGB -> LAB
rgbToLab = Conversion.rgbToLab

labToRgb :: LAB -> RGB
labToRgb = Conversion.labToRgb

rgbToLch :: RGB -> LCH
rgbToLch = Conversion.rgbToLch

lchToRgb :: LCH -> RGB
lchToRgb = Conversion.lchToRgb

kelvinToRgb :: Kelvin.Kelvin -> RGB
kelvinToRgb = Conversion.kelvinToRgb

rgbToRecord :: RGB -> { r :: Int, g :: Int, b :: Int }
rgbToRecord = Conversion.rgbToRecord

rgbFromRecord :: { r :: Int, g :: Int, b :: Int } -> RGB
rgbFromRecord = Conversion.rgbFromRecord

hslToRecord :: HSL -> { h :: Int, s :: Int, l :: Int }
hslToRecord = Conversion.hslToRecord

hslFromRecord :: { h :: Int, s :: Int, l :: Int } -> HSL
hslFromRecord = Conversion.hslFromRecord

cmykToRecord :: CMYK -> { c :: Int, m :: Int, y :: Int, k :: Int }
cmykToRecord = Conversion.cmykToRecord

cmykFromRecord :: { c :: Int, m :: Int, y :: Int, k :: Int } -> CMYK
cmykFromRecord = Conversion.cmykFromRecord

labToRecord :: LAB -> { l :: Number, a :: Number, b :: Number }
labToRecord = Conversion.labToRecord

labFromRecord :: { l :: Number, a :: Number, b :: Number } -> LAB
labFromRecord = Conversion.labFromRecord

lchToRecord :: LCH -> { l :: Number, c :: Number, h :: Number }
lchToRecord = Conversion.lchToRecord

lchFromRecord :: { l :: Number, c :: Number, h :: Number } -> LCH
lchFromRecord = Conversion.lchFromRecord

xyzToRecord :: XYZ -> { x :: Number, y :: Number, z :: Number }
xyzToRecord = Conversion.xyzToRecord

xyzFromRecord :: { x :: Number, y :: Number, z :: Number } -> XYZ
xyzFromRecord = Conversion.xyzFromRecord

-- Blend
type BlendMode = Blend.BlendMode
type CompositeOp = Blend.CompositeOp

blendRGBA :: BlendMode -> RGBA -> RGBA -> RGBA
blendRGBA = Blend.blendRGBA

blendChannel :: BlendMode -> Int -> Int -> Int
blendChannel = Blend.blendChannel

composite :: CompositeOp -> RGBA -> RGBA -> RGBA
composite = Blend.composite

mixRGB :: Number -> RGB -> RGB -> RGB
mixRGB = Blend.mixRGB

mixRGBA :: Number -> RGBA -> RGBA -> RGBA
mixRGBA = Blend.mixRGBA

lerpRGB :: Number -> RGB -> RGB -> RGB
lerpRGB = Blend.lerpRGB

blendModeToCss :: BlendMode -> String
blendModeToCss = Blend.blendModeToCss

compositeOpToCss :: CompositeOp -> String
compositeOpToCss = Blend.compositeOpToCss

-- Glow
type Glow = Glow.Glow

glow :: Int -> Number -> Number -> Glow
glow = Glow.glow

glowFromRecord :: { color :: Int, intensity :: Number, spread :: Number } -> Glow
glowFromRecord = Glow.glowFromRecord

glowColor :: Glow -> Kelvin.Kelvin
glowColor = Glow.glowColor

glowIntensity :: Glow -> Luminance.Luminance
glowIntensity = Glow.glowIntensity

glowSpread :: Glow -> Number
glowSpread = Glow.glowSpread

glowToRecord :: Glow -> { color :: Int, intensity :: Number, spread :: Number }
glowToRecord = Glow.glowToRecord

glowToRgb :: Glow -> RGB
glowToRgb = Glow.glowToRgb

glowToCss :: Glow -> String
glowToCss = Glow.glowToCss

withColor :: Kelvin.Kelvin -> Glow -> Glow
withColor = Glow.withColor

withIntensity :: Luminance.Luminance -> Glow -> Glow
withIntensity = Glow.withIntensity

withSpread :: Number -> Glow -> Glow
withSpread = Glow.withSpread

warmGlow :: Number -> Number -> Glow
warmGlow = Glow.warmGlow

coolGlow :: Number -> Number -> Glow
coolGlow = Glow.coolGlow

neutralGlow :: Number -> Number -> Glow
neutralGlow = Glow.neutralGlow

-- CVD
type CVDType = CVD.CVDType
type AccessibilityIssue = CVD.AccessibilityIssue
type AccessibilityReport = CVD.AccessibilityReport

cvdPrevalence :: CVDType -> { males :: Number, females :: Number }
cvdPrevalence = CVD.cvdPrevalence

simulateCVD :: CVDType -> RGB -> RGB
simulateCVD = CVD.simulateCVD

isDistinguishable :: CVDType -> RGB -> RGB -> Boolean
isDistinguishable = CVD.isDistinguishable

checkAccessibility :: RGB -> RGB -> AccessibilityReport
checkAccessibility = CVD.checkAccessibility

suggestAccessibleAlternative :: RGB -> RGB -> Maybe RGB
suggestAccessibleAlternative = CVD.suggestAccessibleAlternative

ensureAccessible :: RGB -> RGB -> RGB
ensureAccessible = CVD.ensureAccessible

cvdSafeContrast :: RGB -> RGB -> Number
cvdSafeContrast = CVD.cvdSafeContrast

-- Contrast
type WCAGLevel = Contrast.WCAGLevel
type Contrast = Contrast.Contrast

contrastRatio :: RGB -> RGB -> Number
contrastRatio = Contrast.contrastRatio

contrastBetween :: RGB -> RGB -> Contrast
contrastBetween = Contrast.contrastBetween

meetsWCAG :: WCAGLevel -> RGB -> RGB -> Boolean
meetsWCAG = Contrast.meetsWCAG

suggestForeground :: RGB -> RGB
suggestForeground = Contrast.suggestForeground

luminanceRGB :: RGB -> Number
luminanceRGB = Contrast.luminanceRGB

relativeLuminance :: RGB -> Number
relativeLuminance = Contrast.relativeLuminance

-- Harmony
type Harmony = Harmony.Harmony
type HarmonyConfig = Harmony.HarmonyConfig

generateHarmony :: HarmonyConfig -> Array HSL
generateHarmony = Harmony.generateHarmony

-- Properties
colorfulness :: HSL -> Number
colorfulness = Properties.colorfulness

chroma :: HSL -> Number
chroma = Properties.chroma

brightness :: RGB -> Number
brightness = Properties.brightness

value :: RGB -> Number
value = Properties.value

perceivedLightness :: RGB -> Number
perceivedLightness = Properties.perceivedLightness

labLightness :: RGB -> Number
labLightness = Properties.labLightness

-- Temperature
type Temperature = Temperature.Temperature

temperatureFromHSL :: HSL -> Temperature
temperatureFromHSL = Temperature.temperatureFromHSL

kelvin :: Int -> Temperature
kelvin = Temperature.kelvin

-- Mood
type Mood = Mood.Mood

moodFromHSL :: HSL -> Mood
moodFromHSL = Mood.moodFromHSL

moodDescription :: Mood -> String
moodDescription = Mood.moodDescription

-- WhiteBalance
type WhiteBalance = WhiteBalance.WhiteBalance
type Preset = WhiteBalance.Preset

whiteBalance :: Int -> Int -> WhiteBalance
whiteBalance = WhiteBalance.whiteBalance

fromPreset :: Preset -> WhiteBalance
fromPreset = WhiteBalance.fromPreset

temperature :: WhiteBalance -> Int
temperature = WhiteBalance.temperature

tint :: WhiteBalance -> Int
tint = WhiteBalance.tint

whiteBalanceApplyToRgb :: WhiteBalance -> RGB -> RGB
whiteBalanceApplyToRgb = WhiteBalance.applyToRgb

withTemperature :: Int -> WhiteBalance -> WhiteBalance
withTemperature = WhiteBalance.withTemperature

withTint :: Int -> WhiteBalance -> WhiteBalance
withTint = WhiteBalance.withTint

-- ColorWheels
type ColorWheels = ColorWheels.ColorWheels
type WheelAdjustment = ColorWheels.WheelAdjustment

colorWheels :: WheelAdjustment -> WheelAdjustment -> WheelAdjustment -> ColorWheels
colorWheels = ColorWheels.colorWheels

neutralWheels :: ColorWheels
neutralWheels = ColorWheels.neutralWheels

wheelAdjustment :: Number -> Number -> Number -> WheelAdjustment
wheelAdjustment = ColorWheels.wheelAdjustment

neutralAdjustment :: WheelAdjustment
neutralAdjustment = ColorWheels.neutralAdjustment

lift :: ColorWheels -> WheelAdjustment
lift = ColorWheels.lift

gamma :: ColorWheels -> WheelAdjustment
gamma = ColorWheels.gamma

gain :: ColorWheels -> WheelAdjustment
gain = ColorWheels.gain

colorWheelsApplyToRgb :: ColorWheels -> RGB -> RGB
colorWheelsApplyToRgb = ColorWheels.applyToRgb

withLift :: WheelAdjustment -> ColorWheels -> ColorWheels
withLift = ColorWheels.withLift

withGamma :: WheelAdjustment -> ColorWheels -> ColorWheels
withGamma = ColorWheels.withGamma

withGain :: WheelAdjustment -> ColorWheels -> ColorWheels
withGain = ColorWheels.withGain
