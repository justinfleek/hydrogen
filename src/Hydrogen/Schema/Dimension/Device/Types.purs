-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // dimension // device // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core device-dependent unit types.
-- |
-- | A pixel has no inherent physical size. A "1920px" image could be:
-- | - 20 inches wide on a 96 PPI monitor
-- | - 13 inches wide on a 144 PPI laptop
-- | - 200 inches wide on a projector
-- |
-- | ## Unit Distinctions
-- |
-- | - **DevicePixel**: Actual hardware pixels on the display
-- | - **CSSPixel**: Reference pixel at 96 PPI (CSS spec)
-- | - **Pixel**: Generic discrete pixel (context determines meaning)
-- | - **DensityIndependentPixel**: Android dp (1 dp = 1 pixel at 160 PPI)
-- | - **ScaledPixel**: Android sp (like dp but scales with font preference)

module Hydrogen.Schema.Dimension.Device.Types
  ( -- * Pixel Types
    Pixel(Pixel)
  , DevicePixel(DevicePixel)
  , CSSPixel(CSSPixel)
  , DensityIndependentPixel(DensityIndependentPixel)
  , ScaledPixel(ScaledPixel)
  
  -- * Display Properties
  , PixelsPerInch(PixelsPerInch)
  , PixelsPerCentimeter(PixelsPerCentimeter)
  , DevicePixelRatio(DevicePixelRatio)
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Ring
  , class Semiring
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // pixel types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic pixel - a discrete unit on some display
-- | The physical size depends entirely on the display's PPI
newtype Pixel = Pixel Number

derive instance eqPixel :: Eq Pixel
derive instance ordPixel :: Ord Pixel

instance showPixel :: Show Pixel where
  show (Pixel n) = show n <> "px"

instance semiringPixel :: Semiring Pixel where
  add (Pixel a) (Pixel b) = Pixel (a + b)
  zero = Pixel 0.0
  mul (Pixel a) (Pixel b) = Pixel (a * b)
  one = Pixel 1.0

instance ringPixel :: Ring Pixel where
  sub (Pixel a) (Pixel b) = Pixel (a - b)

-- | Device pixel - actual hardware pixel on the display
-- | On a Retina display, 1 CSS pixel = 2 device pixels
newtype DevicePixel = DevicePixel Number

derive instance eqDevicePixel :: Eq DevicePixel
derive instance ordDevicePixel :: Ord DevicePixel

instance showDevicePixel :: Show DevicePixel where
  show (DevicePixel n) = show n <> "dpx"

-- | CSS pixel - reference pixel defined at 96 PPI
-- | This is what web browsers use by default
-- | 1 CSS inch = 96 CSS pixels (regardless of actual display)
newtype CSSPixel = CSSPixel Number

derive instance eqCSSPixel :: Eq CSSPixel
derive instance ordCSSPixel :: Ord CSSPixel

instance showCSSPixel :: Show CSSPixel where
  show (CSSPixel n) = show n <> "px (CSS)"

-- | Density-independent pixel (Android dp)
-- | 1 dp = 1 pixel at 160 PPI (mdpi baseline)
-- | Scales proportionally: at 320 PPI (xhdpi), 1 dp = 2 pixels
newtype DensityIndependentPixel = DensityIndependentPixel Number

derive instance eqDensityIndependentPixel :: Eq DensityIndependentPixel
derive instance ordDensityIndependentPixel :: Ord DensityIndependentPixel

instance showDensityIndependentPixel :: Show DensityIndependentPixel where
  show (DensityIndependentPixel n) = show n <> "dp"

-- | Scaled pixel (Android sp)
-- | Like dp, but also scales with user's font size preference
-- | Used for text to respect accessibility settings
newtype ScaledPixel = ScaledPixel Number

derive instance eqScaledPixel :: Eq ScaledPixel
derive instance ordScaledPixel :: Ord ScaledPixel

instance showScaledPixel :: Show ScaledPixel where
  show (ScaledPixel n) = show n <> "sp"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // display properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pixels per inch - the density of a display
-- | This is what bridges device pixels to physical inches
-- | Also known as DPI (dots per inch) in print contexts
newtype PixelsPerInch = PixelsPerInch Number

derive instance eqPixelsPerInch :: Eq PixelsPerInch
derive instance ordPixelsPerInch :: Ord PixelsPerInch

instance showPixelsPerInch :: Show PixelsPerInch where
  show (PixelsPerInch n) = show n <> " PPI"

-- | Pixels per centimeter - metric equivalent of PPI.
-- |
-- | 1 inch = 2.54 cm, so PPCM = PPI / 2.54
-- | Useful for metric regions and scientific applications.
newtype PixelsPerCentimeter = PixelsPerCentimeter Number

derive instance eqPixelsPerCentimeter :: Eq PixelsPerCentimeter
derive instance ordPixelsPerCentimeter :: Ord PixelsPerCentimeter

instance showPixelsPerCentimeter :: Show PixelsPerCentimeter where
  show (PixelsPerCentimeter n) = show n <> " PPCM"

-- | Device pixel ratio - ratio of device pixels to CSS pixels
-- | Standard displays: 1.0
-- | Retina displays: 2.0
-- | Retina HD: 3.0
-- | Some Android devices: 1.5, 2.5, etc.
newtype DevicePixelRatio = DevicePixelRatio Number

derive instance eqDevicePixelRatio :: Eq DevicePixelRatio
derive instance ordDevicePixelRatio :: Ord DevicePixelRatio

instance showDevicePixelRatio :: Show DevicePixelRatio where
  show (DevicePixelRatio n) = show n <> "x"
