-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // dimension // device
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Device-dependent units - measurements that depend on display hardware.
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
-- |
-- | ## Conversion Requires Context
-- |
-- | To convert between device units and physical units, you need:
-- | - PPI (pixels per inch) of the display
-- | - Device pixel ratio (for HiDPI/Retina displays)
-- |
-- | See `Dimension.Context` for conversion functions.

module Hydrogen.Schema.Dimension.Device
  ( -- * Core Types
    Pixel(Pixel)
  , DevicePixel(DevicePixel)
  , CSSPixel(CSSPixel)
  , DensityIndependentPixel(DensityIndependentPixel)
  , ScaledPixel(ScaledPixel)
  
  -- * Display Properties
  , PixelsPerInch(PixelsPerInch)
  , DevicePixelRatio(DevicePixelRatio)
  
  -- * Constructors
  , px
  , devicePx
  , cssPx
  , dp
  , sp
  , ppi
  , dpr
  
  -- * Operations
  , addPx
  , subtractPx
  , scalePx
  , negatePx
  , absPx
  
  -- * Common Display Densities
  , ppiStandard
  , ppiRetina
  , ppiRetinaHD
  , ppi4K
  , ppiPrint300
  , ppiPrint600
  
  -- * Accessors
  , unwrapPixel
  , unwrapDevicePixel
  , unwrapCSSPixel
  , unwrapDp
  , unwrapSp
  , unwrapPpi
  , unwrapDpr
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Ring
  , class Semiring
  , class Show
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (<>)
  )

import Hydrogen.Math.Core as Math

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // pixel types
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // display properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Pixels per inch - the density of a display
-- | This is what bridges device pixels to physical inches
-- | Also known as DPI (dots per inch) in print contexts
newtype PixelsPerInch = PixelsPerInch Number

derive instance eqPixelsPerInch :: Eq PixelsPerInch
derive instance ordPixelsPerInch :: Ord PixelsPerInch

instance showPixelsPerInch :: Show PixelsPerInch where
  show (PixelsPerInch n) = show n <> " PPI"

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a Pixel value
px :: Number -> Pixel
px = Pixel

-- | Create a DevicePixel value
devicePx :: Number -> DevicePixel
devicePx = DevicePixel

-- | Create a CSSPixel value
cssPx :: Number -> CSSPixel
cssPx = CSSPixel

-- | Create a DensityIndependentPixel value
dp :: Number -> DensityIndependentPixel
dp = DensityIndependentPixel

-- | Create a ScaledPixel value
sp :: Number -> ScaledPixel
sp = ScaledPixel

-- | Create a PixelsPerInch value
ppi :: Number -> PixelsPerInch
ppi = PixelsPerInch

-- | Create a DevicePixelRatio value
dpr :: Number -> DevicePixelRatio
dpr = DevicePixelRatio

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add two Pixel values
addPx :: Pixel -> Pixel -> Pixel
addPx (Pixel a) (Pixel b) = Pixel (a + b)

-- | Subtract two Pixel values
subtractPx :: Pixel -> Pixel -> Pixel
subtractPx (Pixel a) (Pixel b) = Pixel (a - b)

-- | Scale a Pixel value by a dimensionless factor
scalePx :: Number -> Pixel -> Pixel
scalePx factor (Pixel n) = Pixel (n * factor)

-- | Negate a Pixel value
negatePx :: Pixel -> Pixel
negatePx (Pixel n) = Pixel (negate n)

-- | Absolute value of a Pixel
absPx :: Pixel -> Pixel
absPx (Pixel n) = Pixel (Math.abs n)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // common display densities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Standard desktop monitor (96 PPI)
-- | This is the CSS reference density
ppiStandard :: PixelsPerInch
ppiStandard = PixelsPerInch 96.0

-- | Apple Retina display (~220-230 PPI)
-- | iPhone 4 was 326 PPI, MacBook Pro is ~220 PPI
ppiRetina :: PixelsPerInch
ppiRetina = PixelsPerInch 220.0

-- | Apple Retina HD display (~326-458 PPI)
-- | iPhone Plus/Max models
ppiRetinaHD :: PixelsPerInch
ppiRetinaHD = PixelsPerInch 326.0

-- | 4K UHD at typical monitor sizes (~163-185 PPI)
ppi4K :: PixelsPerInch
ppi4K = PixelsPerInch 163.0

-- | Print quality at 300 DPI
ppiPrint300 :: PixelsPerInch
ppiPrint300 = PixelsPerInch 300.0

-- | High quality print at 600 DPI
ppiPrint600 :: PixelsPerInch
ppiPrint600 = PixelsPerInch 600.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number from a Pixel
unwrapPixel :: Pixel -> Number
unwrapPixel (Pixel n) = n

-- | Extract the raw Number from a DevicePixel
unwrapDevicePixel :: DevicePixel -> Number
unwrapDevicePixel (DevicePixel n) = n

-- | Extract the raw Number from a CSSPixel
unwrapCSSPixel :: CSSPixel -> Number
unwrapCSSPixel (CSSPixel n) = n

-- | Extract the raw Number from a DensityIndependentPixel
unwrapDp :: DensityIndependentPixel -> Number
unwrapDp (DensityIndependentPixel n) = n

-- | Extract the raw Number from a ScaledPixel
unwrapSp :: ScaledPixel -> Number
unwrapSp (ScaledPixel n) = n

-- | Extract the raw Number from a PixelsPerInch
unwrapPpi :: PixelsPerInch -> Number
unwrapPpi (PixelsPerInch n) = n

-- | Extract the raw Number from a DevicePixelRatio
unwrapDpr :: DevicePixelRatio -> Number
unwrapDpr (DevicePixelRatio n) = n
