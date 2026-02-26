-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // motion // effects // stylize
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stylize effect enums for motion graphics.
-- |
-- | Defines scanlines direction, RGB split blend modes, pixel sort options,
-- | halftone color modes, dither methods, and color channel selections.

module Hydrogen.Schema.Motion.Effects.Stylize
  ( -- * Scanlines Direction
    ScanlinesDirection(..)
  , allScanlinesDirections
  , scanlinesDirectionToString
  , scanlinesDirectionFromString
  
    -- * RGB Split Blend Mode
  , RGBSplitBlendMode(..)
  , allRGBSplitBlendModes
  , rgbSplitBlendModeToString
  , rgbSplitBlendModeFromString
  
    -- * Pixel Sort Direction
  , PixelSortDirection(..)
  , allPixelSortDirections
  , pixelSortDirectionToString
  , pixelSortDirectionFromString
  
    -- * Sort By Criterion
  , SortByCriterion(..)
  , allSortByCriteria
  , sortByCriterionToString
  , sortByCriterionFromString
  
    -- * Halftone Color Mode
  , HalftoneColorMode(..)
  , allHalftoneColorModes
  , halftoneColorModeToString
  , halftoneColorModeFromString
  
    -- * Dither Method
  , DitherMethod(..)
  , allDitherMethods
  , ditherMethodToString
  , ditherMethodFromString
  
    -- * Dither Matrix Size
  , DitherMatrixSize(..)
  , allDitherMatrixSizes
  , ditherMatrixSizeToString
  , ditherMatrixSizeFromString
  
    -- * Effect Color Channel
  , EffectColorChannel(..)
  , allEffectColorChannels
  , effectColorChannelToString
  , effectColorChannelFromString
  
    -- * HSL Channel
  , HSLChannel(..)
  , allHSLChannels
  , hslChannelToString
  , hslChannelFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // scanlines // direction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Direction of scanlines effect.
data ScanlinesDirection
  = SDHorizontal  -- ^ Horizontal scanlines
  | SDVertical    -- ^ Vertical scanlines

derive instance eqScanlinesDirection :: Eq ScanlinesDirection
derive instance ordScanlinesDirection :: Ord ScanlinesDirection

instance showScanlinesDirection :: Show ScanlinesDirection where
  show SDHorizontal = "SDHorizontal"
  show SDVertical = "SDVertical"

-- | All scanlines directions for enumeration
allScanlinesDirections :: Array ScanlinesDirection
allScanlinesDirections = [ SDHorizontal, SDVertical ]

scanlinesDirectionToString :: ScanlinesDirection -> String
scanlinesDirectionToString SDHorizontal = "horizontal"
scanlinesDirectionToString SDVertical = "vertical"

scanlinesDirectionFromString :: String -> Maybe ScanlinesDirection
scanlinesDirectionFromString "horizontal" = Just SDHorizontal
scanlinesDirectionFromString "vertical" = Just SDVertical
scanlinesDirectionFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // rgb // split // blend // mode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Blend mode for RGB split effect.
data RGBSplitBlendMode
  = RSBMScreen  -- ^ Screen blend
  | RSBMAdd     -- ^ Additive blend
  | RSBMNormal  -- ^ Normal blend

derive instance eqRGBSplitBlendMode :: Eq RGBSplitBlendMode
derive instance ordRGBSplitBlendMode :: Ord RGBSplitBlendMode

instance showRGBSplitBlendMode :: Show RGBSplitBlendMode where
  show RSBMScreen = "RSBMScreen"
  show RSBMAdd = "RSBMAdd"
  show RSBMNormal = "RSBMNormal"

-- | All RGB split blend modes for enumeration
allRGBSplitBlendModes :: Array RGBSplitBlendMode
allRGBSplitBlendModes = [ RSBMScreen, RSBMAdd, RSBMNormal ]

rgbSplitBlendModeToString :: RGBSplitBlendMode -> String
rgbSplitBlendModeToString RSBMScreen = "screen"
rgbSplitBlendModeToString RSBMAdd = "add"
rgbSplitBlendModeToString RSBMNormal = "normal"

rgbSplitBlendModeFromString :: String -> Maybe RGBSplitBlendMode
rgbSplitBlendModeFromString "screen" = Just RSBMScreen
rgbSplitBlendModeFromString "add" = Just RSBMAdd
rgbSplitBlendModeFromString "normal" = Just RSBMNormal
rgbSplitBlendModeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // pixel // sort // direction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Direction of pixel sorting.
data PixelSortDirection
  = PSDHorizontal  -- ^ Sort horizontally
  | PSDVertical    -- ^ Sort vertically

derive instance eqPixelSortDirection :: Eq PixelSortDirection
derive instance ordPixelSortDirection :: Ord PixelSortDirection

instance showPixelSortDirection :: Show PixelSortDirection where
  show PSDHorizontal = "PSDHorizontal"
  show PSDVertical = "PSDVertical"

-- | All pixel sort directions for enumeration
allPixelSortDirections :: Array PixelSortDirection
allPixelSortDirections = [ PSDHorizontal, PSDVertical ]

pixelSortDirectionToString :: PixelSortDirection -> String
pixelSortDirectionToString PSDHorizontal = "horizontal"
pixelSortDirectionToString PSDVertical = "vertical"

pixelSortDirectionFromString :: String -> Maybe PixelSortDirection
pixelSortDirectionFromString "horizontal" = Just PSDHorizontal
pixelSortDirectionFromString "vertical" = Just PSDVertical
pixelSortDirectionFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // sort // by // criterion
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Criterion for sorting pixels.
data SortByCriterion
  = SBCSaturation  -- ^ Sort by saturation
  | SBCBrightness  -- ^ Sort by brightness
  | SBCHue         -- ^ Sort by hue

derive instance eqSortByCriterion :: Eq SortByCriterion
derive instance ordSortByCriterion :: Ord SortByCriterion

instance showSortByCriterion :: Show SortByCriterion where
  show SBCSaturation = "SBCSaturation"
  show SBCBrightness = "SBCBrightness"
  show SBCHue = "SBCHue"

-- | All sort by criteria for enumeration
allSortByCriteria :: Array SortByCriterion
allSortByCriteria = [ SBCSaturation, SBCBrightness, SBCHue ]

sortByCriterionToString :: SortByCriterion -> String
sortByCriterionToString SBCSaturation = "saturation"
sortByCriterionToString SBCBrightness = "brightness"
sortByCriterionToString SBCHue = "hue"

sortByCriterionFromString :: String -> Maybe SortByCriterion
sortByCriterionFromString "saturation" = Just SBCSaturation
sortByCriterionFromString "brightness" = Just SBCBrightness
sortByCriterionFromString "hue" = Just SBCHue
sortByCriterionFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // halftone // color // mode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color mode for halftone effect.
data HalftoneColorMode
  = HCMGrayscale  -- ^ Grayscale halftone
  | HCMRGB        -- ^ RGB halftone
  | HCMCMYK       -- ^ CMYK halftone

derive instance eqHalftoneColorMode :: Eq HalftoneColorMode
derive instance ordHalftoneColorMode :: Ord HalftoneColorMode

instance showHalftoneColorMode :: Show HalftoneColorMode where
  show HCMGrayscale = "HCMGrayscale"
  show HCMRGB = "HCMRGB"
  show HCMCMYK = "HCMCMYK"

-- | All halftone color modes for enumeration
allHalftoneColorModes :: Array HalftoneColorMode
allHalftoneColorModes = [ HCMGrayscale, HCMRGB, HCMCMYK ]

halftoneColorModeToString :: HalftoneColorMode -> String
halftoneColorModeToString HCMGrayscale = "grayscale"
halftoneColorModeToString HCMRGB = "rgb"
halftoneColorModeToString HCMCMYK = "cmyk"

halftoneColorModeFromString :: String -> Maybe HalftoneColorMode
halftoneColorModeFromString "grayscale" = Just HCMGrayscale
halftoneColorModeFromString "rgb" = Just HCMRGB
halftoneColorModeFromString "cmyk" = Just HCMCMYK
halftoneColorModeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // dither // method
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dithering method.
data DitherMethod
  = DMOrdered         -- ^ Ordered (Bayer) dither
  | DMFloydSteinberg  -- ^ Floyd-Steinberg error diffusion
  | DMAtkinson        -- ^ Atkinson dither

derive instance eqDitherMethod :: Eq DitherMethod
derive instance ordDitherMethod :: Ord DitherMethod

instance showDitherMethod :: Show DitherMethod where
  show DMOrdered = "DMOrdered"
  show DMFloydSteinberg = "DMFloydSteinberg"
  show DMAtkinson = "DMAtkinson"

-- | All dither methods for enumeration
allDitherMethods :: Array DitherMethod
allDitherMethods = [ DMOrdered, DMFloydSteinberg, DMAtkinson ]

ditherMethodToString :: DitherMethod -> String
ditherMethodToString DMOrdered = "ordered"
ditherMethodToString DMFloydSteinberg = "floyd-steinberg"
ditherMethodToString DMAtkinson = "atkinson"

ditherMethodFromString :: String -> Maybe DitherMethod
ditherMethodFromString "ordered" = Just DMOrdered
ditherMethodFromString "floyd-steinberg" = Just DMFloydSteinberg
ditherMethodFromString "atkinson" = Just DMAtkinson
ditherMethodFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // dither // matrix // size
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Size of dither matrix.
data DitherMatrixSize
  = DMS2x2  -- ^ 2×2 matrix
  | DMS4x4  -- ^ 4×4 matrix
  | DMS8x8  -- ^ 8×8 matrix

derive instance eqDitherMatrixSize :: Eq DitherMatrixSize
derive instance ordDitherMatrixSize :: Ord DitherMatrixSize

instance showDitherMatrixSize :: Show DitherMatrixSize where
  show DMS2x2 = "DMS2x2"
  show DMS4x4 = "DMS4x4"
  show DMS8x8 = "DMS8x8"

-- | All dither matrix sizes for enumeration
allDitherMatrixSizes :: Array DitherMatrixSize
allDitherMatrixSizes = [ DMS2x2, DMS4x4, DMS8x8 ]

ditherMatrixSizeToString :: DitherMatrixSize -> String
ditherMatrixSizeToString DMS2x2 = "2x2"
ditherMatrixSizeToString DMS4x4 = "4x4"
ditherMatrixSizeToString DMS8x8 = "8x8"

ditherMatrixSizeFromString :: String -> Maybe DitherMatrixSize
ditherMatrixSizeFromString "2x2" = Just DMS2x2
ditherMatrixSizeFromString "4x4" = Just DMS4x4
ditherMatrixSizeFromString "8x8" = Just DMS8x8
ditherMatrixSizeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // effect // color // channel
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color channel selection for effects.
data EffectColorChannel
  = ECCRGB    -- ^ All RGB channels
  | ECCRed    -- ^ Red channel only
  | ECCGreen  -- ^ Green channel only
  | ECCBlue   -- ^ Blue channel only
  | ECCAlpha  -- ^ Alpha channel only

derive instance eqEffectColorChannel :: Eq EffectColorChannel
derive instance ordEffectColorChannel :: Ord EffectColorChannel

instance showEffectColorChannel :: Show EffectColorChannel where
  show ECCRGB = "ECCRGB"
  show ECCRed = "ECCRed"
  show ECCGreen = "ECCGreen"
  show ECCBlue = "ECCBlue"
  show ECCAlpha = "ECCAlpha"

-- | All effect color channels for enumeration
allEffectColorChannels :: Array EffectColorChannel
allEffectColorChannels = [ ECCRGB, ECCRed, ECCGreen, ECCBlue, ECCAlpha ]

effectColorChannelToString :: EffectColorChannel -> String
effectColorChannelToString ECCRGB = "rgb"
effectColorChannelToString ECCRed = "red"
effectColorChannelToString ECCGreen = "green"
effectColorChannelToString ECCBlue = "blue"
effectColorChannelToString ECCAlpha = "alpha"

effectColorChannelFromString :: String -> Maybe EffectColorChannel
effectColorChannelFromString "rgb" = Just ECCRGB
effectColorChannelFromString "red" = Just ECCRed
effectColorChannelFromString "green" = Just ECCGreen
effectColorChannelFromString "blue" = Just ECCBlue
effectColorChannelFromString "alpha" = Just ECCAlpha
effectColorChannelFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // hsl // channel
-- ═══════════════════════════════════════════════════════════════════════════════

-- | HSL channel selection.
data HSLChannel
  = HSLMaster    -- ^ All colors
  | HSLReds      -- ^ Red range
  | HSLYellows   -- ^ Yellow range
  | HSLGreens    -- ^ Green range
  | HSLCyans     -- ^ Cyan range
  | HSLBlues     -- ^ Blue range
  | HSLMagentas  -- ^ Magenta range

derive instance eqHSLChannel :: Eq HSLChannel
derive instance ordHSLChannel :: Ord HSLChannel

instance showHSLChannel :: Show HSLChannel where
  show HSLMaster = "HSLMaster"
  show HSLReds = "HSLReds"
  show HSLYellows = "HSLYellows"
  show HSLGreens = "HSLGreens"
  show HSLCyans = "HSLCyans"
  show HSLBlues = "HSLBlues"
  show HSLMagentas = "HSLMagentas"

-- | All HSL channels for enumeration
allHSLChannels :: Array HSLChannel
allHSLChannels =
  [ HSLMaster
  , HSLReds
  , HSLYellows
  , HSLGreens
  , HSLCyans
  , HSLBlues
  , HSLMagentas
  ]

hslChannelToString :: HSLChannel -> String
hslChannelToString HSLMaster = "master"
hslChannelToString HSLReds = "reds"
hslChannelToString HSLYellows = "yellows"
hslChannelToString HSLGreens = "greens"
hslChannelToString HSLCyans = "cyans"
hslChannelToString HSLBlues = "blues"
hslChannelToString HSLMagentas = "magentas"

hslChannelFromString :: String -> Maybe HSLChannel
hslChannelFromString "master" = Just HSLMaster
hslChannelFromString "reds" = Just HSLReds
hslChannelFromString "yellows" = Just HSLYellows
hslChannelFromString "greens" = Just HSLGreens
hslChannelFromString "cyans" = Just HSLCyans
hslChannelFromString "blues" = Just HSLBlues
hslChannelFromString "magentas" = Just HSLMagentas
hslChannelFromString _ = Nothing
