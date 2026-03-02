-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // surface // blend
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blend Modes — Complete Standard blend mode vocabulary.
-- |
-- | ## Design Philosophy
-- |
-- | Blend modes define how layers combine mathematically. Each mode has
-- | a precise formula operating on normalized RGB values [0,1].
-- |
-- | ## Categories (standard organization)
-- |
-- | 1. **Normal**: Normal, Dissolve
-- | 2. **Darken**: Darken, Multiply, Color Burn, Linear Burn, Darker Color
-- | 3. **Lighten**: Lighten, Screen, Color Dodge, Linear Dodge, Lighter Color
-- | 4. **Contrast**: Overlay, Soft Light, Hard Light, Vivid Light, Linear Light, Pin Light, Hard Mix
-- | 5. **Inversion**: Difference, Exclusion, Subtract, Divide
-- | 6. **Component**: Hue, Saturation, Color, Luminosity
-- |
-- | ## Mathematical Definitions
-- |
-- | Let A = base layer, B = blend layer, both in [0,1]:
-- |
-- | - Normal: B
-- | - Multiply: A * B
-- | - Screen: 1 - (1-A)(1-B)
-- | - Overlay: if A < 0.5 then 2*A*B else 1 - 2*(1-A)*(1-B)
-- | - Soft Light: Complex formula using W3C spec
-- | - Difference: |A - B|
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Surface.BlendMode
  ( -- * Blend Mode Type
    BlendMode(BlendNormal, BlendDissolve, BlendDarken, BlendMultiply, BlendColorBurn, BlendLinearBurn, BlendDarkerColor, BlendLighten, BlendScreen, BlendColorDodge, BlendLinearDodge, BlendLighterColor, BlendOverlay, BlendSoftLight, BlendHardLight, BlendVividLight, BlendLinearLight, BlendPinLight, BlendHardMix, BlendDifference, BlendExclusion, BlendSubtract, BlendDivide, BlendHue, BlendSaturation, BlendColor, BlendLuminosity)
  , allBlendModes
  
  -- * Category Groupings
  , BlendCategory(CategoryNormal, CategoryDarken, CategoryLighten, CategoryContrast, CategoryInversion, CategoryComponent)
  , allBlendCategories
  , blendCategory
  , blendModesInCategory
  
  -- * Descriptions
  , blendModeDescription
  , blendModeFormula
  , blendCategoryDescription
  
  -- * CSS Compatibility
  , toCSSBlendMode
  , fromCSSBlendMode
  , isCSSSupported
  
  -- * Queries
  , isDarkeningMode
  , isLighteningMode
  , isContrastMode
  , isInversionMode
  , isComponentMode
  , preservesTransparency
  , isCommutative
  
  -- * Formatting
  , formatBlendModeWithCategory
  , formatBlendModeInfo
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
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // blend // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | All 27 standard blend modes.
-- |
-- | Organized by visual effect category for discoverability.
data BlendMode
  -- Normal group
  = BlendNormal         -- ^ No blending, top layer opaque
  | BlendDissolve       -- ^ Random pixel replacement based on opacity
  
  -- Darken group
  | BlendDarken         -- ^ Min of each channel
  | BlendMultiply       -- ^ A * B, always darkens
  | BlendColorBurn      -- ^ Darkens by increasing contrast
  | BlendLinearBurn     -- ^ A + B - 1, linear darkening
  | BlendDarkerColor    -- ^ Compares luminosity, keeps darker pixel
  
  -- Lighten group  
  | BlendLighten        -- ^ Max of each channel
  | BlendScreen         -- ^ 1 - (1-A)(1-B), always lightens
  | BlendColorDodge     -- ^ Lightens by decreasing contrast
  | BlendLinearDodge    -- ^ A + B, linear lightening (Add)
  | BlendLighterColor   -- ^ Compares luminosity, keeps lighter pixel
  
  -- Contrast group
  | BlendOverlay        -- ^ Multiply darks, Screen lights
  | BlendSoftLight      -- ^ Subtle version of Overlay
  | BlendHardLight      -- ^ Intense version of Overlay
  | BlendVividLight     -- ^ Color Burn darks, Color Dodge lights
  | BlendLinearLight    -- ^ Linear Burn darks, Linear Dodge lights
  | BlendPinLight       -- ^ Darken/Lighten based on blend value
  | BlendHardMix        -- ^ Posterizes to 8 colors
  
  -- Inversion group
  | BlendDifference     -- ^ |A - B|, inverts based on brightness
  | BlendExclusion      -- ^ Similar to Difference, lower contrast
  | BlendSubtract       -- ^ A - B, clamped to 0
  | BlendDivide         -- ^ A / B, can blow out highlights
  
  -- Component group (HSL operations)
  | BlendHue            -- ^ Hue from B, sat/lum from A
  | BlendSaturation     -- ^ Saturation from B, hue/lum from A
  | BlendColor          -- ^ Hue+Sat from B, luminosity from A
  | BlendLuminosity     -- ^ Luminosity from B, hue/sat from A

derive instance eqBlendMode :: Eq BlendMode
derive instance ordBlendMode :: Ord BlendMode

instance showBlendMode :: Show BlendMode where
  show BlendNormal = "Normal"
  show BlendDissolve = "Dissolve"
  show BlendDarken = "Darken"
  show BlendMultiply = "Multiply"
  show BlendColorBurn = "Color Burn"
  show BlendLinearBurn = "Linear Burn"
  show BlendDarkerColor = "Darker Color"
  show BlendLighten = "Lighten"
  show BlendScreen = "Screen"
  show BlendColorDodge = "Color Dodge"
  show BlendLinearDodge = "Linear Dodge (Add)"
  show BlendLighterColor = "Lighter Color"
  show BlendOverlay = "Overlay"
  show BlendSoftLight = "Soft Light"
  show BlendHardLight = "Hard Light"
  show BlendVividLight = "Vivid Light"
  show BlendLinearLight = "Linear Light"
  show BlendPinLight = "Pin Light"
  show BlendHardMix = "Hard Mix"
  show BlendDifference = "Difference"
  show BlendExclusion = "Exclusion"
  show BlendSubtract = "Subtract"
  show BlendDivide = "Divide"
  show BlendHue = "Hue"
  show BlendSaturation = "Saturation"
  show BlendColor = "Color"
  show BlendLuminosity = "Luminosity"

-- | All blend modes in standard menu order.
allBlendModes :: Array BlendMode
allBlendModes =
  [ BlendNormal
  , BlendDissolve
  , BlendDarken
  , BlendMultiply
  , BlendColorBurn
  , BlendLinearBurn
  , BlendDarkerColor
  , BlendLighten
  , BlendScreen
  , BlendColorDodge
  , BlendLinearDodge
  , BlendLighterColor
  , BlendOverlay
  , BlendSoftLight
  , BlendHardLight
  , BlendVividLight
  , BlendLinearLight
  , BlendPinLight
  , BlendHardMix
  , BlendDifference
  , BlendExclusion
  , BlendSubtract
  , BlendDivide
  , BlendHue
  , BlendSaturation
  , BlendColor
  , BlendLuminosity
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // blend // category
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend mode categories as organized in professional tools.
data BlendCategory
  = CategoryNormal      -- ^ Normal blending operations
  | CategoryDarken      -- ^ Modes that darken the result
  | CategoryLighten     -- ^ Modes that lighten the result
  | CategoryContrast    -- ^ Modes that affect contrast
  | CategoryInversion   -- ^ Modes based on difference/inversion
  | CategoryComponent   -- ^ HSL component transfer modes

derive instance eqBlendCategory :: Eq BlendCategory
derive instance ordBlendCategory :: Ord BlendCategory

instance showBlendCategory :: Show BlendCategory where
  show CategoryNormal = "Normal"
  show CategoryDarken = "Darken"
  show CategoryLighten = "Lighten"
  show CategoryContrast = "Contrast"
  show CategoryInversion = "Inversion"
  show CategoryComponent = "Component"

-- | All blend categories.
allBlendCategories :: Array BlendCategory
allBlendCategories =
  [ CategoryNormal
  , CategoryDarken
  , CategoryLighten
  , CategoryContrast
  , CategoryInversion
  , CategoryComponent
  ]

-- | Get the category for a blend mode.
blendCategory :: BlendMode -> BlendCategory
blendCategory BlendNormal = CategoryNormal
blendCategory BlendDissolve = CategoryNormal
blendCategory BlendDarken = CategoryDarken
blendCategory BlendMultiply = CategoryDarken
blendCategory BlendColorBurn = CategoryDarken
blendCategory BlendLinearBurn = CategoryDarken
blendCategory BlendDarkerColor = CategoryDarken
blendCategory BlendLighten = CategoryLighten
blendCategory BlendScreen = CategoryLighten
blendCategory BlendColorDodge = CategoryLighten
blendCategory BlendLinearDodge = CategoryLighten
blendCategory BlendLighterColor = CategoryLighten
blendCategory BlendOverlay = CategoryContrast
blendCategory BlendSoftLight = CategoryContrast
blendCategory BlendHardLight = CategoryContrast
blendCategory BlendVividLight = CategoryContrast
blendCategory BlendLinearLight = CategoryContrast
blendCategory BlendPinLight = CategoryContrast
blendCategory BlendHardMix = CategoryContrast
blendCategory BlendDifference = CategoryInversion
blendCategory BlendExclusion = CategoryInversion
blendCategory BlendSubtract = CategoryInversion
blendCategory BlendDivide = CategoryInversion
blendCategory BlendHue = CategoryComponent
blendCategory BlendSaturation = CategoryComponent
blendCategory BlendColor = CategoryComponent
blendCategory BlendLuminosity = CategoryComponent

-- | Get all blend modes in a category.
blendModesInCategory :: BlendCategory -> Array BlendMode
blendModesInCategory CategoryNormal = 
  [ BlendNormal, BlendDissolve ]
blendModesInCategory CategoryDarken = 
  [ BlendDarken, BlendMultiply, BlendColorBurn, BlendLinearBurn, BlendDarkerColor ]
blendModesInCategory CategoryLighten = 
  [ BlendLighten, BlendScreen, BlendColorDodge, BlendLinearDodge, BlendLighterColor ]
blendModesInCategory CategoryContrast = 
  [ BlendOverlay, BlendSoftLight, BlendHardLight, BlendVividLight
  , BlendLinearLight, BlendPinLight, BlendHardMix ]
blendModesInCategory CategoryInversion = 
  [ BlendDifference, BlendExclusion, BlendSubtract, BlendDivide ]
blendModesInCategory CategoryComponent = 
  [ BlendHue, BlendSaturation, BlendColor, BlendLuminosity ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Human-readable description of each blend mode's visual effect.
blendModeDescription :: BlendMode -> String
blendModeDescription BlendNormal = 
  "Replaces base pixels with blend pixels at given opacity"
blendModeDescription BlendDissolve = 
  "Randomly replaces pixels based on opacity, creating a dithered effect"
blendModeDescription BlendDarken = 
  "Keeps the darker of base or blend for each channel"
blendModeDescription BlendMultiply = 
  "Multiplies colors, always producing a darker result (like stacking transparencies)"
blendModeDescription BlendColorBurn = 
  "Darkens by increasing contrast, similar to overexposing a photo negative"
blendModeDescription BlendLinearBurn = 
  "Darkens by decreasing brightness linearly, more intense than Multiply"
blendModeDescription BlendDarkerColor = 
  "Compares total luminosity and keeps the darker complete pixel"
blendModeDescription BlendLighten = 
  "Keeps the lighter of base or blend for each channel"
blendModeDescription BlendScreen = 
  "Multiplies inverses, always producing a lighter result (like projecting slides)"
blendModeDescription BlendColorDodge = 
  "Lightens by decreasing contrast, like bleaching"
blendModeDescription BlendLinearDodge = 
  "Adds colors together, also known as Add blend mode"
blendModeDescription BlendLighterColor = 
  "Compares total luminosity and keeps the lighter complete pixel"
blendModeDescription BlendOverlay = 
  "Combines Multiply and Screen based on base brightness, preserving highlights/shadows"
blendModeDescription BlendSoftLight = 
  "Subtle contrast adjustment like shining a diffused light"
blendModeDescription BlendHardLight = 
  "Intense contrast like shining a harsh spotlight"
blendModeDescription BlendVividLight = 
  "Burns or dodges based on blend color brightness"
blendModeDescription BlendLinearLight = 
  "Linear burn or dodge based on blend color brightness"
blendModeDescription BlendPinLight = 
  "Replaces colors based on blend brightness thresholds"
blendModeDescription BlendHardMix = 
  "Posterizes to primary colors based on threshold"
blendModeDescription BlendDifference = 
  "Absolute difference between layers, useful for alignment"
blendModeDescription BlendExclusion = 
  "Similar to Difference but with less contrast"
blendModeDescription BlendSubtract = 
  "Subtracts blend from base, clamping negative values to black"
blendModeDescription BlendDivide = 
  "Divides base by blend, can create blown-out highlights"
blendModeDescription BlendHue = 
  "Applies hue from blend while keeping base saturation and luminosity"
blendModeDescription BlendSaturation = 
  "Applies saturation from blend while keeping base hue and luminosity"
blendModeDescription BlendColor = 
  "Applies hue and saturation from blend while keeping base luminosity"
blendModeDescription BlendLuminosity = 
  "Applies luminosity from blend while keeping base hue and saturation"

-- | Mathematical formula for each blend mode.
-- | Uses A for base layer, B for blend layer, both normalized to [0,1].
blendModeFormula :: BlendMode -> String
blendModeFormula BlendNormal = "B"
blendModeFormula BlendDissolve = "random(opacity) ? B : A"
blendModeFormula BlendDarken = "min(A, B)"
blendModeFormula BlendMultiply = "A * B"
blendModeFormula BlendColorBurn = "1 - (1-A) / B"
blendModeFormula BlendLinearBurn = "A + B - 1"
blendModeFormula BlendDarkerColor = "lum(A) < lum(B) ? A : B"
blendModeFormula BlendLighten = "max(A, B)"
blendModeFormula BlendScreen = "1 - (1-A) * (1-B)"
blendModeFormula BlendColorDodge = "A / (1-B)"
blendModeFormula BlendLinearDodge = "A + B"
blendModeFormula BlendLighterColor = "lum(A) > lum(B) ? A : B"
blendModeFormula BlendOverlay = "A < 0.5 ? 2*A*B : 1 - 2*(1-A)*(1-B)"
blendModeFormula BlendSoftLight = "B < 0.5 ? A - (1-2*B)*A*(1-A) : A + (2*B-1)*(D(A)-A)"
blendModeFormula BlendHardLight = "B < 0.5 ? 2*A*B : 1 - 2*(1-A)*(1-B)"
blendModeFormula BlendVividLight = "B < 0.5 ? ColorBurn(A, 2*B) : ColorDodge(A, 2*B-1)"
blendModeFormula BlendLinearLight = "B < 0.5 ? LinearBurn(A, 2*B) : LinearDodge(A, 2*B-1)"
blendModeFormula BlendPinLight = "B < 0.5 ? Darken(A, 2*B) : Lighten(A, 2*B-1)"
blendModeFormula BlendHardMix = "A + B >= 1 ? 1 : 0"
blendModeFormula BlendDifference = "|A - B|"
blendModeFormula BlendExclusion = "A + B - 2*A*B"
blendModeFormula BlendSubtract = "max(0, A - B)"
blendModeFormula BlendDivide = "A / B"
blendModeFormula BlendHue = "HSL(H(B), S(A), L(A))"
blendModeFormula BlendSaturation = "HSL(H(A), S(B), L(A))"
blendModeFormula BlendColor = "HSL(H(B), S(B), L(A))"
blendModeFormula BlendLuminosity = "HSL(H(A), S(A), L(B))"

-- | Description of each blend category.
blendCategoryDescription :: BlendCategory -> String
blendCategoryDescription CategoryNormal = 
  "Standard blending with no special color interaction"
blendCategoryDescription CategoryDarken = 
  "Modes that result in darker colors than either layer alone"
blendCategoryDescription CategoryLighten = 
  "Modes that result in lighter colors than either layer alone"
blendCategoryDescription CategoryContrast = 
  "Modes that increase or manipulate contrast between layers"
blendCategoryDescription CategoryInversion = 
  "Modes based on color differences and mathematical inversion"
blendCategoryDescription CategoryComponent = 
  "Modes that transfer specific HSL components between layers"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // css // compatibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to CSS mix-blend-mode value.
-- | Returns Nothing for modes not supported in CSS.
toCSSBlendMode :: BlendMode -> Maybe String
toCSSBlendMode BlendNormal = Just "normal"
toCSSBlendMode BlendMultiply = Just "multiply"
toCSSBlendMode BlendScreen = Just "screen"
toCSSBlendMode BlendOverlay = Just "overlay"
toCSSBlendMode BlendDarken = Just "darken"
toCSSBlendMode BlendLighten = Just "lighten"
toCSSBlendMode BlendColorDodge = Just "color-dodge"
toCSSBlendMode BlendColorBurn = Just "color-burn"
toCSSBlendMode BlendHardLight = Just "hard-light"
toCSSBlendMode BlendSoftLight = Just "soft-light"
toCSSBlendMode BlendDifference = Just "difference"
toCSSBlendMode BlendExclusion = Just "exclusion"
toCSSBlendMode BlendHue = Just "hue"
toCSSBlendMode BlendSaturation = Just "saturation"
toCSSBlendMode BlendColor = Just "color"
toCSSBlendMode BlendLuminosity = Just "luminosity"
-- Not supported in CSS
toCSSBlendMode BlendDissolve = Nothing
toCSSBlendMode BlendLinearBurn = Nothing
toCSSBlendMode BlendDarkerColor = Nothing
toCSSBlendMode BlendLinearDodge = Nothing
toCSSBlendMode BlendLighterColor = Nothing
toCSSBlendMode BlendVividLight = Nothing
toCSSBlendMode BlendLinearLight = Nothing
toCSSBlendMode BlendPinLight = Nothing
toCSSBlendMode BlendHardMix = Nothing
toCSSBlendMode BlendSubtract = Nothing
toCSSBlendMode BlendDivide = Nothing

-- | Parse from CSS mix-blend-mode value.
fromCSSBlendMode :: String -> Maybe BlendMode
fromCSSBlendMode "normal" = Just BlendNormal
fromCSSBlendMode "multiply" = Just BlendMultiply
fromCSSBlendMode "screen" = Just BlendScreen
fromCSSBlendMode "overlay" = Just BlendOverlay
fromCSSBlendMode "darken" = Just BlendDarken
fromCSSBlendMode "lighten" = Just BlendLighten
fromCSSBlendMode "color-dodge" = Just BlendColorDodge
fromCSSBlendMode "color-burn" = Just BlendColorBurn
fromCSSBlendMode "hard-light" = Just BlendHardLight
fromCSSBlendMode "soft-light" = Just BlendSoftLight
fromCSSBlendMode "difference" = Just BlendDifference
fromCSSBlendMode "exclusion" = Just BlendExclusion
fromCSSBlendMode "hue" = Just BlendHue
fromCSSBlendMode "saturation" = Just BlendSaturation
fromCSSBlendMode "color" = Just BlendColor
fromCSSBlendMode "luminosity" = Just BlendLuminosity
fromCSSBlendMode _ = Nothing

-- | Is this blend mode supported in CSS?
isCSSSupported :: BlendMode -> Boolean
isCSSSupported mode = case toCSSBlendMode mode of
  Just _ -> true
  Nothing -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Does this mode always darken the result?
isDarkeningMode :: BlendMode -> Boolean
isDarkeningMode mode = blendCategory mode == CategoryDarken

-- | Does this mode always lighten the result?
isLighteningMode :: BlendMode -> Boolean
isLighteningMode mode = blendCategory mode == CategoryLighten

-- | Does this mode affect contrast?
isContrastMode :: BlendMode -> Boolean
isContrastMode mode = blendCategory mode == CategoryContrast

-- | Is this an inversion/difference mode?
isInversionMode :: BlendMode -> Boolean
isInversionMode mode = blendCategory mode == CategoryInversion

-- | Is this an HSL component transfer mode?
isComponentMode :: BlendMode -> Boolean
isComponentMode mode = blendCategory mode == CategoryComponent

-- | Does this mode preserve transparent areas?
-- | Most modes do; Dissolve is the notable exception.
preservesTransparency :: BlendMode -> Boolean
preservesTransparency BlendDissolve = false
preservesTransparency _ = true

-- | Is this blend operation commutative (A blend B = B blend A)?
-- | Only a few modes have this property.
isCommutative :: BlendMode -> Boolean
isCommutative BlendDarken = true
isCommutative BlendMultiply = true
isCommutative BlendLighten = true
isCommutative BlendScreen = true
isCommutative BlendDifference = true
isCommutative BlendExclusion = true
isCommutative BlendLinearDodge = true
isCommutative _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format blend mode with category for debugging/logging.
-- | Example: "Multiply (Darken)"
formatBlendModeWithCategory :: BlendMode -> String
formatBlendModeWithCategory mode =
  show mode <> " (" <> show (blendCategory mode) <> ")"

-- | Format complete blend mode info for documentation.
-- | Includes name, category, description, and formula.
formatBlendModeInfo :: BlendMode -> String
formatBlendModeInfo mode =
  show mode <> "\n" <>
  "  Category: " <> show (blendCategory mode) <> "\n" <>
  "  Formula: " <> blendModeFormula mode <> "\n" <>
  "  " <> blendModeDescription mode
