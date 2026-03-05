-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // element // input // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | InputGeometry — Spatial atoms for text input layout.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - Pixel (Dimension.Device) — Verified pixel unit
-- | - SpacingValue (Geometry.Spacing) — Bounded spacing [0-1000]
-- | - CornerRadii (Geometry.CornerRadii) — 4-corner radii
-- |
-- | ## Input Geometry Model
-- |
-- | An input consists of:
-- | - Container: The outer box with border
-- | - Content area: Text area with padding
-- | - Prefix/Suffix slots: Optional icons or text
-- | - Clear button: Optional clear control
-- |
-- | ## Size Presets
-- |
-- | Standard sizes for common use cases:
-- | - Sm: 32px height (compact forms)
-- | - Md: 40px height (default)
-- | - Lg: 48px height (large forms)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Dimension.Device (Pixel)
-- | - Hydrogen.Schema.Geometry.Spacing (SpacingValue)
-- | - Hydrogen.Schema.Geometry.CornerRadii (CornerRadii)

module Hydrogen.Schema.Element.Input.Geometry
  ( -- * Input Size Presets
    InputSize
      ( SizeSm
      , SizeMd
      , SizeLg
      , SizeCustom
      )
  , sizeToHeight
  , sizeToPaddingX
  , sizeToPaddingY
  , sizeToFontSize
  
  -- * Input Geometry Record
  , InputGeometry
  , defaultGeometry
  , compactGeometry
  , largeGeometry
  , fullWidthGeometry
  , multilineGeometry
  
  -- * Geometry Accessors
  , getWidth
  , getHeight
  , getPaddingX
  , getPaddingY
  , getCornerRadius
  , getBorderWidth
  , isFullWidth
  , isMultiline
  , getMinRows
  , getMaxRows
  
  -- * Geometry Modifiers
  , setWidth
  , setHeight
  , setPaddingX
  , setPaddingY
  , setCornerRadius
  , setBorderWidth
  , setFullWidth
  , setMultiline
  , setMinRows
  , setMaxRows
  , setPillShape
  , setSquareShape
  
  -- * Re-exports
  , module Hydrogen.Schema.Dimension.Device.Types
  , module Hydrogen.Schema.Geometry.Spacing
  , module Hydrogen.Schema.Geometry.CornerRadii
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
  , (/)
  )

import Prim (Boolean, Int, Number)

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Dimension.Device.Types
  ( Pixel(Pixel)
  )

import Hydrogen.Schema.Geometry.Spacing
  ( SpacingValue(SpacingValue)
  , spacingValue
  , spacingZero
  , spacingSm
  , spacingMd
  )

import Hydrogen.Schema.Geometry.CornerRadii
  ( CornerRadii
  , uniform
  , none
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // input sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input size presets — semantic sizes for input controls.
-- |
-- | ## Size Specifications
-- |
-- | | Size | Height | Padding X | Padding Y | Font |
-- | |------|--------|-----------|-----------|------|
-- | | Sm   | 32px   | 10px      | 6px       | 14px |
-- | | Md   | 40px   | 12px      | 8px       | 16px |
-- | | Lg   | 48px   | 16px      | 12px      | 18px |
data InputSize
  = SizeSm                               -- ^ 32px height (compact)
  | SizeMd                               -- ^ 40px height (default)
  | SizeLg                               -- ^ 48px height (large)
  | SizeCustom Pixel Pixel Pixel         -- ^ Custom (height, paddingX, paddingY)

derive instance eqInputSize :: Eq InputSize
derive instance ordInputSize :: Ord InputSize

instance showInputSize :: Show InputSize where
  show SizeSm = "sm"
  show SizeMd = "md"
  show SizeLg = "lg"
  show (SizeCustom h px py) = "(custom " <> show h <> " " <> show px <> " " <> show py <> ")"

-- | Get height for size preset.
sizeToHeight :: InputSize -> Pixel
sizeToHeight = case _ of
  SizeSm -> Pixel 32.0
  SizeMd -> Pixel 40.0
  SizeLg -> Pixel 48.0
  SizeCustom h _ _ -> h

-- | Get horizontal padding for size preset.
sizeToPaddingX :: InputSize -> Pixel
sizeToPaddingX = case _ of
  SizeSm -> Pixel 10.0
  SizeMd -> Pixel 12.0
  SizeLg -> Pixel 16.0
  SizeCustom _ px _ -> px

-- | Get vertical padding for size preset.
sizeToPaddingY :: InputSize -> Pixel
sizeToPaddingY = case _ of
  SizeSm -> Pixel 6.0
  SizeMd -> Pixel 8.0
  SizeLg -> Pixel 12.0
  SizeCustom _ _ py -> py

-- | Get font size for size preset.
sizeToFontSize :: InputSize -> Pixel
sizeToFontSize = case _ of
  SizeSm -> Pixel 14.0
  SizeMd -> Pixel 16.0
  SizeLg -> Pixel 18.0
  SizeCustom (Pixel h) _ _ -> Pixel (h / 2.5)  -- Approximate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // input geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete input geometry — all spatial properties.
-- |
-- | ## Verified Bounds
-- |
-- | - Dimensions: via Pixel (typed, not raw Number)
-- | - Corner radii: via CornerRadii (bounded 0-1000)
-- | - Border width: bounded 0-10
-- |
-- | ## Width Modes
-- |
-- | - Fixed width: Specific pixel width
-- | - Full width: Expands to fill container (width = Nothing)
-- |
-- | ## Multiline
-- |
-- | For textarea-style inputs:
-- | - minRows: Minimum visible rows
-- | - maxRows: Maximum before scrolling
type InputGeometry =
  { -- Dimensions
    width :: Maybe Pixel               -- ^ Fixed width (Nothing = full width)
  , height :: Pixel                    -- ^ Single-line height
  , paddingX :: Pixel                  -- ^ Horizontal padding
  , paddingY :: Pixel                  -- ^ Vertical padding
    -- Border
  , cornerRadius :: CornerRadii        -- ^ Corner radii
  , borderWidth :: Number              -- ^ Border width (bounded 0-10)
    -- Multiline
  , multiline :: Boolean               -- ^ Is this a textarea?
  , minRows :: Int                     -- ^ Minimum rows (multiline)
  , maxRows :: Maybe Int               -- ^ Maximum rows before scroll
    -- Font (for proper line height calc)
  , fontSize :: Pixel                  -- ^ Font size
  , lineHeight :: Number               -- ^ Line height multiplier
  }

-- | Default input geometry — medium size, fixed 240px width.
defaultGeometry :: InputGeometry
defaultGeometry =
  { width: Just (Pixel 240.0)
  , height: Pixel 40.0
  , paddingX: Pixel 12.0
  , paddingY: Pixel 8.0
  , cornerRadius: uniform 6.0
  , borderWidth: 1.0
  , multiline: false
  , minRows: 1
  , maxRows: Nothing
  , fontSize: Pixel 16.0
  , lineHeight: 1.5
  }

-- | Compact input geometry — small size for dense forms.
compactGeometry :: InputGeometry
compactGeometry =
  { width: Just (Pixel 180.0)
  , height: Pixel 32.0
  , paddingX: Pixel 10.0
  , paddingY: Pixel 6.0
  , cornerRadius: uniform 4.0
  , borderWidth: 1.0
  , multiline: false
  , minRows: 1
  , maxRows: Nothing
  , fontSize: Pixel 14.0
  , lineHeight: 1.4
  }

-- | Large input geometry — for primary forms and touch.
largeGeometry :: InputGeometry
largeGeometry =
  { width: Just (Pixel 320.0)
  , height: Pixel 48.0
  , paddingX: Pixel 16.0
  , paddingY: Pixel 12.0
  , cornerRadius: uniform 8.0
  , borderWidth: 1.0
  , multiline: false
  , minRows: 1
  , maxRows: Nothing
  , fontSize: Pixel 18.0
  , lineHeight: 1.5
  }

-- | Full width input geometry — expands to container.
fullWidthGeometry :: InputGeometry
fullWidthGeometry = defaultGeometry
  { width = Nothing
  }

-- | Multiline input geometry — textarea style.
multilineGeometry :: InputGeometry
multilineGeometry = defaultGeometry
  { multiline = true
  , height = Pixel 120.0      -- Initial height
  , minRows = 3
  , maxRows = Just 10
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get width (Nothing = full width).
getWidth :: InputGeometry -> Maybe Pixel
getWidth g = g.width

-- | Get height.
getHeight :: InputGeometry -> Pixel
getHeight g = g.height

-- | Get horizontal padding.
getPaddingX :: InputGeometry -> Pixel
getPaddingX g = g.paddingX

-- | Get vertical padding.
getPaddingY :: InputGeometry -> Pixel
getPaddingY g = g.paddingY

-- | Get corner radius.
getCornerRadius :: InputGeometry -> CornerRadii
getCornerRadius g = g.cornerRadius

-- | Get border width (bounded 0-10).
getBorderWidth :: InputGeometry -> Number
getBorderWidth g = Bounded.clampNumber 0.0 10.0 g.borderWidth

-- | Is this a full-width input?
isFullWidth :: InputGeometry -> Boolean
isFullWidth g = case g.width of
  Nothing -> true
  Just _ -> false

-- | Is this a multiline input?
isMultiline :: InputGeometry -> Boolean
isMultiline g = g.multiline

-- | Get minimum rows (multiline).
getMinRows :: InputGeometry -> Int
getMinRows g = g.minRows

-- | Get maximum rows (multiline).
getMaxRows :: InputGeometry -> Maybe Int
getMaxRows g = g.maxRows

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set fixed width.
setWidth :: Number -> InputGeometry -> InputGeometry
setWidth w g = g { width = Just (Pixel (Bounded.clampNumber 40.0 1000.0 w)) }

-- | Set height.
setHeight :: Number -> InputGeometry -> InputGeometry
setHeight h g = g { height = Pixel (Bounded.clampNumber 24.0 500.0 h) }

-- | Set horizontal padding.
setPaddingX :: Number -> InputGeometry -> InputGeometry
setPaddingX p g = g { paddingX = Pixel (Bounded.clampNumber 0.0 100.0 p) }

-- | Set vertical padding.
setPaddingY :: Number -> InputGeometry -> InputGeometry
setPaddingY p g = g { paddingY = Pixel (Bounded.clampNumber 0.0 100.0 p) }

-- | Set corner radius (uniform).
setCornerRadius :: Number -> InputGeometry -> InputGeometry
setCornerRadius r g = g { cornerRadius = uniform r }

-- | Set border width (bounded 0-10).
setBorderWidth :: Number -> InputGeometry -> InputGeometry
setBorderWidth w g = g { borderWidth = Bounded.clampNumber 0.0 10.0 w }

-- | Set full width mode.
setFullWidth :: Boolean -> InputGeometry -> InputGeometry
setFullWidth true g = g { width = Nothing }
setFullWidth false g = g { width = Just (Pixel 240.0) }

-- | Set multiline mode.
setMultiline :: Boolean -> InputGeometry -> InputGeometry
setMultiline m g = g { multiline = m }

-- | Set minimum rows (multiline).
setMinRows :: Int -> InputGeometry -> InputGeometry
setMinRows n g = g { minRows = Bounded.clampInt 1 100 n }

-- | Set maximum rows (multiline).
setMaxRows :: Int -> InputGeometry -> InputGeometry
setMaxRows n g = g { maxRows = Just (Bounded.clampInt 1 100 n) }

-- | Set pill shape (radius = height/2).
setPillShape :: InputGeometry -> InputGeometry
setPillShape g = case g.height of
  Pixel h -> g { cornerRadius = uniform (h / 2.0) }

-- | Set square shape (no radius).
setSquareShape :: InputGeometry -> InputGeometry
setSquareShape g = g { cornerRadius = none }
