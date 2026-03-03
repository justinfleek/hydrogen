-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // icon // library // brand // foundry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Foundry Brand Icon — The brand extraction engine identity.
-- |
-- | A stylized anvil shape representing the "forging" of brand identity
-- | from raw website data. The icon works at all sizes from 16px to 128px.
-- |
-- | ## Design Rationale
-- |
-- | - **Anvil silhouette**: Represents the forge where brands are shaped
-- | - **Solid fill**: Works well as an extension icon at small sizes
-- | - **Geometric construction**: Clean lines, no complex curves

module Hydrogen.Icon.Library.Brand.Foundry
  ( -- * Icon Definition
    iconFoundry
  , iconFoundryOutline
  
  -- * SVG Export
  , foundryIconSvg16
  , foundryIconSvg48
  , foundryIconSvg128
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  )

import Hydrogen.Schema.Geometry.Point (point2D)
import Hydrogen.Schema.Geometry.Path.Types (PathCommand(MoveTo, LineTo, ClosePath))
import Hydrogen.Schema.Geometry.Path.Construction (pathFromCommands)

import Hydrogen.Icon.Types
  ( IconCategory(CategoryBrand)
  , IconDefinition
  , IconName(IconName)
  , IconPath(SinglePath)
  , IconSize(SizeSm, SizeXxl)
  , IconStyle(StyleSolid, StyleOutline)
  , IconProps
  , defaultIconProps
  , defaultViewBox
  )

import Hydrogen.Icon.Pipeline.SVG (renderAsInline)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // icon definitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Foundry brand icon (solid style).
-- |
-- | An anvil silhouette in a 24x24 viewBox. The shape is:
-- |
-- | ```
-- |        ┌───────────────┐
-- |        │   TOP PLATE   │   (the flat striking surface)
-- |        └───────┬───────┘
-- |            ┌───┴───┐
-- |            │ WAIST │       (narrow middle section)
-- |        ┌───┴───────┴───┐
-- |        │     BASE      │   (wide stable base)
-- |        └───────────────┘
-- | ```
-- |
-- | Coordinates designed for 24x24 viewBox:
-- | - Top plate: 4,3 to 20,7 (wide)
-- | - Waist: 8,7 to 16,14 (narrow)
-- | - Base: 3,14 to 21,21 (widest, stable)
iconFoundry :: IconDefinition
iconFoundry =
  { name: IconName "foundry"
  , category: CategoryBrand
  , viewBox: defaultViewBox
  , paths: SinglePath anvilPath
  , tags: [ "brand", "forge", "anvil", "extraction", "foundry" ]
  , style: StyleSolid
  }
  where
    -- Anvil path: top plate → waist → base → back up
    anvilPath = pathFromCommands
      -- Start at top-left of top plate
      [ MoveTo (point2D 4.0 3.0)
      -- Top plate (horizontal bar)
      , LineTo (point2D 20.0 3.0)
      , LineTo (point2D 20.0 7.0)
      -- Step down to waist (right side)
      , LineTo (point2D 16.0 7.0)
      , LineTo (point2D 16.0 14.0)
      -- Step out to base (right side)
      , LineTo (point2D 21.0 14.0)
      , LineTo (point2D 21.0 21.0)
      -- Base bottom
      , LineTo (point2D 3.0 21.0)
      -- Step up from base (left side)
      , LineTo (point2D 3.0 14.0)
      , LineTo (point2D 8.0 14.0)
      -- Waist left side going up
      , LineTo (point2D 8.0 7.0)
      , LineTo (point2D 4.0 7.0)
      -- Close back to start
      , ClosePath
      ]

-- | Foundry brand icon (outline style).
-- |
-- | Same anvil shape but rendered as stroked outline rather than filled.
iconFoundryOutline :: IconDefinition
iconFoundryOutline = iconFoundry { style = StyleOutline }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // svg export
-- ═════════════════════════════════════════════════════════════════════════════

-- | Foundry icon as inline SVG string (16x16).
-- |
-- | Suitable for browser extension icon16.png source.
foundryIconSvg16 :: String
foundryIconSvg16 = renderAsInline iconFoundry props16
  where
    props16 :: IconProps
    props16 = defaultIconProps { size = SizeSm, style = StyleSolid }

-- | Foundry icon as inline SVG string (48x48).
-- |
-- | Suitable for browser extension icon48.png source.
foundryIconSvg48 :: String
foundryIconSvg48 = renderAsInline iconFoundry props48
  where
    props48 :: IconProps
    props48 = defaultIconProps { size = SizeXxl, style = StyleSolid }

-- | Foundry icon as inline SVG string (128x128).
-- |
-- | Suitable for browser extension icon128.png source.
-- | Note: 128 is beyond standard IconSize, so we use Xxl (48) and the
-- | runtime scales via the viewBox.
foundryIconSvg128 :: String
foundryIconSvg128 = renderAsInline iconFoundry props128
  where
    props128 :: IconProps
    props128 = defaultIconProps { size = SizeXxl, style = StyleSolid }
