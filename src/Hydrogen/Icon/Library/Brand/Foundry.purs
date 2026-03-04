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
  
  -- * Geometry Helpers
  , anvilBounds
  , anvilCenter
  , scaleAnvilPath
  , anvilPathData
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (<>)
  , map
  , show
  , (*)
  , (+)
  , (-)
  , (/)
  , (==)
  , otherwise
  )

import Data.Array (foldl)
import Data.String (joinWith)

import Hydrogen.Schema.Geometry.Point (Point2D, point2D, getX, getY)
import Hydrogen.Schema.Geometry.Path.Types 
  ( PathCommand
      ( MoveTo
      , LineTo
      , HLineTo
      , VLineTo
      , QuadTo
      , SmoothQuadTo
      , CubicTo
      , SmoothCurveTo
      , ArcTo
      , ClosePath
      )
  )
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // geometry helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Anvil bounding box in viewBox coordinates.
-- |
-- | Returns { minX, minY, maxX, maxY, width, height }.
-- | Useful for computing padding, alignment, or hit testing.
anvilBounds :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number, width :: Number, height :: Number }
anvilBounds =
  { minX: 3.0
  , minY: 3.0
  , maxX: 21.0
  , maxY: 21.0
  , width: 21.0 - 3.0
  , height: 21.0 - 3.0
  }

-- | Anvil center point in viewBox coordinates.
-- |
-- | Useful for rotation transforms or centering operations.
anvilCenter :: { x :: Number, y :: Number }
anvilCenter =
  { x: (anvilBounds.minX + anvilBounds.maxX) / 2.0
  , y: (anvilBounds.minY + anvilBounds.maxY) / 2.0
  }

-- | Scale anvil path coordinates by a factor.
-- |
-- | Generates path commands scaled from the default 24x24 viewBox.
-- | For example, `scaleAnvilPath 2.0` produces coordinates for 48x48.
scaleAnvilPath :: Number -> Array PathCommand
scaleAnvilPath factor = map scaleCmd anvilCommands
  where
    scaleCmd :: PathCommand -> PathCommand
    scaleCmd (MoveTo p) = MoveTo (scalePoint p)
    scaleCmd (LineTo p) = LineTo (scalePoint p)
    scaleCmd (HLineTo x) = HLineTo (x * factor)
    scaleCmd (VLineTo y) = VLineTo (y * factor)
    scaleCmd (QuadTo c p) = QuadTo (scalePoint c) (scalePoint p)
    scaleCmd (SmoothQuadTo p) = SmoothQuadTo (scalePoint p)
    scaleCmd (CubicTo c1 c2 p) = CubicTo (scalePoint c1) (scalePoint c2) (scalePoint p)
    scaleCmd (SmoothCurveTo c2 p) = SmoothCurveTo (scalePoint c2) (scalePoint p)
    scaleCmd (ArcTo params) = ArcTo (params { rx = params.rx * factor, ry = params.ry * factor, end = scalePoint params.end })
    scaleCmd ClosePath = ClosePath
    
    scalePoint :: Point2D -> Point2D
    scalePoint p = point2D (getX p * factor) (getY p * factor)

-- | Raw anvil path commands for direct manipulation.
anvilCommands :: Array PathCommand
anvilCommands =
  [ MoveTo (point2D 4.0 3.0)
  , LineTo (point2D 20.0 3.0)
  , LineTo (point2D 20.0 7.0)
  , LineTo (point2D 16.0 7.0)
  , LineTo (point2D 16.0 14.0)
  , LineTo (point2D 21.0 14.0)
  , LineTo (point2D 21.0 21.0)
  , LineTo (point2D 3.0 21.0)
  , LineTo (point2D 3.0 14.0)
  , LineTo (point2D 8.0 14.0)
  , LineTo (point2D 8.0 7.0)
  , LineTo (point2D 4.0 7.0)
  , ClosePath
  ]

-- | SVG path data string for the anvil.
-- |
-- | Returns the `d` attribute value: "M4 3 L20 3 L20 7..."
-- | Useful for embedding in custom SVG or canvas operations.
anvilPathData :: String
anvilPathData = joinWith " " (map renderCmd anvilCommands)
  where
    renderCmd :: PathCommand -> String
    renderCmd (MoveTo p) = "M" <> show (getX p) <> " " <> show (getY p)
    renderCmd (LineTo p) = "L" <> show (getX p) <> " " <> show (getY p)
    renderCmd (HLineTo x) = "H" <> show x
    renderCmd (VLineTo y) = "V" <> show y
    renderCmd (QuadTo c p) = "Q" <> show (getX c) <> " " <> show (getY c) <> " " <> show (getX p) <> " " <> show (getY p)
    renderCmd (SmoothQuadTo p) = "T" <> show (getX p) <> " " <> show (getY p)
    renderCmd (CubicTo c1 c2 p) = "C" <> show (getX c1) <> " " <> show (getY c1) <> " " <> show (getX c2) <> " " <> show (getY c2) <> " " <> show (getX p) <> " " <> show (getY p)
    renderCmd (SmoothCurveTo c2 p) = "S" <> show (getX c2) <> " " <> show (getY c2) <> " " <> show (getX p) <> " " <> show (getY p)
    renderCmd (ArcTo params) = "A" <> show params.rx <> " " <> show params.ry <> " " <> show params.rotation <> " " <> boolToFlag params.largeArc <> " " <> boolToFlag params.sweep <> " " <> show (getX params.end) <> " " <> show (getY params.end)
    renderCmd ClosePath = "Z"
    
    boolToFlag :: Boolean -> String
    boolToFlag b = if b then "1" else "0"
