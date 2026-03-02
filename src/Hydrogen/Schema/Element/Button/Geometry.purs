-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // element // button // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ButtonGeometry — spatial atoms for button layout and shape.
-- |
-- | ## Atoms Included
-- |
-- | - Size (width, height, min/max constraints)
-- | - Padding (internal spacing)
-- | - Margin (external spacing)
-- | - Corner radii (per-corner radius)
-- | - Aspect ratio constraints

module Hydrogen.Schema.Element.Button.Geometry
  ( -- * Button Geometry Record
    ButtonGeometry
  , defaultGeometry
  , mkGeometry
    -- * Accessors
  , geoWidth
  , geoHeight
  , geoPadding
  , geoCornerRadii
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Geometry.CornerRadii
  ( CornerRadii
  , uniform
  ) as Corner

import Hydrogen.Schema.Geometry.Spacing
  ( Padding
  , SpacingValue
  , padding
  , spacingValue
  , unwrapSpacing
  ) as Spacing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // button geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Geometry atoms for button layout.
-- |
-- | All spatial properties a button needs for layout calculation.
-- |
-- | ## Bounds
-- |
-- | - Dimensions: 1-10000 pixels when specified (Nothing = auto)
-- | - Padding: 0-1000 pixels per edge (via SpacingValue)
-- | - Gap: 0-1000 pixels (via SpacingValue)
-- | - Corner radii: 0-1000 pixels per corner (via CornerRadii)
type ButtonGeometry =
  { -- Dimensions (bounded 1-10000 when specified)
    width :: Maybe Number           -- ^ Explicit width (Nothing = auto)
  , height :: Maybe Number          -- ^ Explicit height (Nothing = auto)
  , minWidth :: Maybe Number        -- ^ Minimum width constraint
  , maxWidth :: Maybe Number        -- ^ Maximum width constraint
  , minHeight :: Maybe Number       -- ^ Minimum height constraint
  , maxHeight :: Maybe Number       -- ^ Maximum height constraint
    -- Spacing (bounded via SpacingValue 0-1000)
  , paddingTop :: Spacing.SpacingValue     -- ^ Top padding
  , paddingRight :: Spacing.SpacingValue   -- ^ Right padding
  , paddingBottom :: Spacing.SpacingValue  -- ^ Bottom padding
  , paddingLeft :: Spacing.SpacingValue    -- ^ Left padding
  , gap :: Spacing.SpacingValue            -- ^ Gap between icon and label
    -- Shape
  , cornerRadii :: Corner.CornerRadii  -- ^ Per-corner radius
  }

-- | Default button geometry.
-- |
-- | Auto-sized with 12px horizontal, 8px vertical padding, 8px corners.
defaultGeometry :: ButtonGeometry
defaultGeometry =
  { width: Nothing
  , height: Nothing
  , minWidth: Nothing
  , maxWidth: Nothing
  , minHeight: Just 36.0
  , maxHeight: Nothing
  , paddingTop: Spacing.spacingValue 8.0
  , paddingRight: Spacing.spacingValue 12.0
  , paddingBottom: Spacing.spacingValue 8.0
  , paddingLeft: Spacing.spacingValue 12.0
  , gap: Spacing.spacingValue 8.0
  , cornerRadii: Corner.uniform 8.0
  }

-- | Clamp a dimension to valid button size range (1-10000 pixels).
-- |
-- | Nothing remains Nothing (auto sizing).
-- | Just values are clamped to 1-10000.
clampDimension :: Maybe Number -> Maybe Number
clampDimension = map (Bounded.clampNumber 1.0 10000.0)

-- | Create custom geometry with bounded values.
-- |
-- | All dimensions are clamped to 1-10000 pixels.
-- | All spacing is clamped to 0-1000 pixels via SpacingValue.
mkGeometry
  :: Maybe Number          -- ^ Width (clamped 1-10000)
  -> Maybe Number          -- ^ Height (clamped 1-10000)
  -> Number                -- ^ Padding X (clamped 0-1000)
  -> Number                -- ^ Padding Y (clamped 0-1000)
  -> Number                -- ^ Corner radius (uniform, clamped via CornerRadii)
  -> ButtonGeometry
mkGeometry w h px py r =
  { width: clampDimension w
  , height: clampDimension h
  , minWidth: Nothing
  , maxWidth: Nothing
  , minHeight: Just 36.0
  , maxHeight: Nothing
  , paddingTop: Spacing.spacingValue py
  , paddingRight: Spacing.spacingValue px
  , paddingBottom: Spacing.spacingValue py
  , paddingLeft: Spacing.spacingValue px
  , gap: Spacing.spacingValue 8.0
  , cornerRadii: Corner.uniform r
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get width.
geoWidth :: ButtonGeometry -> Maybe Number
geoWidth g = g.width

-- | Get height.
geoHeight :: ButtonGeometry -> Maybe Number
geoHeight g = g.height

-- | Get padding as Spacing.Padding.
geoPadding :: ButtonGeometry -> Spacing.Padding
geoPadding g = Spacing.padding
  g.paddingTop
  g.paddingRight
  g.paddingBottom
  g.paddingLeft

-- | Get corner radii.
geoCornerRadii :: ButtonGeometry -> Corner.CornerRadii
geoCornerRadii g = g.cornerRadii
