-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // carousel // item shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Item Shape — Geometry clipping masks for carousel items.
-- |
-- | ## Design Philosophy
-- |
-- | Shapes define the clipping mask applied to item content:
-- | - Rectangle (default, with optional corner radius)
-- | - Circle or ellipse
-- | - Regular polygons (hexagon, octagon, etc.)
-- | - Stars with configurable points
-- | - Custom SVG path
-- |
-- | ## Dependencies
-- |
-- | Pure module with no external dependencies.

module Hydrogen.Element.Compound.Carousel.Item.Shape
  ( ItemShape
      ( ShapeRectangle
      , ShapeCircle
      , ShapeEllipse
      , ShapePolygon
      , ShapeStar
      , ShapeSvgPath
      , ShapeNone
      )
  , itemShape
  , noItemShape
  , rectangleShape
  , starItem
  , starItemWithRatio
  , hexagonItem
  , octagonItem
  , circleItem
  , ellipseItem
  , polygonItem
  , customShapeItem
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape configuration for an item.
-- |
-- | Defines the clipping mask applied to item content:
-- | - Rectangle (default, with optional corner radius)
-- | - Circle or ellipse
-- | - Regular polygons (hexagon, octagon, etc.)
-- | - Stars with configurable points
-- | - Custom SVG path
-- |
-- | ## Corner Radius
-- |
-- | For rectangular shapes, corner radius creates rounded corners.
-- | Radius is clamped to half the smaller dimension.
-- |
-- | ## Star Configuration
-- |
-- | Stars are defined by:
-- | - Point count (minimum 3)
-- | - Inner radius ratio (0.0 to 1.0, where 0.5 is typical)
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Rounded rectangle
-- | rounded = rectangleShape 8.0
-- |
-- | -- 5-pointed star with 50% inner radius
-- | star = starShape 5 0.5
-- |
-- | -- Custom heart shape
-- | heart = customShapeItem "M12 21.35l-1.45-1.32..."
-- | ```
data ItemShape
  = ShapeRectangle Number            -- ^ Rectangle with corner radius
  | ShapeCircle                      -- ^ Circle (aspect ratio preserved)
  | ShapeEllipse                     -- ^ Ellipse (fills container)
  | ShapePolygon Int                 -- ^ Regular polygon with n sides
  | ShapeStar Int Number             -- ^ Star with n points and inner ratio
  | ShapeSvgPath String              -- ^ Custom SVG path data
  | ShapeNone                        -- ^ No clipping (full rectangle)

derive instance eqItemShape :: Eq ItemShape

instance showItemShape :: Show ItemShape where
  show (ShapeRectangle r) = "rectangle:" <> show r
  show ShapeCircle = "circle"
  show ShapeEllipse = "ellipse"
  show (ShapePolygon n) = "polygon:" <> show n
  show (ShapeStar n _) = "star:" <> show n
  show (ShapeSvgPath _) = "svg-path"
  show ShapeNone = "none"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create rectangular shape with corner radius
itemShape :: Number -> ItemShape
itemShape radius = ShapeRectangle (clampRadius radius)
  where
    clampRadius r
      | r < 0.0 = 0.0
      | otherwise = r

-- | No shape clipping (default rectangle, no radius)
noItemShape :: ItemShape
noItemShape = ShapeNone

-- | Rectangle with rounded corners
rectangleShape :: Number -> ItemShape
rectangleShape = itemShape

-- | Star-shaped item with configurable points
-- |
-- | - points: Number of star points (minimum 3)
-- | - innerRatio: Inner radius as ratio of outer (0.0 to 1.0)
starItem :: Int -> ItemShape
starItem points = ShapeStar (clampPoints points) 0.5
  where
    clampPoints p
      | p < 3 = 3
      | p > 32 = 32
      | otherwise = p

-- | Star with custom inner radius ratio
starItemWithRatio :: Int -> Number -> ItemShape
starItemWithRatio points ratio = ShapeStar (clampPoints points) (clampRatio ratio)
  where
    clampPoints p
      | p < 3 = 3
      | p > 32 = 32
      | otherwise = p
    clampRatio r
      | r < 0.1 = 0.1
      | r > 0.9 = 0.9
      | otherwise = r

-- | Hexagon-shaped item (6-sided polygon)
hexagonItem :: ItemShape
hexagonItem = ShapePolygon 6

-- | Octagon-shaped item (8-sided polygon)
octagonItem :: ItemShape
octagonItem = ShapePolygon 8

-- | Circle-shaped item (preserves aspect ratio)
circleItem :: ItemShape
circleItem = ShapeCircle

-- | Ellipse-shaped item (fills container)
ellipseItem :: ItemShape
ellipseItem = ShapeEllipse

-- | Regular polygon with n sides
polygonItem :: Int -> ItemShape
polygonItem sides = ShapePolygon (clampSides sides)
  where
    clampSides s
      | s < 3 = 3
      | s > 32 = 32
      | otherwise = s

-- | Custom SVG path item
-- |
-- | Path data should be valid SVG path syntax (M, L, C, Z commands).
customShapeItem :: String -> ItemShape
customShapeItem = ShapeSvgPath
