-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // graph // card-and-shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CardAndShape — Card fields and node shape types.
-- |
-- | ## Overview
-- |
-- | Defines:
-- | - CardField: Fields for card-style nodes
-- | - NodeShape: Visual shapes for node containers
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - ContentTypes (BadgeContent, ProgressContent)

module Hydrogen.Schema.Graph.NodeContent.CardAndShape
  ( -- * Card Fields
    CardField(FieldTitle, FieldSubtitle, FieldMetadata, FieldImage, FieldAvatar, FieldBadge, FieldProgress, FieldDivider, FieldSpacer)
  , titleField
  , subtitleField
  , metadataField
  , imageField
  , avatarField
  
  -- * Node Shape
  , NodeShape(ShapeRectangle, ShapeRoundedRect, ShapePill, ShapeCircle, ShapeEllipse, ShapeDiamond, ShapeHexagon, ShapeOctagon, ShapeParallelogram, ShapeCylinder, ShapeDocument, ShapeCloud, ShapeCustomPath)
  , isRectangle
  , isCircle
  , isDiamond
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Hydrogen.Schema.Graph.NodeContent.ContentTypes
  ( BadgeContent
  , ProgressContent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // card fields
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fields for card-style nodes
data CardField
  = FieldTitle String
  | FieldSubtitle String
  | FieldMetadata String String     -- ^ label, value
  | FieldImage String               -- ^ URL
  | FieldAvatar String String       -- ^ URL, name
  | FieldBadge BadgeContent
  | FieldProgress ProgressContent
  | FieldDivider
  | FieldSpacer Number

derive instance eqCardField :: Eq CardField

instance showCardField :: Show CardField where
  show (FieldTitle _) = "title"
  show (FieldSubtitle _) = "subtitle"
  show (FieldMetadata _ _) = "metadata"
  show (FieldImage _) = "image"
  show (FieldAvatar _ _) = "avatar"
  show (FieldBadge _) = "badge"
  show (FieldProgress _) = "progress"
  show FieldDivider = "divider"
  show (FieldSpacer _) = "spacer"

titleField :: String -> CardField
titleField = FieldTitle

subtitleField :: String -> CardField
subtitleField = FieldSubtitle

metadataField :: String -> String -> CardField
metadataField = FieldMetadata

imageField :: String -> CardField
imageField = FieldImage

avatarField :: String -> String -> CardField
avatarField = FieldAvatar

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // node shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual shape of the node container
data NodeShape
  = ShapeRectangle         -- ^ Standard rectangle
  | ShapeRoundedRect       -- ^ Rounded corners
  | ShapePill              -- ^ Fully rounded ends
  | ShapeCircle            -- ^ Circle (for radial)
  | ShapeEllipse           -- ^ Ellipse
  | ShapeDiamond           -- ^ Rotated square
  | ShapeHexagon           -- ^ Six-sided
  | ShapeOctagon           -- ^ Eight-sided
  | ShapeParallelogram     -- ^ Skewed rectangle
  | ShapeCylinder          -- ^ Database-style
  | ShapeDocument          -- ^ Document shape
  | ShapeCloud             -- ^ Cloud shape
  | ShapeCustomPath String -- ^ Custom SVG path

derive instance eqNodeShape :: Eq NodeShape

instance showNodeShape :: Show NodeShape where
  show ShapeRectangle = "rectangle"
  show ShapeRoundedRect = "rounded-rect"
  show ShapePill = "pill"
  show ShapeCircle = "circle"
  show ShapeEllipse = "ellipse"
  show ShapeDiamond = "diamond"
  show ShapeHexagon = "hexagon"
  show ShapeOctagon = "octagon"
  show ShapeParallelogram = "parallelogram"
  show ShapeCylinder = "cylinder"
  show ShapeDocument = "document"
  show ShapeCloud = "cloud"
  show (ShapeCustomPath _) = "custom"

isRectangle :: NodeShape -> Boolean
isRectangle ShapeRectangle = true
isRectangle ShapeRoundedRect = true
isRectangle _ = false

isCircle :: NodeShape -> Boolean
isCircle ShapeCircle = true
isCircle ShapeEllipse = true
isCircle _ = false

isDiamond :: NodeShape -> Boolean
isDiamond ShapeDiamond = true
isDiamond _ = false
