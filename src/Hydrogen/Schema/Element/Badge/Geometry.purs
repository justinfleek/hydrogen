-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // element // badge // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BadgeGeometry — Spatial atoms for badge layout, shape, and positioning.
-- |
-- | ## Design Philosophy
-- |
-- | Badge geometry defines WHERE and WHAT SHAPE the badge takes. Badges can be:
-- | - Dots (small circles, no content)
-- | - Circles (larger, can contain single digit)
-- | - Pills (rounded rectangles, can contain text/numbers)
-- | - Custom paths (brand-specific shapes)
-- |
-- | Badges also have ANCHOR POSITION relative to their parent element:
-- | - Top-right corner (most common for notifications)
-- | - Top-left, bottom-left, bottom-right
-- | - Custom offset
-- |
-- | ## Atoms from Pillars
-- |
-- | - Geometry.CornerRadii — Corner rounding
-- | - Geometry.Spacing — Padding, offset
-- | - Dimension.Device — Size in pixels
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.CornerRadii
-- | - Hydrogen.Schema.Geometry.Spacing
-- | - Hydrogen.Schema.Bounded
-- |
-- | ## Dependents
-- |
-- | - Hydrogen.Schema.Element.Badge (compound type)
-- | - Element.Core renderer uses geometry to create shapes

module Hydrogen.Schema.Element.Badge.Geometry
  ( -- * Badge Geometry Record
    BadgeGeometry
  , defaultGeometry
  , mkGeometry
  
  -- * Shape Type
  , BadgeShape(Dot, Circle, Pill, CustomShape)
  , shapeToCornerRadii
  
  -- * Anchor Position
  , AnchorPosition(TopRight, TopLeft, BottomRight, BottomLeft, Custom)
  , anchorOffset
  
  -- * Size Presets
  , dotGeometry
  , smallGeometry
  , mediumGeometry
  , largeGeometry
  
  -- * Accessors
  , geoShape
  , geoSize
  , geoAnchor
  , geoPadding
  , geoOffset
  
  -- * Modifiers
  , setShape
  , setSize
  , setAnchor
  , setPadding
  , setOffset
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , negate
  , (<>)
  , (/)
  , (*)
  )

import Data.Ord (Ordering(LT, GT, EQ))

import Hydrogen.Schema.Geometry.CornerRadii
  ( CornerRadii
  , uniform
  ) as Corner

import Hydrogen.Schema.Geometry.Spacing
  ( SpacingValue
  , spacingValue
  , unwrapSpacing
  ) as Spacing

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // badge shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Badge shape determines the outline and corner treatment.
-- |
-- | ## Variants
-- |
-- | - Dot: Small circle (6-10px), no content, just indicator
-- | - Circle: Larger circle (16-24px), can contain single digit
-- | - Pill: Rounded rectangle, expands to fit content (text, numbers)
-- | - CustomShape: Arbitrary path for brand-specific shapes
data BadgeShape
  = Dot           -- ^ Small indicator dot
  | Circle        -- ^ Full circle (for single digit)
  | Pill          -- ^ Rounded rectangle (for text/multi-digit)
  | CustomShape   -- ^ Custom path (SVG-like)

derive instance eqBadgeShape :: Eq BadgeShape

instance ordBadgeShape :: Ord BadgeShape where
  compare Dot Dot = EQ
  compare Dot _ = LT
  compare Circle Dot = GT
  compare Circle Circle = EQ
  compare Circle _ = LT
  compare Pill Dot = GT
  compare Pill Circle = GT
  compare Pill Pill = EQ
  compare Pill CustomShape = LT
  compare CustomShape CustomShape = EQ
  compare CustomShape _ = GT

instance showBadgeShape :: Show BadgeShape where
  show Dot = "Dot"
  show Circle = "Circle"
  show Pill = "Pill"
  show CustomShape = "CustomShape"

-- | Convert badge shape to corner radii.
-- |
-- | - Dot/Circle: Fully rounded (9999px)
-- | - Pill: Fully rounded (9999px)
-- | - CustomShape: No automatic rounding (path defines shape)
shapeToCornerRadii :: BadgeShape -> Number -> Corner.CornerRadii
shapeToCornerRadii Dot _ = Corner.uniform 9999.0
shapeToCornerRadii Circle _ = Corner.uniform 9999.0
shapeToCornerRadii Pill _ = Corner.uniform 9999.0
shapeToCornerRadii CustomShape _ = Corner.uniform 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // anchor position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Badge anchor position relative to parent element.
-- |
-- | Badges are typically positioned at corners of their parent,
-- | with slight offset to overlap the edge.
data AnchorPosition
  = TopRight      -- ^ Top-right corner (most common)
  | TopLeft       -- ^ Top-left corner
  | BottomRight   -- ^ Bottom-right corner
  | BottomLeft    -- ^ Bottom-left corner
  | Custom        -- ^ Custom position via offset

derive instance eqAnchorPosition :: Eq AnchorPosition

instance showAnchorPosition :: Show AnchorPosition where
  show TopRight = "TopRight"
  show TopLeft = "TopLeft"
  show BottomRight = "BottomRight"
  show BottomLeft = "BottomLeft"
  show Custom = "Custom"

-- | Get the default offset for an anchor position.
-- |
-- | Returns (x, y) offset in pixels. Negative values mean
-- | the badge extends beyond the parent boundary.
anchorOffset :: AnchorPosition -> { x :: Number, y :: Number }
anchorOffset TopRight = { x: negate 4.0, y: negate 4.0 }
anchorOffset TopLeft = { x: 4.0, y: negate 4.0 }
anchorOffset BottomRight = { x: negate 4.0, y: 4.0 }
anchorOffset BottomLeft = { x: 4.0, y: 4.0 }
anchorOffset Custom = { x: 0.0, y: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // badge geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geometry atoms for badge layout.
-- |
-- | ## Fields
-- |
-- | - shape: BadgeShape — Dot, Circle, Pill, or Custom
-- | - width: Number — Width in pixels (auto for Pill based on content)
-- | - height: Number — Height in pixels
-- | - anchor: AnchorPosition — Where to position relative to parent
-- | - offsetX, offsetY: Number — Additional offset from anchor
-- | - paddingX, paddingY: SpacingValue — Internal padding (for Pill)
-- |
-- | ## Bounds
-- |
-- | - Size: 4-200 pixels (clamped)
-- | - Padding: 0-50 pixels (clamped via SpacingValue)
-- | - Offset: -100 to 100 pixels (clamped)
type BadgeGeometry =
  { -- Shape
    shape :: BadgeShape             -- ^ Badge outline type
  -- Size (bounded 4-200px)
  , width :: Number                 -- ^ Width in pixels
  , height :: Number                -- ^ Height in pixels
  -- Position
  , anchor :: AnchorPosition        -- ^ Corner to anchor to
  , offsetX :: Number               -- ^ X offset from anchor (bounded -100 to 100)
  , offsetY :: Number               -- ^ Y offset from anchor (bounded -100 to 100)
  -- Padding (for Pill shape)
  , paddingX :: Spacing.SpacingValue  -- ^ Horizontal padding
  , paddingY :: Spacing.SpacingValue  -- ^ Vertical padding
  }

-- | Default badge geometry — small pill at top-right.
-- |
-- | Suitable for notification counts.
defaultGeometry :: BadgeGeometry
defaultGeometry =
  { shape: Pill
  , width: 20.0
  , height: 20.0
  , anchor: TopRight
  , offsetX: negate 4.0
  , offsetY: negate 4.0
  , paddingX: Spacing.spacingValue 6.0
  , paddingY: Spacing.spacingValue 2.0
  }

-- | Create custom geometry with bounded values.
mkGeometry
  :: BadgeShape
  -> Number           -- ^ Width (clamped 4-200)
  -> Number           -- ^ Height (clamped 4-200)
  -> AnchorPosition
  -> Number           -- ^ Offset X (clamped -100 to 100)
  -> Number           -- ^ Offset Y (clamped -100 to 100)
  -> BadgeGeometry
mkGeometry shape w h anchor ox oy =
  { shape
  , width: clampSize w
  , height: clampSize h
  , anchor
  , offsetX: clampOffset ox
  , offsetY: clampOffset oy
  , paddingX: Spacing.spacingValue 6.0
  , paddingY: Spacing.spacingValue 2.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // size presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dot geometry — minimal indicator (8px).
-- |
-- | No padding, just a presence indicator.
dotGeometry :: BadgeGeometry
dotGeometry = defaultGeometry
  { shape = Dot
  , width = 8.0
  , height = 8.0
  , paddingX = Spacing.spacingValue 0.0
  , paddingY = Spacing.spacingValue 0.0
  }

-- | Small geometry — compact badge (16px).
-- |
-- | Good for single-digit counts.
smallGeometry :: BadgeGeometry
smallGeometry = defaultGeometry
  { shape = Circle
  , width = 16.0
  , height = 16.0
  , paddingX = Spacing.spacingValue 4.0
  , paddingY = Spacing.spacingValue 0.0
  }

-- | Medium geometry — standard badge (20px).
-- |
-- | Default size for most notification badges.
mediumGeometry :: BadgeGeometry
mediumGeometry = defaultGeometry

-- | Large geometry — prominent badge (24px).
-- |
-- | For badges that need more visibility.
largeGeometry :: BadgeGeometry
largeGeometry = defaultGeometry
  { width = 24.0
  , height = 24.0
  , paddingX = Spacing.spacingValue 8.0
  , paddingY = Spacing.spacingValue 4.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get badge shape.
geoShape :: BadgeGeometry -> BadgeShape
geoShape g = g.shape

-- | Get badge size as (width, height).
geoSize :: BadgeGeometry -> { width :: Number, height :: Number }
geoSize g = { width: g.width, height: g.height }

-- | Get anchor position.
geoAnchor :: BadgeGeometry -> AnchorPosition
geoAnchor g = g.anchor

-- | Get padding as (x, y).
geoPadding :: BadgeGeometry -> { x :: Number, y :: Number }
geoPadding g = 
  { x: Spacing.unwrapSpacing g.paddingX
  , y: Spacing.unwrapSpacing g.paddingY
  }

-- | Get offset as (x, y).
geoOffset :: BadgeGeometry -> { x :: Number, y :: Number }
geoOffset g = { x: g.offsetX, y: g.offsetY }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set badge shape.
setShape :: BadgeShape -> BadgeGeometry -> BadgeGeometry
setShape s g = g { shape = s }

-- | Set badge size (clamped to 4-200).
setSize :: Number -> Number -> BadgeGeometry -> BadgeGeometry
setSize w h g = g
  { width = clampSize w
  , height = clampSize h
  }

-- | Set anchor position.
setAnchor :: AnchorPosition -> BadgeGeometry -> BadgeGeometry
setAnchor a g = 
  let offset = anchorOffset a
  in g 
    { anchor = a
    , offsetX = offset.x
    , offsetY = offset.y
    }

-- | Set padding (clamped to 0-50).
setPadding :: Number -> Number -> BadgeGeometry -> BadgeGeometry
setPadding px py g = g
  { paddingX = Spacing.spacingValue (clampPadding px)
  , paddingY = Spacing.spacingValue (clampPadding py)
  }

-- | Set offset (clamped to -100 to 100).
setOffset :: Number -> Number -> BadgeGeometry -> BadgeGeometry
setOffset ox oy g = g
  { offsetX = clampOffset ox
  , offsetY = clampOffset oy
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp size to valid range (4-200 pixels).
clampSize :: Number -> Number
clampSize = Bounded.clampNumber 4.0 200.0

-- | Clamp offset to valid range (-100 to 100 pixels).
clampOffset :: Number -> Number
clampOffset = Bounded.clampNumber (negate 100.0) 100.0

-- | Clamp padding to valid range (0-50 pixels).
clampPadding :: Number -> Number
clampPadding = Bounded.clampNumber 0.0 50.0
