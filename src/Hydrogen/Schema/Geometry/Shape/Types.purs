-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // geometry // shape // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Types — Foundational type definitions for Shape module.
-- |
-- | This module contains all the core type definitions used across the Shape
-- | subsystem: pixel points, anchor points, path commands, winding rules,
-- | and shape primitive enumeration.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Schema.Dimension.Device (Pixel for measurements)

module Hydrogen.Schema.Geometry.Shape.Types
  ( -- * Pixel Point Types
    PixelPoint2D
  , pixelPoint2D
  , pixelOrigin
  , PixelPoint3D
  , pixelPoint3D
  , pixelOrigin3D
  
  -- * Anchor Points (for Bezier)
  , AnchorPoint
  , anchorPoint
  , smoothAnchor
  , cornerAnchor
  , symmetricAnchor
  , AnchorType(AnchorSmooth, AnchorCorner, AnchorSymmetric)
  
  -- * Path Primitives
  , PathCommand(MoveTo, LineTo, HorizontalTo, VerticalTo, CubicTo, QuadraticTo, ArcTo, ClosePath)
  , WindingRule(WindingNonZero, WindingEvenOdd)
  , ArcParams
  
  -- * Primitive Shapes Enumeration
  , ShapePrimitive(PrimitiveRectangle, PrimitiveEllipse, PrimitiveLine, PrimitivePolygon, PrimitiveStar, PrimitiveRing, PrimitiveSpiral, PrimitiveArrow, PrimitiveCross, PrimitiveGear, PrimitivePath)
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
  , negate
  )

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pixel point 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 2D point in pixel space with explicit Pixel units.
-- |
-- | This is distinct from Geometry.Point.Point2D which uses unbounded Numbers.
-- | PixelPoint2D is used for shape vertices and control points where we need
-- | type-safe unit tracking.
-- |
-- | For generic coordinate operations, use Geometry.Point.Point2D.
-- | For shape definitions with pixel measurements, use PixelPoint2D.
type PixelPoint2D = { x :: Pixel, y :: Pixel }

-- | Smart constructor for PixelPoint2D
pixelPoint2D :: Pixel -> Pixel -> PixelPoint2D
pixelPoint2D x y = { x, y }

-- | The pixel origin point (0, 0)
pixelOrigin :: PixelPoint2D
pixelOrigin = { x: Pixel 0.0, y: Pixel 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pixel point 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 3D point in pixel space with explicit Pixel units.
-- |
-- | Extends PixelPoint2D with a Z coordinate for:
-- | - 3D viewport positioning (widgets floating in space)
-- | - Depth sorting for overlapping elements
-- | - WebGL/WebGPU vertex data with type-safe units
-- | - Gimbal and gizmo positioning for interactive 3D controls
-- |
-- | The Z axis follows WebGL convention: positive Z comes toward the viewer.
-- |
-- | ## Example: Bento box widget at depth
-- |
-- | ```purescript
-- | widgetPosition = pixelPoint3D (Pixel 100.0) (Pixel 50.0) (Pixel 10.0)
-- | -- Widget is 100px right, 50px down, 10px toward viewer
-- | ```
type PixelPoint3D = { x :: Pixel, y :: Pixel, z :: Pixel }

-- | Smart constructor for PixelPoint3D
pixelPoint3D :: Pixel -> Pixel -> Pixel -> PixelPoint3D
pixelPoint3D x y z = { x, y, z }

-- | The 3D pixel origin point (0, 0, 0)
pixelOrigin3D :: PixelPoint3D
pixelOrigin3D = { x: Pixel 0.0, y: Pixel 0.0, z: Pixel 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // anchor point
-- ═════════════════════════════════════════════════════════════════════════════

-- | Anchor point type for Bezier curve vertices.
-- | Determines how control handles behave at this vertex.
data AnchorType
  = AnchorSmooth      -- ^ Handles are colinear (C1 continuity)
  | AnchorCorner      -- ^ Handles are independent (no continuity)
  | AnchorSymmetric   -- ^ Handles are colinear and equal length

derive instance eqAnchorType :: Eq AnchorType
derive instance ordAnchorType :: Ord AnchorType

instance showAnchorType :: Show AnchorType where
  show AnchorSmooth = "(AnchorType Smooth)"
  show AnchorCorner = "(AnchorType Corner)"
  show AnchorSymmetric = "(AnchorType Symmetric)"

-- | A bezier anchor point with position and control handles.
-- | Control handles are relative to the anchor position.
type AnchorPoint =
  { position :: PixelPoint2D
  , handleIn :: PixelPoint2D    -- ^ Incoming control handle (relative)
  , handleOut :: PixelPoint2D   -- ^ Outgoing control handle (relative)
  , anchorType :: AnchorType
  }

-- | Create an anchor point with explicit handles
anchorPoint :: PixelPoint2D -> PixelPoint2D -> PixelPoint2D -> AnchorType -> AnchorPoint
anchorPoint position handleIn handleOut anchorType' =
  { position, handleIn, handleOut, anchorType: anchorType' }

-- | Create a smooth anchor with colinear handles
smoothAnchor :: PixelPoint2D -> PixelPoint2D -> PixelPoint2D -> AnchorPoint
smoothAnchor position handleIn handleOut =
  anchorPoint position handleIn handleOut AnchorSmooth

-- | Create a corner anchor (sharp, independent handles)
cornerAnchor :: PixelPoint2D -> AnchorPoint
cornerAnchor position =
  anchorPoint position pixelOrigin pixelOrigin AnchorCorner

-- | Create a symmetric anchor (handles mirror each other)
symmetricAnchor :: PixelPoint2D -> PixelPoint2D -> AnchorPoint
symmetricAnchor position handle =
  anchorPoint position (negatePoint handle) handle AnchorSymmetric
  where
    negatePoint :: PixelPoint2D -> PixelPoint2D
    negatePoint { x: Pixel px, y: Pixel py } = 
      { x: Pixel (negate px), y: Pixel (negate py) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // path commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Winding rule for determining inside/outside of paths.
-- | Critical for boolean operations and fill rendering.
data WindingRule
  = WindingNonZero   -- ^ Non-zero winding rule (SVG default)
  | WindingEvenOdd   -- ^ Even-odd (alternate) rule

derive instance eqWindingRule :: Eq WindingRule
derive instance ordWindingRule :: Ord WindingRule

instance showWindingRule :: Show WindingRule where
  show WindingNonZero = "(WindingRule NonZero)"
  show WindingEvenOdd = "(WindingRule EvenOdd)"

-- | Parameters for elliptical arc commands
type ArcParams =
  { radiusX :: Pixel
  , radiusY :: Pixel
  , rotation :: Number       -- ^ X-axis rotation in degrees
  , largeArc :: Boolean      -- ^ Use large arc sweep
  , sweep :: Boolean         -- ^ Clockwise sweep direction
  }

-- | Path commands following SVG path semantics.
-- | These are the atomic operations for constructing paths.
data PathCommand
  = MoveTo PixelPoint2D              -- ^ Move to point (starts new subpath)
  | LineTo PixelPoint2D              -- ^ Draw line to point
  | HorizontalTo Pixel               -- ^ Draw horizontal line to X
  | VerticalTo Pixel                 -- ^ Draw vertical line to Y
  | CubicTo PixelPoint2D PixelPoint2D PixelPoint2D  -- ^ Cubic bezier (c1, c2, end)
  | QuadraticTo PixelPoint2D PixelPoint2D           -- ^ Quadratic bezier (control, end)
  | ArcTo ArcParams PixelPoint2D                    -- ^ Elliptical arc to point
  | ClosePath                                       -- ^ Close current subpath

derive instance eqPathCommand :: Eq PathCommand

instance showPathCommand :: Show PathCommand where
  show (MoveTo p) = "(PathCommand MoveTo " <> show p <> ")"
  show (LineTo p) = "(PathCommand LineTo " <> show p <> ")"
  show (HorizontalTo x) = "(PathCommand HorizontalTo " <> show x <> ")"
  show (VerticalTo y) = "(PathCommand VerticalTo " <> show y <> ")"
  show (CubicTo c1 c2 end) = "(PathCommand CubicTo " <> show c1 <> " " <> show c2 <> " " <> show end <> ")"
  show (QuadraticTo c end) = "(PathCommand QuadraticTo " <> show c <> " " <> show end <> ")"
  show (ArcTo _ end) = "(PathCommand ArcTo " <> show end <> ")"
  show ClosePath = "(PathCommand ClosePath)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // primitive shapes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enumeration of all primitive shape types.
-- | Used for type-level discrimination and pattern matching.
data ShapePrimitive
  = PrimitiveRectangle
  | PrimitiveEllipse
  | PrimitiveLine
  | PrimitivePolygon
  | PrimitiveStar
  | PrimitiveRing
  | PrimitiveSpiral
  | PrimitiveArrow
  | PrimitiveCross
  | PrimitiveGear
  | PrimitivePath

derive instance eqShapePrimitive :: Eq ShapePrimitive
derive instance ordShapePrimitive :: Ord ShapePrimitive

instance showShapePrimitive :: Show ShapePrimitive where
  show PrimitiveRectangle = "(ShapePrimitive Rectangle)"
  show PrimitiveEllipse = "(ShapePrimitive Ellipse)"
  show PrimitiveLine = "(ShapePrimitive Line)"
  show PrimitivePolygon = "(ShapePrimitive Polygon)"
  show PrimitiveStar = "(ShapePrimitive Star)"
  show PrimitiveRing = "(ShapePrimitive Ring)"
  show PrimitiveSpiral = "(ShapePrimitive Spiral)"
  show PrimitiveArrow = "(ShapePrimitive Arrow)"
  show PrimitiveCross = "(ShapePrimitive Cross)"
  show PrimitiveGear = "(ShapePrimitive Gear)"
  show PrimitivePath = "(ShapePrimitive Path)"
