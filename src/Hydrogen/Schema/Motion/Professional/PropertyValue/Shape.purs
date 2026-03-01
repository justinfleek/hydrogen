-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--        // hydrogen // schema // motion // professional // propertyvalue // shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape Property Value — Bezier path data for motion graphics shape layers.
-- |
-- | This module defines the ShapeValue type for professional motion graphics
-- | interchange. Shape paths consist of vertices and relative tangent handles.

module Hydrogen.Schema.Motion.Professional.PropertyValue.Shape
  ( ShapeValue
  , shapeValue
  , shapeVertices
  , shapeInTangents
  , shapeOutTangents
  , shapeClosed
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape value - bezier path data.
-- |
-- | Exactly matches AE's Shape object:
-- | - vertices: Array of [x,y] anchor points
-- | - inTangents: Array of [x,y] incoming tangent handles (relative)
-- | - outTangents: Array of [x,y] outgoing tangent handles (relative)
-- | - closed: Whether the path is closed
-- |
-- | All tangent values are RELATIVE to their vertex.
type ShapeValue =
  { vertices :: Array (Array Number)     -- ^ Array of [x,y] points
  , inTangents :: Array (Array Number)   -- ^ Array of [x,y] relative tangents
  , outTangents :: Array (Array Number)  -- ^ Array of [x,y] relative tangents
  , closed :: Boolean
  }

shapeValue 
  :: Array (Array Number) 
  -> Array (Array Number) 
  -> Array (Array Number) 
  -> Boolean 
  -> ShapeValue
shapeValue verts inT outT cl =
  { vertices: verts
  , inTangents: inT
  , outTangents: outT
  , closed: cl
  }

shapeVertices :: ShapeValue -> Array (Array Number)
shapeVertices s = s.vertices

shapeInTangents :: ShapeValue -> Array (Array Number)
shapeInTangents s = s.inTangents

shapeOutTangents :: ShapeValue -> Array (Array Number)
shapeOutTangents s = s.outTangents

shapeClosed :: ShapeValue -> Boolean
shapeClosed s = s.closed
