-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // element // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Core — Pure data description of visual elements.
-- |
-- | ## Purpose
-- |
-- | This module defines the CORRECT Element type: pure data composed entirely
-- | from Schema atoms. No strings. No DOM concepts. No CSS. No JavaScript.
-- |
-- | This replaces the broken `Hydrogen.Render.Element` which uses:
-- |   - `tag :: String` (unbounded, non-deterministic)
-- |   - `Attr String String` (CSS as strings)
-- |
-- | ## Architecture
-- |
-- | Element is pure data that flows:
-- |   Haskell backend → PureScript types → WebGPU execution
-- |
-- | There is no browser in this stack. JavaScript is treated as legacy
-- | bytecode only at the export boundary for broken legacy formats.
-- |
-- | ## Design Principles
-- |
-- | 1. **Composed from Schema atoms** — Every field uses bounded, typed atoms
-- | 2. **GPU-native** — Describes what to render, not how
-- | 3. **Deterministic** — Same Element = same pixels, always
-- | 4. **Serializable** — Can be sent over wire, stored, replayed
-- | 5. **Target-agnostic** — WebGPU, Canvas, Static HTML, any renderer
-- |
-- | ## What Element IS
-- |
-- | Element is a complete GPU instruction set as pure data:
-- |   - Shapes (Rectangle, Ellipse, Path)
-- |   - Fills (Solid, Gradient, Pattern, Noise)
-- |   - Strokes (Width, Color, Dash pattern, Caps, Joins)
-- |   - Transforms (Translate, Rotate, Scale, Skew)
-- |   - Compositions (Group, Clip, Mask)
-- |
-- | ## What Element is NOT
-- |
-- | Element is NOT:
-- |   - A DOM abstraction (no "div", "span", "button")
-- |   - A CSS generator (no "background-color", "border-radius")
-- |   - A framework adapter (no Halogen, React, Vue concepts)
-- |   - JavaScript-dependent (no FFI for core operations)
-- |
-- | ## Module Structure
-- |
-- | This leader module re-exports from submodules:
-- |   - Hydrogen.Element.Core.Stroke — StrokeSpec and constructors
-- |   - Hydrogen.Element.Core.Specs — Shape and text specifications
-- |   - Hydrogen.Element.Core.Media — Image, video, audio, 3D specs
-- |   - Hydrogen.Element.Core.Element — Element type, instances, constructors
-- |
-- | ## Dependencies (Schema atoms only)
-- |
-- | - Hydrogen.Schema.Geometry.Shape (RectangleShape, EllipseShape, PathShape)
-- | - Hydrogen.Schema.Surface.Fill (Fill)
-- | - Hydrogen.Schema.Geometry.Stroke (LineCap, LineJoin, MiterLimit)
-- | - Hydrogen.Schema.Dimension.Stroke (StrokeWidth, DashPattern)
-- | - Hydrogen.Schema.Geometry.Transform (Transform2D)
-- | - Hydrogen.Schema.Color.Opacity (Opacity)

module Hydrogen.Element.Core
  ( -- * Core Element Type
    module ReExportElement
    
  -- * Shape Specs
  , module ReExportSpecs
  
  -- * Stroke Spec
  , module ReExportStroke
  
  -- * Media Specs
  , module ReExportMedia
  
  -- * Stroke Configuration (LineCap, LineJoin)
  , module ReExportLineCap
  , module ReExportLineJoin
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Element type, composition specs, instances, and smart constructors
import Hydrogen.Element.Core.Element
  ( Element(..)
  , GroupSpec
  , TransformSpec
  , rectangle
  , ellipse
  , path
  , text
  , image
  , video
  , audio
  , model3D
  , group
  , transform
  , empty
  ) as ReExportElement

-- Shape and text specifications
import Hydrogen.Element.Core.Specs
  ( RectangleSpec
  , EllipseSpec
  , PathSpec
  , GlyphSpec
  , TextSpec
  ) as ReExportSpecs

-- Stroke specification and constructors
import Hydrogen.Element.Core.Stroke
  ( StrokeSpec
  , stroke
  , strokeWith
  , noStroke
  ) as ReExportStroke

-- Media specifications (image, video, audio, 3D)
import Hydrogen.Element.Core.Media
  ( ImageSpec
  , ImageSource(..)
  , VideoSpec
  , VideoSource(..)
  , VideoPlayback
  , AudioSpec
  , AudioSource(..)
  , AudioPlayback
  , Model3DSpec
  , Model3DSource(..)
  , Model3DCamera
  ) as ReExportMedia

-- LineCap and LineJoin for stroke configuration (directly from Schema)
import Hydrogen.Schema.Geometry.Stroke
  ( LineCap(CapButt, CapRound, CapSquare)
  ) as ReExportLineCap
import Hydrogen.Schema.Geometry.Stroke
  ( LineJoin(JoinMiter, JoinRound, JoinBevel)
  ) as ReExportLineJoin
