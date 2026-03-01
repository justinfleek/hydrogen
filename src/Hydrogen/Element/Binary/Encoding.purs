-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // binary // encoding
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Binary Encoding
-- |
-- | Serialize Element values to binary wire format.
-- | Deterministic: same Element value produces identical bytes.
-- |
-- | This is the leader module that re-exports from submodules and provides
-- | the recursive serializeElement function (which handles the circular
-- | dependency between Element types).

module Hydrogen.Element.Binary.Encoding
  ( -- * Top-level
    serialize
  , serializeElement
  
  -- * Group/Transform
  , serializeGroupSpec
  , serializeElements
  , serializeTransformSpec
  
  -- * Re-exports from Encoding.Helpers
  , module Hydrogen.Element.Binary.Encoding.Helpers
  
  -- * Re-exports from Encoding.Shape
  , module Hydrogen.Element.Binary.Encoding.Shape
  
  -- * Re-exports from Encoding.Material
  , module Hydrogen.Element.Binary.Encoding.Material
  
  -- * Re-exports from Encoding.Transform
  , module Hydrogen.Element.Binary.Encoding.Transform
  
  -- * Re-exports from Encoding.Text
  , module Hydrogen.Element.Binary.Encoding.Text
  
  -- * Re-exports from Encoding.Media
  , module Hydrogen.Element.Binary.Encoding.Media
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (+)
  )

import Data.Array as Array

-- Binary types and primitives
import Hydrogen.Element.Binary.Types
  ( Bytes
  , ElementTag
      ( TagEmpty
      , TagRectangle
      , TagEllipse
      , TagPath
      , TagText
      , TagImage
      , TagVideo
      , TagAudio
      , TagModel3D
      , TagGroup
      , TagTransform
      )
  , magic
  , version
  , headerSize
  , tagToInt
  )

import Hydrogen.Element.Binary.Primitives
  ( concatBytes
  , emptyBytes
  , bytesLength
  , writeU32
  , writeU8
  , serializeHeader
  )

-- Element types
import Hydrogen.Element.Core
  ( Element(Rectangle, Ellipse, Path, Text, Image, Video, Audio, Model3D, Group, Transform, Empty)
  , GroupSpec
  , TransformSpec
  )

-- Re-export submodules
import Hydrogen.Element.Binary.Encoding.Helpers
  ( unwrapPixel
  , radiusToNumber
  )

import Hydrogen.Element.Binary.Encoding.Shape
  ( serializeRectangleSpec
  , serializeRectangleShape
  , serializeEllipseSpec
  , serializeEllipseShape
  , serializePathSpec
  , serializePathShape
  , serializePathCommands
  , serializePathCommand
  , serializeArcParams
  , serializePixelPoint2D
  , serializeCorners
  )

import Hydrogen.Element.Binary.Encoding.Material
  ( serializeFill
  , serializeRGB
  , serializeMaybeStroke
  , serializeStrokeSpec
  , serializeLineCap
  , serializeLineJoin
  , serializeDashPattern
  , serializeOpacity
  )

import Hydrogen.Element.Binary.Encoding.Transform
  ( serializeTransform2D
  )

import Hydrogen.Element.Binary.Encoding.Text
  ( serializeTextSpec
  , serializeGlyphArray
  , serializeGlyph
  , serializeGlyphPath
  , serializeContours
  , serializeContour
  , serializePathCommands3D
  , serializePathCommand3D
  , serializeControlPoint3D
  , serializeGlyphBounds
  , serializeProgress
  )

import Hydrogen.Element.Binary.Encoding.Media
  ( serializeImageSpec
  , serializeImageSource
  , serializeVideoSpec
  , serializeVideoSource
  , serializeVideoPlayback
  , serializeAudioSpec
  , serializeAudioSource
  , serializeAudioPlayback
  , serializeModel3DSpec
  , serializeModel3DSource
  , serializeModel3DCamera
  , serializeMaybeRectangleShape
  , serializeObjectFit
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // element serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize a complete Element with header
serialize :: Element -> Bytes
serialize elem =
  let body = serializeElement elem
      size = headerSize + bytesLength body
      header = serializeHeader { magic, version, size, checksum: 0 }
  in concatBytes header body

-- | Serialize Element without header (for recursive use)
-- | This function lives in the main module due to the circular dependency:
-- | serializeElement needs serializeGroupSpec and serializeTransformSpec,
-- | which in turn need serializeElement for their children.
serializeElement :: Element -> Bytes
serializeElement Empty =
  writeU8 (tagToInt TagEmpty)

serializeElement (Rectangle spec) =
  concatBytes (writeU8 (tagToInt TagRectangle)) $
  serializeRectangleSpec spec

serializeElement (Ellipse spec) =
  concatBytes (writeU8 (tagToInt TagEllipse)) $
  serializeEllipseSpec spec

serializeElement (Path spec) =
  concatBytes (writeU8 (tagToInt TagPath)) $
  serializePathSpec spec

serializeElement (Group spec) =
  concatBytes (writeU8 (tagToInt TagGroup)) $
  serializeGroupSpec spec

serializeElement (Transform spec) =
  concatBytes (writeU8 (tagToInt TagTransform)) $
  serializeTransformSpec spec

serializeElement (Text spec) =
  concatBytes (writeU8 (tagToInt TagText)) $
  serializeTextSpec spec

serializeElement (Image spec) =
  concatBytes (writeU8 (tagToInt TagImage)) $
  serializeImageSpec spec

serializeElement (Video spec) =
  concatBytes (writeU8 (tagToInt TagVideo)) $
  serializeVideoSpec spec

serializeElement (Audio spec) =
  concatBytes (writeU8 (tagToInt TagAudio)) $
  serializeAudioSpec spec

serializeElement (Model3D spec) =
  concatBytes (writeU8 (tagToInt TagModel3D)) $
  serializeModel3DSpec spec

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // group/transform serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize GroupSpec
-- | These functions live here due to the circular dependency with serializeElement.
serializeGroupSpec :: GroupSpec -> Bytes
serializeGroupSpec spec =
  concatBytes (writeU32 (Array.length spec.children)) $
  concatBytes (serializeElements spec.children) $
  serializeOpacity spec.opacity

-- | Serialize array of Elements
serializeElements :: Array Element -> Bytes
serializeElements elems =
  Array.foldl (\acc elem -> concatBytes acc (serializeElement elem)) emptyBytes elems

-- | Serialize TransformSpec
serializeTransformSpec :: TransformSpec -> Bytes
serializeTransformSpec spec =
  concatBytes (serializeTransform2D spec.transform) $
  serializeElement spec.child
