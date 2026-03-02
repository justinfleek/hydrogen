-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // binary // encoding // material
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Material Serialization
-- |
-- | Binary encoding for Fill, Stroke, and Opacity.

module Hydrogen.Element.Binary.Encoding.Material
  ( -- * Fill
    serializeFill
  , serializeRGB
  
  -- * Stroke
  , serializeMaybeStroke
  , serializeStrokeSpec
  , serializeLineCap
  , serializeLineJoin
  , serializeDashPattern
  
  -- * Opacity
  , serializeOpacity
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber)

import Hydrogen.Element.Binary.Types
  ( Bytes(Bytes)
  )

import Hydrogen.Element.Binary.Primitives
  ( concatBytes
  , emptyBytes
  , writeU8
  , writeU32
  , writeF32
  )

import Hydrogen.Element.Core
  ( StrokeSpec
  )

import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Gradient as Gradient
import Hydrogen.Schema.Dimension.Stroke as Stroke
import Hydrogen.Schema.Geometry.Stroke as GeomStroke
import Hydrogen.Schema.Surface.Fill as Fill

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // fill serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Fill (tag + payload)
serializeFill :: Fill.Fill -> Bytes
serializeFill = case _ of
  Fill.FillNone -> 
    writeU8 0
  Fill.FillSolid color ->
    concatBytes (writeU8 1) (serializeRGB color)
  Fill.FillGradient gradient ->
    concatBytes (writeU8 2) (serializeGradient gradient)
  Fill.FillPattern _ ->
    -- Pattern serialization: would need image data handling
    writeU8 3
  Fill.FillNoise _ ->
    -- Noise serialization: would need FBM parameter encoding
    writeU8 4

-- | Serialize Gradient using color stop arrays.
-- | Layout:
-- |   gradientType: u8 (0=Linear, 1=Radial, 2=Conic, 3=Mesh)
-- |   stopCount: u32
-- |   stops: array of (position f32 + r u8 + g u8 + b u8)
-- |
-- | Note: Gradient internal structure is opaque. We serialize stops only.
-- | Full gradient reconstruction requires the type tag + stops.
serializeGradient :: Gradient.Gradient -> Bytes
serializeGradient grad = case grad of
  Gradient.Linear _ ->
    concatBytes (writeU8 0) $
    serializeColorStops (Gradient.getStops grad)
  
  Gradient.Radial _ ->
    concatBytes (writeU8 1) $
    serializeColorStops (Gradient.getStops grad)
  
  Gradient.Conic _ ->
    concatBytes (writeU8 2) $
    serializeColorStops (Gradient.getStops grad)
  
  Gradient.Mesh _ ->
    -- Mesh gradients don't use stops, serialize 4 sampled corners
    concatBytes (writeU8 3) $
    concatBytes (serializeRGB (Gradient.sampleMeshAt 0.0 0.0 (extractMesh grad))) $
    concatBytes (serializeRGB (Gradient.sampleMeshAt 1.0 0.0 (extractMesh grad))) $
    concatBytes (serializeRGB (Gradient.sampleMeshAt 0.0 1.0 (extractMesh grad))) $
    serializeRGB (Gradient.sampleMeshAt 1.0 1.0 (extractMesh grad))
  where
    -- Extract MeshGradient for sampling (always valid for Mesh variant)
    extractMesh :: Gradient.Gradient -> Gradient.MeshGradient
    extractMesh (Gradient.Mesh mg) = mg
    extractMesh _ = defaultMesh
    
    -- Default mesh for unreachable cases
    defaultMesh :: Gradient.MeshGradient
    defaultMesh = Gradient.meshGradient 
      (RGB.rgb 0 0 0) 
      (RGB.rgb 0 0 0) 
      (RGB.rgb 0 0 0) 
      (RGB.rgb 0 0 0)

-- | Serialize array of color stops
-- | Layout: count (u32) + stops (each: position f32 + r u8 + g u8 + b u8)
serializeColorStops :: Array Gradient.ColorStop -> Bytes
serializeColorStops stops =
  let countBytes = writeU32 (Array.length stops)
      stopBytes = Array.foldl
        (\acc stop -> concatBytes acc (serializeColorStop stop))
        emptyBytes
        stops
  in concatBytes countBytes stopBytes

-- | Serialize a single color stop
-- | Layout: position (f32) + r (u8) + g (u8) + b (u8)
serializeColorStop :: Gradient.ColorStop -> Bytes
serializeColorStop (Gradient.ColorStop cs) =
  let posBytes = writeF32 (Gradient.unwrapRatio cs.position)
      colorBytes = serializeRGB cs.color
  in concatBytes posBytes colorBytes

-- | Serialize RGB color (3 bytes: r, g, b as u8)
serializeRGB :: RGB.RGB -> Bytes
serializeRGB color =
  let r = Channel.unwrap (RGB.red color)
      g = Channel.unwrap (RGB.green color)
      b = Channel.unwrap (RGB.blue color)
  in Bytes [r, g, b]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // stroke serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Maybe StrokeSpec
serializeMaybeStroke :: Maybe StrokeSpec -> Bytes
serializeMaybeStroke = case _ of
  Nothing -> writeU8 0
  Just s -> concatBytes (writeU8 1) (serializeStrokeSpec s)

-- | Serialize StrokeSpec
serializeStrokeSpec :: StrokeSpec -> Bytes
serializeStrokeSpec spec =
  concatBytes (writeF32 (Stroke.strokeWidthValue spec.width)) $
  concatBytes (serializeFill spec.fill) $
  concatBytes (serializeLineCap spec.cap) $
  concatBytes (serializeLineJoin spec.join) $
  concatBytes (writeF32 (GeomStroke.miterLimitValue spec.miterLimit)) $
  concatBytes (serializeDashPattern spec.dashPattern) $
  serializeOpacity spec.opacity

-- | Serialize LineCap (1 byte)
serializeLineCap :: GeomStroke.LineCap -> Bytes
serializeLineCap = case _ of
  GeomStroke.CapButt -> writeU8 0
  GeomStroke.CapRound -> writeU8 1
  GeomStroke.CapSquare -> writeU8 2

-- | Serialize LineJoin (1 byte)
serializeLineJoin :: GeomStroke.LineJoin -> Bytes
serializeLineJoin = case _ of
  GeomStroke.JoinMiter -> writeU8 0
  GeomStroke.JoinRound -> writeU8 1
  GeomStroke.JoinBevel -> writeU8 2

-- | Serialize DashPattern
serializeDashPattern :: Stroke.DashPattern -> Bytes
serializeDashPattern pattern =
  let dashes = Stroke.dashPatternSegments pattern
      countBytes = writeU32 (Array.length dashes)
      dashBytes = Array.foldl
        (\acc d -> concatBytes acc (writeF32 d))
        emptyBytes
        dashes
  in concatBytes countBytes dashBytes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // opacity serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Opacity (4 bytes as f32)
serializeOpacity :: Opacity.Opacity -> Bytes
serializeOpacity op = writeF32 (toNumber (Opacity.unwrap op))
