-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // binary // typography
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | V2 typography serializers for GPU commands.
-- |
-- | This module provides serialization for typography-as-geometry commands:
-- | DrawGlyphPath, DrawGlyphInstance, DrawWord, DefinePathData, and
-- | UpdateAnimationState.
-- |
-- | ## Wire Format
-- |
-- | Typography commands use opcodes 0x20-0x24 and support variable-length
-- | payloads for contour and path data.

module Hydrogen.GPU.Binary.Typography
  ( -- * Typography serializers
    serializeGlyphPath
  , serializeGlyphInstance
  , serializeWord
  , serializePathData
  , serializeAnimationState
  
  -- * Helpers
  , serializeContour
  , serializePoint3D
  , serializeAnimTarget
  
  -- * Enum encoders
  , staggerDirToInt
  , easingToInt
  , animModeToInt
  , targetTypeToInt
  , getStaggerSeed
  , getBlendFactor
  ) where

import Prelude
  ( (<>)
  )

import Data.Array (concatMap, length, replicate) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.GPU.Binary.LowLevel (writeF32, writeU32, writeU16, writeU8, writeI8)
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.GPU.Coordinates as Coord
import Hydrogen.Animation.Types as AnimTypes
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Dimension.Device as Device

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // typography serializers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize DrawGlyphPath payload (variable length).
-- |
-- | Wire format:
-- | - glyphId: u32
-- | - fontId: u32 (upgraded for billion-agent scale)
-- | - contourCount: u16
-- | - padding: u16
-- | - bounds: 6 x f32
-- | - advanceWidth: f32
-- | - depth: f32
-- | - pickId: u32
-- | - [contours]: variable, per-contour command arrays
serializeGlyphPath :: forall msg. DC.GlyphPathParams msg -> Array Int
serializeGlyphPath p =
  let
    contourCount = Array.length p.contours
  in
    -- Header
    writeU32 p.glyphId
    <> writeU32 p.fontId
    <> writeU16 contourCount
    <> writeU16 0                -- padding for alignment
    -- Bounds
    <> writeF32 (unwrapPixel p.bounds.minX)
    <> writeF32 (unwrapPixel p.bounds.minY)
    <> writeF32 (unwrapPixel p.bounds.minZ)
    <> writeF32 (unwrapPixel p.bounds.maxX)
    <> writeF32 (unwrapPixel p.bounds.maxY)
    <> writeF32 (unwrapPixel p.bounds.maxZ)
    -- Advance and depth (bounded)
    <> writeF32 (unwrapPixel p.advanceWidth)
    <> writeF32 (Coord.unwrapDepthValue p.depth)
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)
    -- Contours (variable)
    <> Array.concatMap serializeContour p.contours

-- | Serialize a single contour.
serializeContour :: DC.ContourData -> Array Int
serializeContour c =
  let
    cmdCount = Array.length c.commands
    outerFlag = if c.isOuter then 1 else 0
  in
    writeU16 cmdCount
    <> writeU8 outerFlag
    <> writeU8 0  -- padding for alignment
    <> Array.concatMap serializePathSegment c.commands

-- | Serialize DrawGlyphInstance payload (fixed 76 bytes).
serializeGlyphInstance :: forall msg. DC.GlyphInstanceParams msg -> Array Int
serializeGlyphInstance p =
  let
    rgb = RGB.fromRGBA p.color
  in
    -- Path reference
    writeU32 p.pathDataId
    -- Position (3D)
    <> writeF32 (unwrapPixel p.position.x)
    <> writeF32 (unwrapPixel p.position.y)
    <> writeF32 (unwrapPixel p.position.z)
    -- Rotation (euler)
    <> writeF32 p.rotation.x
    <> writeF32 p.rotation.y
    <> writeF32 p.rotation.z
    -- Scale
    <> writeF32 p.scale.x
    <> writeF32 p.scale.y
    <> writeF32 p.scale.z
    -- Color (packed RGBA)
    <> writeU8 (Channel.unwrap (RGB.red rgb))
    <> writeU8 (Channel.unwrap (RGB.green rgb))
    <> writeU8 (Channel.unwrap (RGB.blue rgb))
    <> writeU8 (Opacity.unwrap (RGB.alpha p.color))
    -- Animation state (animationPhase is bounded NormalizedX)
    <> writeF32 (Coord.unwrapNormalizedX p.animationPhase)
    <> writeF32 p.spring.velocity
    <> writeF32 p.spring.displacement
    <> writeF32 p.spring.tension
    <> writeF32 p.spring.damping
    <> writeF32 p.spring.mass
    -- Depth and pick (depth is bounded)
    <> writeF32 (Coord.unwrapDepthValue p.depth)
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawWord payload (variable length).
serializeWord :: forall msg. DC.WordParams msg -> Array Int
serializeWord p =
  let
    glyphCount = Array.length p.glyphInstances
    rgb = RGB.fromRGBA p.color
    staggerSeed = getStaggerSeed p.stagger.direction
  in
    -- Header
    writeU32 p.wordId
    <> writeU16 glyphCount
    <> writeU8 (staggerDirToInt p.stagger.direction)
    <> writeU8 (easingToInt p.stagger.easing)
    -- Origin
    <> writeF32 (unwrapPixel p.origin.x)
    <> writeF32 (unwrapPixel p.origin.y)
    <> writeF32 (unwrapPixel p.origin.z)
    -- Stagger delay and seed
    <> writeF32 p.stagger.delayMs
    <> writeU32 staggerSeed  -- Seed for StaggerRandom, 0 otherwise
    -- Color (packed)
    <> writeU8 (Channel.unwrap (RGB.red rgb))
    <> writeU8 (Channel.unwrap (RGB.green rgb))
    <> writeU8 (Channel.unwrap (RGB.blue rgb))
    <> writeU8 (Opacity.unwrap (RGB.alpha p.color))
    -- Depth and pick (depth is bounded)
    <> writeF32 (Coord.unwrapDepthValue p.depth)
    <> writeU32 (pickIdToInt p.pickId)
    -- Glyph references (variable)
    <> Array.concatMap writeU32 p.glyphInstances
    -- Positions (variable)
    <> Array.concatMap serializePoint3D p.positions

-- | Serialize a 3D point.
serializePoint3D :: DC.Point3D -> Array Int
serializePoint3D p =
  writeF32 (unwrapPixel p.x)
  <> writeF32 (unwrapPixel p.y)
  <> writeF32 (unwrapPixel p.z)

-- | Serialize PathData payload (variable length).
serializePathData :: DC.PathDataParams -> Array Int
serializePathData p =
  let
    cmdCount = Array.length p.commands
  in
    writeU32 p.pathDataId
    <> writeU32 cmdCount
    -- Bounds
    <> writeF32 (unwrapPixel p.bounds.minX)
    <> writeF32 (unwrapPixel p.bounds.minY)
    <> writeF32 (unwrapPixel p.bounds.minZ)
    <> writeF32 (unwrapPixel p.bounds.maxX)
    <> writeF32 (unwrapPixel p.bounds.maxY)
    <> writeF32 (unwrapPixel p.bounds.maxZ)
    -- Commands (variable)
    <> Array.concatMap serializePathSegment p.commands

-- | Serialize AnimationState payload (variable length).
serializeAnimationState :: DC.AnimationStateParams -> Array Int
serializeAnimationState p =
  let
    targetCount = Array.length p.targets
    blendFactor = getBlendFactor p.mode
  in
    writeU16 targetCount
    <> writeU8 (animModeToInt p.mode)
    <> writeU8 0  -- padding
    <> writeF32 p.frameTime
    <> writeF32 blendFactor  -- Blend factor (0.0 if not AnimationBlend)
    -- Targets (variable)
    <> Array.concatMap serializeAnimTarget p.targets

-- | Serialize a single animation target.
serializeAnimTarget :: DC.AnimationTarget -> Array Int
serializeAnimTarget t =
  writeU32 t.targetId
  <> writeU8 (targetTypeToInt t.targetType)
  <> pad 3  -- alignment
  -- Delta position
  <> writeF32 (unwrapPixel t.deltaPosition.x)
  <> writeF32 (unwrapPixel t.deltaPosition.y)
  <> writeF32 (unwrapPixel t.deltaPosition.z)
  -- Delta rotation
  <> writeF32 t.deltaRotation.x
  <> writeF32 t.deltaRotation.y
  <> writeF32 t.deltaRotation.z
  -- Delta scale
  <> writeF32 t.deltaScale.x
  <> writeF32 t.deltaScale.y
  <> writeF32 t.deltaScale.z
  -- Delta color (signed, but stored as unsigned)
  <> writeI8 t.deltaColor.r
  <> writeI8 t.deltaColor.g
  <> writeI8 t.deltaColor.b
  <> writeI8 t.deltaColor.a
  -- Phase advance
  <> writeF32 t.phaseAdvance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // enum encoders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Encode StaggerDirection to u8.
staggerDirToInt :: DC.StaggerDirection -> Int
staggerDirToInt = case _ of
  AnimTypes.StaggerLeftToRight -> 0
  AnimTypes.StaggerRightToLeft -> 1
  AnimTypes.StaggerCenterOut -> 2
  AnimTypes.StaggerEdgesIn -> 3
  AnimTypes.StaggerTopToBottom -> 4
  AnimTypes.StaggerBottomToTop -> 5
  AnimTypes.StaggerRandom _ -> 6  -- Seed stored separately

-- | Extract seed from StaggerDirection (0 for non-random).
getStaggerSeed :: DC.StaggerDirection -> Int
getStaggerSeed = case _ of
  AnimTypes.StaggerRandom seed -> seed
  _ -> 0

-- | Encode EasingFunction to u8.
easingToInt :: DC.EasingFunction -> Int
easingToInt = case _ of
  AnimTypes.EasingIdLinear -> 0
  AnimTypes.EasingIdInQuad -> 1
  AnimTypes.EasingIdOutQuad -> 2
  AnimTypes.EasingIdInOutQuad -> 3
  AnimTypes.EasingIdInCubic -> 4
  AnimTypes.EasingIdOutCubic -> 5
  AnimTypes.EasingIdInOutCubic -> 6
  AnimTypes.EasingIdInElastic -> 7
  AnimTypes.EasingIdOutElastic -> 8
  AnimTypes.EasingIdInOutElastic -> 9
  AnimTypes.EasingIdInBounce -> 10
  AnimTypes.EasingIdOutBounce -> 11
  AnimTypes.EasingIdSpring -> 12

-- | Encode AnimationUpdateMode to u8.
animModeToInt :: DC.AnimationUpdateMode -> Int
animModeToInt = case _ of
  DC.AnimationReplace -> 0
  DC.AnimationAdditive -> 1
  DC.AnimationBlend _ -> 2  -- Factor stored separately

-- | Extract blend factor from AnimationUpdateMode (0.0 for non-blend).
getBlendFactor :: DC.AnimationUpdateMode -> Number
getBlendFactor = case _ of
  DC.AnimationBlend factor -> factor
  _ -> 0.0

-- | Encode TargetType to u8.
targetTypeToInt :: DC.TargetType -> Int
targetTypeToInt = case _ of
  DC.TargetGlyphInstance -> 0
  DC.TargetWord -> 1
  DC.TargetPathData -> 2
  DC.TargetControlPoint -> 3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Padding bytes for alignment.
pad :: Int -> Array Int
pad n = Array.replicate n 0

-- | Unwrap Pixel to Number.
unwrapPixel :: Device.Pixel -> Number
unwrapPixel (Device.Pixel n) = n

-- | Convert Maybe PickId to Int (0 = no hit).
pickIdToInt :: Maybe DC.PickId -> Int
pickIdToInt = case _ of
  Nothing -> 0
  Just pid -> DC.unwrapPickId pid

-- | Serialize a path segment (delegated here to avoid circular import).
serializePathSegment :: DC.PathSegment -> Array Int
serializePathSegment = case _ of
  DC.MoveTo pt -> 
    writeU8 0x01 <> pad 3
    <> writeF32 (unwrapPixel pt.x)
    <> writeF32 (unwrapPixel pt.y)
  
  DC.LineTo pt ->
    writeU8 0x02 <> pad 3
    <> writeF32 (unwrapPixel pt.x)
    <> writeF32 (unwrapPixel pt.y)
  
  DC.QuadraticTo ctrl end ->
    writeU8 0x03 <> pad 3
    <> writeF32 (unwrapPixel ctrl.x)
    <> writeF32 (unwrapPixel ctrl.y)
    <> writeF32 (unwrapPixel end.x)
    <> writeF32 (unwrapPixel end.y)
  
  DC.CubicTo c1 c2 end ->
    writeU8 0x04 <> pad 3
    <> writeF32 (unwrapPixel c1.x)
    <> writeF32 (unwrapPixel c1.y)
    <> writeF32 (unwrapPixel c2.x)
    <> writeF32 (unwrapPixel c2.y)
    <> writeF32 (unwrapPixel end.x)
    <> writeF32 (unwrapPixel end.y)
  
  DC.ClosePath ->
    writeU8 0x05 <> pad 3
