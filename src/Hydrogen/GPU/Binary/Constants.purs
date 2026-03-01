-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // gpu // binary // constants
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Constants for binary GPU command serialization.
-- |
-- | This module defines magic numbers, format version, and payload sizes
-- | for all command types.

module Hydrogen.GPU.Binary.Constants
  ( -- * Core constants
    magic
  , version
  , headerSize
  
  -- * V1 payload sizes
  , rectPayloadSize
  , quadPayloadSize
  , glyphPayloadSize
  , particlePayloadSize
  
  -- * V2 payload sizes
  , glyphPathHeaderSize
  , glyphInstancePayloadSize
  , wordHeaderSize
  , pathDataHeaderSize
  , animationStateHeaderSize
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // core constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Magic number: "HYDG" in little-endian ASCII
magic :: Int
magic = 0x48594447

-- | Current format version
version :: Int
version = 1

-- | Header size in bytes
headerSize :: Int
headerSize = 16

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // v1 payload sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | DrawRect payload size (excluding 4-byte command header)
-- | x, y, width, height: 4 x f32 = 16
-- | r, g, b, a: 4 x f32 = 16 (unpacked for GPU)
-- | cornerRadius (4 corners): 4 x f32 = 16
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 56 bytes payload (60 bytes with header)
rectPayloadSize :: Int
rectPayloadSize = 56

-- | DrawQuad payload size
-- | 4 vertices x 2 coords x f32 = 32
-- | color: 4 x f32 = 16
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 56 bytes
quadPayloadSize :: Int
quadPayloadSize = 56

-- | DrawGlyph payload size
-- | x, y: 2 x f32 = 8
-- | glyphIndex: u32 = 4
-- | fontId: u32 = 4
-- | fontSize: f32 = 4
-- | color: 4 x f32 = 16
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 44 bytes
glyphPayloadSize :: Int
glyphPayloadSize = 44

-- | DrawParticle payload size
-- | x, y, z: 3 x f32 = 12
-- | size: f32 = 4
-- | color: 4 x f32 = 16
-- | pickId: u32 = 4
-- | Total: 36 bytes
particlePayloadSize :: Int
particlePayloadSize = 36

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // v2 payload sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | DrawGlyphPath payload size (VARIABLE - this is the header portion)
-- | glyphId: u32 = 4
-- | fontId: u32 = 4 (upgraded for billion-agent scale)
-- | contourCount: u16 = 2
-- | padding: u16 = 2
-- | bounds: 6 x f32 = 24 (minX, minY, minZ, maxX, maxY, maxZ)
-- | advanceWidth: f32 = 4
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Header: 48 bytes + variable contour data
glyphPathHeaderSize :: Int
glyphPathHeaderSize = 48

-- | DrawGlyphInstance payload size (FIXED: 76 bytes)
-- | pathDataId: u32 = 4
-- | position: 3 x f32 = 12 (x, y, z)
-- | rotation: 3 x f32 = 12 (x, y, z euler)
-- | scale: 3 x f32 = 12 (x, y, z)
-- | color: 4 x u8 = 4 (RGBA packed)
-- | animationPhase: f32 = 4
-- | springState: 5 x f32 = 20 (velocity, displacement, tension, damping, mass)
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 76 bytes
glyphInstancePayloadSize :: Int
glyphInstancePayloadSize = 76

-- | DrawWord payload size (VARIABLE - this is the header portion)
-- | wordId: u32 = 4
-- | glyphCount: u16 = 2
-- | staggerDirection: u8 = 1
-- | easing: u8 = 1
-- | origin: 3 x f32 = 12 (x, y, z)
-- | staggerDelayMs: f32 = 4
-- | staggerSeed: u32 = 4 (for StaggerRandom, 0 otherwise)
-- | color: 4 x u8 = 4
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Header: 40 bytes + variable glyph references
wordHeaderSize :: Int
wordHeaderSize = 40

-- | PathData payload size (VARIABLE - this is the header portion)
-- | pathDataId: u32 = 4
-- | commandCount: u32 = 4
-- | bounds: 6 x f32 = 24
-- | Header: 32 bytes + variable command data
pathDataHeaderSize :: Int
pathDataHeaderSize = 32

-- | AnimationState payload size (VARIABLE - this is the header portion)
-- | targetCount: u16 = 2
-- | mode: u8 = 1
-- | padding: u8 = 1
-- | frameTime: f32 = 4
-- | blendFactor: f32 = 4 (for AnimationBlend, 0.0 otherwise)
-- | Header: 12 bytes + variable target data
animationStateHeaderSize :: Int
animationStateHeaderSize = 12
