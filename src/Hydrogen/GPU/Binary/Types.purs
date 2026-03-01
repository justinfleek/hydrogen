-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // gpu // binary // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for binary GPU command serialization.
-- |
-- | This module defines the fundamental types used across all binary
-- | serialization operations.

module Hydrogen.GPU.Binary.Types
  ( -- * Types
    Bytes(Bytes)
  , Header
  , CommandType
      ( CmdNoop
      , CmdDrawRect
      , CmdDrawQuad
      , CmdDrawGlyph
      , CmdDrawPath
      , CmdDrawParticle
      , CmdPushClip
      , CmdPopClip
      , CmdDrawGlyphPath
      , CmdDrawGlyphInstance
      , CmdDrawWord
      , CmdDefinePathData
      , CmdUpdateAnimationState
      )
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Array (length) as Array

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Raw bytes as array of integers (0-255).
-- | This is the pure representation - actual TypedArray created at boundary.
newtype Bytes = Bytes (Array Int)

derive instance eqBytes :: Eq Bytes

instance showBytes :: Show Bytes where
  show (Bytes arr) = "Bytes[" <> show (Array.length arr) <> "]"

-- | Buffer header.
type Header =
  { magic :: Int      -- 0x48594447 "HYDG"
  , version :: Int    -- Format version
  , count :: Int      -- Number of commands
  , flags :: Int      -- Reserved
  }

-- | Command type discriminant.
data CommandType
  = CmdNoop
  | CmdDrawRect
  | CmdDrawQuad
  | CmdDrawGlyph
  | CmdDrawPath
  | CmdDrawParticle
  | CmdPushClip
  | CmdPopClip
  -- v2 Typography as Geometry
  | CmdDrawGlyphPath
  | CmdDrawGlyphInstance
  | CmdDrawWord
  | CmdDefinePathData
  | CmdUpdateAnimationState

derive instance eqCommandType :: Eq CommandType
derive instance ordCommandType :: Ord CommandType

instance showCommandType :: Show CommandType where
  show CmdNoop = "Noop"
  show CmdDrawRect = "DrawRect"
  show CmdDrawQuad = "DrawQuad"
  show CmdDrawGlyph = "DrawGlyph"
  show CmdDrawPath = "DrawPath"
  show CmdDrawParticle = "DrawParticle"
  show CmdPushClip = "PushClip"
  show CmdPopClip = "PopClip"
  show CmdDrawGlyphPath = "DrawGlyphPath"
  show CmdDrawGlyphInstance = "DrawGlyphInstance"
  show CmdDrawWord = "DrawWord"
  show CmdDefinePathData = "DefinePathData"
  show CmdUpdateAnimationState = "UpdateAnimationState"
