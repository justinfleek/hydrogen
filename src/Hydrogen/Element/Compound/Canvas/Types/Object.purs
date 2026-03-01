-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // element // compound // canvas // types // object
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Object Types — Object representation with compositing.
-- |
-- | ## Scope
-- |
-- | This module defines the CanvasObject type with full compositing support:
-- |
-- | - **Bounds & Transform**: Spatial properties in canvas coordinates
-- | - **Layer Ordering**: Z-index based stacking
-- | - **Blend Modes**: All standard blend modes from Schema
-- | - **Clipping**: Binary clip paths
-- | - **Masking**: Soft alpha masks
-- | - **Track Mattes**: Layer-based masking (After Effects style)
-- |
-- | ## Compositing Order
-- |
-- | When rendering, compositing is applied in this order:
-- | 1. Apply object's clip path (binary visibility)
-- | 2. Apply object's mask (soft alpha)
-- | 3. If trackMatte is set, use the referenced matte layer for masking
-- | 4. Apply blend mode when compositing onto layers below
-- | 5. Apply object opacity as final alpha multiplier
-- |
-- | ## Dependencies
-- |
-- | - Schema.Color.Blend (BlendMode)
-- | - Schema.Geometry.Mask (Mask)
-- | - Schema.Geometry.ClipPath (ClipPath)
-- | - Schema.Motion.Composition (TrackMatteMode)
-- | - Schema.Geometry.Transform (Transform2D)

module Hydrogen.Element.Compound.Canvas.Types.Object
  ( -- * Object Types
    CanvasObject
  , defaultCanvasObject
  , objectId
  , objectBounds
  , objectTransform
  , objectVisible
  , objectLocked
  , objectName
  , objectZIndex
  , objectBlendMode
  , objectOpacity
  , objectClipPath
  , objectMask
  , objectTrackMatteMode
  , objectMatteLayerId
  
  -- * Re-exports for compositing
  , module Blend
  , module Mask
  , module ClipPath
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Transform (Transform2D, identityTransform)

-- Compositing imports
import Hydrogen.Schema.Color.Blend as Blend
import Hydrogen.Schema.Geometry.Mask as Mask
import Hydrogen.Schema.Geometry.ClipPath as ClipPath
import Hydrogen.Schema.Motion.Composition as Composition

-- Object ID from sibling module
import Hydrogen.Element.Compound.Canvas.Types.ObjectId (CanvasObjectId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // object types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A canvas object with bounds, transform, and compositing properties.
-- |
-- | This is the complete interface needed for canvas operations including
-- | layer stacking with 1+N layers, blend modes, masks, clips, and mattes.
-- |
-- | ## Layer Ordering
-- |
-- | Objects are rendered in ascending zIndex order (lower = behind).
-- | Multiple objects can share the same zIndex; tie-breaking uses array order.
type CanvasObject =
  { -- Identity
    id :: CanvasObjectId
  , name :: String
  
  -- Spatial
  , bounds :: { x :: Number, y :: Number, width :: Number, height :: Number }
  , transform :: Transform2D
  
  -- Visibility & Interaction
  , visible :: Boolean
  , locked :: Boolean
  
  -- Layer ordering
  , zIndex :: Int
  
  -- Compositing: Blend Mode
  , blendMode :: Blend.BlendMode            -- ^ How this layer blends with layers below
  , opacity :: Number                        -- ^ Object opacity (0.0-1.0)
  
  -- Compositing: Clipping
  , clipPath :: Maybe ClipPath.ClipPath      -- ^ Binary clip (inside/outside)
  
  -- Compositing: Masking
  , mask :: Maybe Mask.Mask                  -- ^ Soft alpha mask
  
  -- Compositing: Track Matte
  , trackMatteMode :: Composition.TrackMatteMode  -- ^ How to use matte layer
  , matteLayerId :: Maybe CanvasObjectId     -- ^ Reference to matte layer (if any)
  }

-- | Get object ID.
objectId :: CanvasObject -> CanvasObjectId
objectId obj = obj.id

-- | Get object bounds in canvas space.
objectBounds :: CanvasObject -> { x :: Number, y :: Number, width :: Number, height :: Number }
objectBounds obj = obj.bounds

-- | Get object transform.
objectTransform :: CanvasObject -> Transform2D
objectTransform obj = obj.transform

-- | Check if object is visible.
objectVisible :: CanvasObject -> Boolean
objectVisible obj = obj.visible

-- | Check if object is locked.
objectLocked :: CanvasObject -> Boolean
objectLocked obj = obj.locked

-- | Get object name.
objectName :: CanvasObject -> String
objectName obj = obj.name

-- | Get object z-index (layer order).
objectZIndex :: CanvasObject -> Int
objectZIndex obj = obj.zIndex

-- | Get object blend mode.
objectBlendMode :: CanvasObject -> Blend.BlendMode
objectBlendMode obj = obj.blendMode

-- | Get object opacity (0.0-1.0).
objectOpacity :: CanvasObject -> Number
objectOpacity obj = obj.opacity

-- | Get object clip path (if any).
objectClipPath :: CanvasObject -> Maybe ClipPath.ClipPath
objectClipPath obj = obj.clipPath

-- | Get object mask (if any).
objectMask :: CanvasObject -> Maybe Mask.Mask
objectMask obj = obj.mask

-- | Get object track matte mode.
objectTrackMatteMode :: CanvasObject -> Composition.TrackMatteMode
objectTrackMatteMode obj = obj.trackMatteMode

-- | Get reference to matte layer (if any).
objectMatteLayerId :: CanvasObject -> Maybe CanvasObjectId
objectMatteLayerId obj = obj.matteLayerId

-- | Create a default canvas object with no compositing effects.
-- |
-- | Uses Normal blend mode, full opacity, no clip/mask/matte.
defaultCanvasObject :: CanvasObjectId -> String -> CanvasObject
defaultCanvasObject objId name =
  { id: objId
  , name: name
  , bounds: { x: 0.0, y: 0.0, width: 100.0, height: 100.0 }
  , transform: identityTransform
  , visible: true
  , locked: false
  , zIndex: 0
  , blendMode: Blend.Normal
  , opacity: 1.0
  , clipPath: Nothing
  , mask: Nothing
  , trackMatteMode: Composition.TMNone
  , matteLayerId: Nothing
  }
