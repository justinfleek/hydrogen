-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // motion // layer // full
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete Layer type combining LayerBase with LayerContent.
-- |
-- | This module provides the full Layer representation that pairs the common
-- | layer properties (LayerBase) with type-specific content (LayerContent).
-- |
-- | ## Architecture
-- |
-- | ```purescript
-- | Layer = { base :: LayerBase, content :: LayerContent }
-- | ```
-- |
-- | The Layer type ensures that:
-- | - Every layer has complete base properties (timing, visibility, transforms)
-- | - Every layer has type-appropriate content
-- | - The content type matches the layer type in the base
-- |
-- | ## Validation
-- |
-- | The `mkLayer` smart constructor validates that the LayerContent type
-- | matches the LayerType in the LayerBase. This prevents invalid combinations
-- | like an Image layer with Text content.

module Hydrogen.Schema.Motion.Layer.Full
  ( -- * Layer Type
    Layer(Layer)
  , mkLayer
  , mkLayerUnchecked
  
  -- * Accessors
  , layerBase
  , layerContent
  
  -- * Validation
  , isLayerValid
  , layerContentMatchesType
  
  -- * Transformations
  , mapLayerBase
  , mapLayerContent
  , setLayerContent
  , updateLayerBase
  
  -- * Predicates (delegating to base)
  , fullLayerVisible
  , fullLayerLocked
  , fullLayerIs3D
  , fullLayerIsGenerated
  , fullLayerType
  
  -- * Layer Type Queries
  , isImageLayer
  , isVideoLayer
  , isTextLayer
  , isShapeLayer
  , isSolidLayer
  , isGeneratedLayer
  
  -- * Content Extraction
  , extractImageContent
  , extractVideoContent
  , extractTextContent
  , extractGeneratedContent
  
  ) where

import Prelude
  ( class Eq
  , class Show
  , (==)
  , (&&)
  , (<>)
  , ($)
  , otherwise
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Motion.Layer 
  ( LayerBase
  , LayerType(LTImage, LTVideo, LTText, LTShape, LTSolid, LTGenerated)
  , layerType
  , layerVisible
  , layerLocked
  , layerIs3D
  , layerEnabled
  )
import Hydrogen.Schema.Motion.LayerContent
  ( LayerContent(LCImage, LCVideo, LCAudio, LCSolid, LCText, LCShape, LCNull, LCCamera, LCLight, LCAdjustment, LCEffect, LCPreComp, LCGroup, LCNestedComp, LCParticle, LCDepth, LCNormal, LCGenerated, LCMatte, LCControl, LCSpline, LCPath, LCPose, LCModel, LCPointCloud, LCDepthflow)
  , contentToLayerType
  , isContentGenerated
  , ImageContent
  , VideoContent
  , TextContent
  , GeneratedContent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | A complete layer with base properties and type-specific content.
-- |
-- | The Layer record pairs LayerBase (common properties) with LayerContent
-- | (type-specific data). The content type should match the layer type.
newtype Layer = Layer
  { base :: LayerBase
  , content :: LayerContent
  }

derive instance eqLayer :: Eq Layer

instance showLayer :: Show Layer where
  show (Layer l) = "Layer(" <> show l.base <> ", " <> show l.content <> ")"

-- | Smart constructor that validates content matches layer type.
-- |
-- | Returns Nothing if the content type doesn't match the layer type.
mkLayer :: LayerBase -> LayerContent -> Maybe Layer
mkLayer base content
  | layerContentMatchesType base content = Just $ Layer { base, content }
  | otherwise = Nothing

-- | Constructor without validation (use when you're sure types match).
-- |
-- | Prefer `mkLayer` in most cases.
mkLayerUnchecked :: LayerBase -> LayerContent -> Layer
mkLayerUnchecked base content = Layer { base, content }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the layer's base properties.
layerBase :: Layer -> LayerBase
layerBase (Layer l) = l.base

-- | Get the layer's type-specific content.
layerContent :: Layer -> LayerContent
layerContent (Layer l) = l.content

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if layer content type matches the base layer type.
layerContentMatchesType :: LayerBase -> LayerContent -> Boolean
layerContentMatchesType base content =
  layerType base == contentToLayerType content

-- | Check if a layer is valid (content matches type).
isLayerValid :: Layer -> Boolean
isLayerValid (Layer l) = layerContentMatchesType l.base l.content

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a transformation to the layer's base properties.
mapLayerBase :: (LayerBase -> LayerBase) -> Layer -> Layer
mapLayerBase f (Layer l) = Layer { base: f l.base, content: l.content }

-- | Apply a transformation to the layer's content.
mapLayerContent :: (LayerContent -> LayerContent) -> Layer -> Layer
mapLayerContent f (Layer l) = Layer { base: l.base, content: f l.content }

-- | Set new content for a layer.
-- |
-- | Returns Nothing if the new content type doesn't match the layer type.
setLayerContent :: LayerContent -> Layer -> Maybe Layer
setLayerContent content (Layer l)
  | layerContentMatchesType l.base content = Just $ Layer { base: l.base, content }
  | otherwise = Nothing

-- | Update the layer base with a transformation.
updateLayerBase :: (LayerBase -> LayerBase) -> Layer -> Layer
updateLayerBase = mapLayerBase

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if the full layer is visible.
fullLayerVisible :: Layer -> Boolean
fullLayerVisible l = layerVisible (layerBase l) && layerEnabled (layerBase l)

-- | Check if the full layer is locked.
fullLayerLocked :: Layer -> Boolean
fullLayerLocked l = layerLocked (layerBase l)

-- | Check if the full layer is 3D.
fullLayerIs3D :: Layer -> Boolean
fullLayerIs3D l = layerIs3D (layerBase l)

-- | Check if the layer contains AI-generated content.
fullLayerIsGenerated :: Layer -> Boolean
fullLayerIsGenerated l = isContentGenerated (layerContent l)

-- | Get the layer type from the base.
fullLayerType :: Layer -> LayerType
fullLayerType l = layerType (layerBase l)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // layer // type // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if this is an image layer.
isImageLayer :: Layer -> Boolean
isImageLayer l = case fullLayerType l of
  LTImage -> true
  _ -> false

-- | Check if this is a video layer.
isVideoLayer :: Layer -> Boolean
isVideoLayer l = case fullLayerType l of
  LTVideo -> true
  _ -> false

-- | Check if this is a text layer.
isTextLayer :: Layer -> Boolean
isTextLayer l = case fullLayerType l of
  LTText -> true
  _ -> false

-- | Check if this is a shape layer.
isShapeLayer :: Layer -> Boolean
isShapeLayer l = case fullLayerType l of
  LTShape -> true
  _ -> false

-- | Check if this is a solid layer.
isSolidLayer :: Layer -> Boolean
isSolidLayer l = case fullLayerType l of
  LTSolid -> true
  _ -> false

-- | Check if this is a generated/AI content layer.
isGeneratedLayer :: Layer -> Boolean
isGeneratedLayer l = case fullLayerType l of
  LTGenerated -> true
  _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // content // extraction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract ImageContent if this is an image layer.
extractImageContent :: Layer -> Maybe ImageContent
extractImageContent l = case layerContent l of
  LCImage c -> Just c
  _ -> Nothing

-- | Extract VideoContent if this is a video layer.
extractVideoContent :: Layer -> Maybe VideoContent
extractVideoContent l = case layerContent l of
  LCVideo c -> Just c
  _ -> Nothing

-- | Extract TextContent if this is a text layer.
extractTextContent :: Layer -> Maybe TextContent
extractTextContent l = case layerContent l of
  LCText c -> Just c
  _ -> Nothing

-- | Extract GeneratedContent if this is a generated layer.
extractGeneratedContent :: Layer -> Maybe GeneratedContent
extractGeneratedContent l = case layerContent l of
  LCGenerated c -> Just c
  _ -> Nothing
