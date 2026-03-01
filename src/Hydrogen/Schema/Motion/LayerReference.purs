-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // motion // layer-reference
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LayerReference — Unified namespace for layer-to-layer relationships.
-- |
-- | ## Design Philosophy
-- |
-- | In motion graphics, layers need to reference each other for many purposes:
-- |
-- | - **Track Mattes**: Alpha/luma from one layer masks another
-- | - **Clipping Groups**: Layer clips to the layer directly below
-- | - **Parenting**: Transform inheritance from parent layer
-- | - **Effect Inputs**: Effects reference other layers (displacement, set matte)
-- | - **Expression Links**: Property values driven by other layer properties
-- | - **Masks**: Vector paths attached to layers
-- |
-- | This module provides a **unified reference system** where every layer has
-- | a unique namespace (UUID5-based) and can be referenced by type-safe links.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - **Types**: Core reference types (LayerRef, PropertyRef, EffectRef, MaskRef)
-- | - **Purpose**: Reference purpose and layer links
-- | - **TrackMatte**: Track matte relationships
-- | - **ClippingGroup**: Clipping group management
-- | - **EffectRef**: Effect layer references and channels
-- | - **Expression**: Expression links and mask modes
-- | - **Stack**: Layer stack management
-- | - **Validation**: Reference validation and composition namespace
-- |
-- | ## Dependencies
-- |
-- | - Schema.Motion.Composition (TrackMatteMode)
-- | - Schema.Attestation.UUID5 (UUID5, namespaces)

module Hydrogen.Schema.Motion.LayerReference
  ( -- * All submodules re-exported
    module ReExportTypes
  , module ReExportPurpose
  , module ReExportTrackMatte
  , module ReExportClippingGroup
  , module ReExportEffectRef
  , module ReExportExpression
  , module ReExportStack
  , module ReExportValidation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- Re-export all submodules

import Hydrogen.Schema.Motion.LayerReference.Types
  ( LayerRef(LayerRef)
  , PropertyRef(PropertyRef)
  , EffectRef(EffectRef)
  , MaskRef(MaskRef)
  , mkLayerRef
  , mkLayerRefFromUUID
  , mkPropertyRef
  , mkPropertyRefFromUUID
  , mkEffectRef
  , mkEffectRefFromUUID
  , mkMaskRef
  , mkMaskRefFromUUID
  , layerRefId
  , layerRefUUID
  , propertyRefPath
  , propertyRefUUID
  , effectRefUUID
  , maskRefUUID
  ) as ReExportTypes

import Hydrogen.Schema.Motion.LayerReference.Purpose
  ( ReferencePurpose
      ( RPTrackMatte
      , RPClipping
      , RPParent
      , RPEffectInput
      , RPExpressionLink
      , RPMaskSource
      , RPControlLayer
      , RPPrecompSource
      )
  , allReferencePurposes
  , referencePurposeToString
  , LayerLink(LayerLink)
  , mkLayerLink
  , linkSource
  , linkTarget
  , linkPurpose
  ) as ReExportPurpose

import Hydrogen.Schema.Motion.LayerReference.TrackMatte
  ( TrackMatteLink(TrackMatteLink)
  , mkTrackMatteLink
  , trackMatteLinkSource
  , trackMatteLinkMatte
  , trackMatteLinkMode
  ) as ReExportTrackMatte

import Hydrogen.Schema.Motion.LayerReference.ClippingGroup
  ( ClippingGroup(ClippingGroup)
  , mkClippingGroup
  , clippingGroupBase
  , clippingGroupMembers
  , addToClippingGroup
  , removeFromClippingGroup
  , isInClippingGroup
  ) as ReExportClippingGroup

import Hydrogen.Schema.Motion.LayerReference.EffectRef
  ( EffectChannel
      ( ECFull
      , ECRed
      , ECGreen
      , ECBlue
      , ECAlpha
      , ECLuminance
      , ECLightness
      , ECSaturation
      , ECHue
      , ECEffectsAndMasks
      , ECSourceOnly
      )
  , allEffectChannels
  , effectChannelToString
  , EffectLayerRef(EffectLayerRef)
  , mkEffectLayerRef
  , effectRefTargetLayer
  , effectRefChannel
  ) as ReExportEffectRef

import Hydrogen.Schema.Motion.LayerReference.Expression
  ( ExpressionLink(ExpressionLink)
  , mkExpressionLink
  , expressionLinkSource
  , expressionLinkTarget
  , expressionLinkExpression
  , MaskMode
      ( MMNone
      , MMAdd
      , MMSubtract
      , MMIntersect
      , MMLighten
      , MMDarken
      , MMDifference
      )
  , allMaskModes
  , maskModeToString
  ) as ReExportExpression

import Hydrogen.Schema.Motion.LayerReference.Stack
  ( LayerStack(LayerStack)
  , mkLayerStack
  , layerStackLayers
  , layerStackLinks
  , addLayerToStack
  , removeLayerFromStack
  , moveLayerInStack
  , getLayerAtIndex
  , getLayerIndex
  , resolveLayerRef
  , resolveAllReferences
  ) as ReExportStack

import Hydrogen.Schema.Motion.LayerReference.Validation
  ( validateReference
  , validateAllReferences
  , ReferenceError
      ( RELayerNotFound
      , REPropertyNotFound
      , RECircularReference
      , RESelfReference
      , REInvalidMatteOrder
      )
  , referenceErrorToString
  , CompositionNamespace(CompositionNamespace)
  , mkCompositionNamespace
  , registerLayer
  , unregisterLayer
  , lookupLayer
  , lookupProperty
  , allLayerIds
  , allPropertyPaths
  ) as ReExportValidation
