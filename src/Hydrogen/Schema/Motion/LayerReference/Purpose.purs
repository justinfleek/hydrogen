-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // motion // layer-reference // purpose
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Reference purpose and layer link types.
-- |
-- | ## Reference Purposes
-- |
-- | Layers reference each other for various purposes:
-- | - Track mattes (alpha/luma masking)
-- | - Clipping groups
-- | - Transform parenting
-- | - Effect inputs
-- | - Expression links
-- | - Mask sources
-- | - Control layers
-- | - Precomp sources
-- |
-- | ## Dependencies
-- |
-- | - LayerReference.Types (LayerRef)

module Hydrogen.Schema.Motion.LayerReference.Purpose
  ( -- * Reference Purpose
    ReferencePurpose(RPTrackMatte, RPClipping, RPParent, RPEffectInput, RPExpressionLink, RPMaskSource, RPControlLayer, RPPrecompSource)
  , allReferencePurposes
  , referencePurposeToString
  
  -- * Layer Link
  , LayerLink(LayerLink)
  , mkLayerLink
  , linkSource
  , linkTarget
  , linkPurpose
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Motion.LayerReference.Types (LayerRef)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // reference // purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Purpose of a layer-to-layer reference.
-- |
-- | Determines how the reference is used during rendering.
data ReferencePurpose
  = RPTrackMatte       -- Source uses target as track matte
  | RPClipping         -- Source clips to target
  | RPParent           -- Source inherits transform from target
  | RPEffectInput      -- Effect on source uses target as input
  | RPExpressionLink   -- Property on source driven by target property
  | RPMaskSource       -- Mask path from target applied to source
  | RPControlLayer     -- Target controls source (slider, checkbox, etc.)
  | RPPrecompSource    -- Source is a precomp containing target

derive instance eqReferencePurpose :: Eq ReferencePurpose
derive instance ordReferencePurpose :: Ord ReferencePurpose

instance showReferencePurpose :: Show ReferencePurpose where
  show = referencePurposeToString

-- | All reference purposes for enumeration.
allReferencePurposes :: Array ReferencePurpose
allReferencePurposes =
  [ RPTrackMatte
  , RPClipping
  , RPParent
  , RPEffectInput
  , RPExpressionLink
  , RPMaskSource
  , RPControlLayer
  , RPPrecompSource
  ]

-- | Convert reference purpose to string.
referencePurposeToString :: ReferencePurpose -> String
referencePurposeToString RPTrackMatte = "track-matte"
referencePurposeToString RPClipping = "clipping"
referencePurposeToString RPParent = "parent"
referencePurposeToString RPEffectInput = "effect-input"
referencePurposeToString RPExpressionLink = "expression-link"
referencePurposeToString RPMaskSource = "mask-source"
referencePurposeToString RPControlLayer = "control-layer"
referencePurposeToString RPPrecompSource = "precomp-source"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layer // link
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic link between two layers.
-- |
-- | Represents any relationship where one layer references another.
newtype LayerLink = LayerLink
  { source :: LayerRef      -- The layer making the reference
  , target :: LayerRef      -- The layer being referenced
  , purpose :: ReferencePurpose
  , enabled :: Boolean
  }

derive instance eqLayerLink :: Eq LayerLink

instance showLayerLink :: Show LayerLink where
  show (LayerLink ll) = 
    show ll.source <> " --[" <> show ll.purpose <> "]--> " <> show ll.target

-- | Create a layer link.
mkLayerLink :: LayerRef -> LayerRef -> ReferencePurpose -> LayerLink
mkLayerLink source target purpose = LayerLink
  { source, target, purpose, enabled: true }

-- | Get source layer of link.
linkSource :: LayerLink -> LayerRef
linkSource (LayerLink ll) = ll.source

-- | Get target layer of link.
linkTarget :: LayerLink -> LayerRef
linkTarget (LayerLink ll) = ll.target

-- | Get link purpose.
linkPurpose :: LayerLink -> ReferencePurpose
linkPurpose (LayerLink ll) = ll.purpose
