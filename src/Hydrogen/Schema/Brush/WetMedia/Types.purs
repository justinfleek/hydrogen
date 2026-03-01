-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brush // wetmedia // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WetMedia Types — ADTs for wet paint simulation.
-- |
-- | ## Design Philosophy
-- |
-- | Wet media simulation enables natural media behaviors in digital painting.
-- | Different media types (watercolor, oil, acrylic) have distinct properties
-- | for wetness, flow, and interaction with the canvas.
-- |
-- | ## Media Types
-- |
-- | - **Watercolor**: Transparent, flows, pools at edges
-- | - **OilPaint**: Thick, blends, supports impasto
-- | - **Acrylic**: Quick-drying, versatile coverage
-- | - **Gouache**: Opaque watercolor behavior
-- | - **Ink**: Fluid, bleeds at edges
-- | - **WetIntoWet**: Painting into existing wet areas
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Brush.WetMedia.Types
  ( -- * WetMediaType ADT
    WetMediaType
      ( Watercolor
      , OilPaint
      , Acrylic
      , Gouache
      , Ink
      , WetIntoWet
      )
  , allWetMediaTypes
  , wetMediaTypeDescription
  , isTransparentMedia
  , isThickMedia
  , defaultDryingRate
  
  -- * WetInteraction ADT
  , WetInteraction
      ( WetOnDry
      , WetOnWet
      , WetInWet
      , DryBrush
      )
  , allWetInteractions
  , wetInteractionDescription
  , blendIntensity
  
  -- * Debug & Serialization Helpers
  , wetMediaTypeDebugInfo
  , wetMediaTypeToId
  , sameWetMediaTypeKind
  , wetInteractionDebugInfo
  , wetInteractionToId
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (==)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // wet media type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of wet media being simulated.
-- |
-- | Each type has distinct characteristics for flow, transparency,
-- | drying, and interaction with the canvas.
data WetMediaType
  = Watercolor   -- ^ Transparent, flows, pools at edges
  | OilPaint     -- ^ Thick, blends, impasto capable
  | Acrylic      -- ^ Quick-drying, versatile, plastic feel
  | Gouache      -- ^ Opaque watercolor, matte finish
  | Ink          -- ^ Fluid, bleeds at edges, permanent
  | WetIntoWet   -- ^ Painting into existing wet paint

derive instance eqWetMediaType :: Eq WetMediaType
derive instance ordWetMediaType :: Ord WetMediaType

instance showWetMediaType :: Show WetMediaType where
  show Watercolor = "(WetMediaType Watercolor)"
  show OilPaint = "(WetMediaType OilPaint)"
  show Acrylic = "(WetMediaType Acrylic)"
  show Gouache = "(WetMediaType Gouache)"
  show Ink = "(WetMediaType Ink)"
  show WetIntoWet = "(WetMediaType WetIntoWet)"

-- | All wet media type variants.
allWetMediaTypes :: Array WetMediaType
allWetMediaTypes =
  [ Watercolor
  , OilPaint
  , Acrylic
  , Gouache
  , Ink
  , WetIntoWet
  ]

-- | Human-readable description of each wet media type.
wetMediaTypeDescription :: WetMediaType -> String
wetMediaTypeDescription Watercolor =
  "Transparent, flows and pools, pigment settles in texture"
wetMediaTypeDescription OilPaint =
  "Thick and buttery, blends smoothly, supports impasto"
wetMediaTypeDescription Acrylic =
  "Quick-drying, versatile coverage, plastic finish"
wetMediaTypeDescription Gouache =
  "Opaque watercolor, reactivates when wet, matte finish"
wetMediaTypeDescription Ink =
  "Fluid and permanent, bleeds at edges, high contrast"
wetMediaTypeDescription WetIntoWet =
  "Painting into existing wet areas, aggressive blending"

-- | Check if media type is transparent.
isTransparentMedia :: WetMediaType -> Boolean
isTransparentMedia Watercolor = true
isTransparentMedia Ink = true
isTransparentMedia _ = false

-- | Check if media type is thick/impasto capable.
isThickMedia :: WetMediaType -> Boolean
isThickMedia OilPaint = true
isThickMedia Acrylic = true
isThickMedia _ = false

-- | Default drying rate for each media type (percent per second).
defaultDryingRate :: WetMediaType -> Number
defaultDryingRate Watercolor = 30.0
defaultDryingRate OilPaint = 5.0
defaultDryingRate Acrylic = 50.0
defaultDryingRate Gouache = 40.0
defaultDryingRate Ink = 60.0
defaultDryingRate WetIntoWet = 20.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // wet interaction
-- ═════════════════════════════════════════════════════════════════════════════

-- | How wet paint interacts with the canvas.
-- |
-- | Controls blending behavior based on canvas wetness state.
data WetInteraction
  = WetOnDry   -- ^ Normal painting on dry canvas
  | WetOnWet   -- ^ Colors blend where canvas is wet
  | WetInWet   -- ^ Aggressive blending, watercolor blooms
  | DryBrush   -- ^ Minimal paint, texture shows through

derive instance eqWetInteraction :: Eq WetInteraction
derive instance ordWetInteraction :: Ord WetInteraction

instance showWetInteraction :: Show WetInteraction where
  show WetOnDry = "(WetInteraction WetOnDry)"
  show WetOnWet = "(WetInteraction WetOnWet)"
  show WetInWet = "(WetInteraction WetInWet)"
  show DryBrush = "(WetInteraction DryBrush)"

-- | All wet interaction variants.
allWetInteractions :: Array WetInteraction
allWetInteractions =
  [ WetOnDry
  , WetOnWet
  , WetInWet
  , DryBrush
  ]

-- | Human-readable description of each wet interaction.
wetInteractionDescription :: WetInteraction -> String
wetInteractionDescription WetOnDry =
  "Normal painting on dry canvas, paint sits on top"
wetInteractionDescription WetOnWet =
  "Colors blend where canvas is wet, soft edges"
wetInteractionDescription WetInWet =
  "Aggressive blending with blooms and backruns"
wetInteractionDescription DryBrush =
  "Minimal paint, texture shows through, rough edges"

-- | Blend intensity for each interaction mode (0-1).
blendIntensity :: WetInteraction -> Number
blendIntensity WetOnDry = 0.0
blendIntensity WetOnWet = 0.5
blendIntensity WetInWet = 1.0
blendIntensity DryBrush = 0.1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // debug helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info for wet media type.
wetMediaTypeDebugInfo :: WetMediaType -> String
wetMediaTypeDebugInfo mtype =
  "WetMediaType: " <> wetMediaTypeToId mtype <>
  " — " <> wetMediaTypeDescription mtype

-- | Convert wet media type to string ID.
wetMediaTypeToId :: WetMediaType -> String
wetMediaTypeToId Watercolor = "watercolor"
wetMediaTypeToId OilPaint = "oil"
wetMediaTypeToId Acrylic = "acrylic"
wetMediaTypeToId Gouache = "gouache"
wetMediaTypeToId Ink = "ink"
wetMediaTypeToId WetIntoWet = "wet-into-wet"

-- | Check if two wet media types are the same kind.
sameWetMediaTypeKind :: WetMediaType -> WetMediaType -> Boolean
sameWetMediaTypeKind a b = wetMediaTypeToId a == wetMediaTypeToId b

-- | Generate debug info for wet interaction.
wetInteractionDebugInfo :: WetInteraction -> String
wetInteractionDebugInfo interaction =
  "WetInteraction: " <> wetInteractionToId interaction <>
  " — " <> wetInteractionDescription interaction

-- | Convert wet interaction to string ID.
wetInteractionToId :: WetInteraction -> String
wetInteractionToId WetOnDry = "wet-on-dry"
wetInteractionToId WetOnWet = "wet-on-wet"
wetInteractionToId WetInWet = "wet-in-wet"
wetInteractionToId DryBrush = "dry-brush"
