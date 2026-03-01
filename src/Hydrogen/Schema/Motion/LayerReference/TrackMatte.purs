-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // layer-reference // track-matte
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Track matte relationships between layers.
-- |
-- | ## Track Mattes
-- |
-- | A track matte uses one layer's alpha or luminance to determine
-- | another layer's transparency. The matte layer sits directly above
-- | the layer being matted in the layer stack.
-- |
-- | ## Modes
-- |
-- | - Alpha: Matte layer's alpha channel controls transparency
-- | - Alpha Inverted: Inverted alpha channel
-- | - Luma: Matte layer's luminance controls transparency
-- | - Luma Inverted: Inverted luminance
-- |
-- | ## Dependencies
-- |
-- | - LayerReference.Types (LayerRef)
-- | - Schema.Motion.Composition (TrackMatteMode)

module Hydrogen.Schema.Motion.LayerReference.TrackMatte
  ( -- * Track Matte Link
    TrackMatteLink(..)
  , mkTrackMatteLink
  , trackMatteLinkSource
  , trackMatteLinkMatte
  , trackMatteLinkMode
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Motion.LayerReference.Types (LayerRef)
import Hydrogen.Schema.Motion.Composition (TrackMatteMode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // track // matte link
-- ═════════════════════════════════════════════════════════════════════════════

-- | Track matte relationship between layers.
-- |
-- | The source layer uses the matte layer's alpha or luminance
-- | to determine its own transparency.
newtype TrackMatteLink = TrackMatteLink
  { source :: LayerRef        -- Layer being matted
  , matte :: LayerRef         -- Layer providing the matte
  , mode :: TrackMatteMode    -- How to interpret the matte
  , inverted :: Boolean       -- Invert the matte
  , preserveUnderlying :: Boolean  -- Keep matte layer visible
  }

derive instance eqTrackMatteLink :: Eq TrackMatteLink

instance showTrackMatteLink :: Show TrackMatteLink where
  show (TrackMatteLink tm) = 
    show tm.source <> " matted by " <> show tm.matte <> " (" <> show tm.mode <> ")"

-- | Create a track matte link.
mkTrackMatteLink :: LayerRef -> LayerRef -> TrackMatteMode -> TrackMatteLink
mkTrackMatteLink source matte mode = TrackMatteLink
  { source, matte, mode
  , inverted: false
  , preserveUnderlying: false
  }

-- | Get source layer of track matte.
trackMatteLinkSource :: TrackMatteLink -> LayerRef
trackMatteLinkSource (TrackMatteLink tm) = tm.source

-- | Get matte layer.
trackMatteLinkMatte :: TrackMatteLink -> LayerRef
trackMatteLinkMatte (TrackMatteLink tm) = tm.matte

-- | Get track matte mode.
trackMatteLinkMode :: TrackMatteLink -> TrackMatteMode
trackMatteLinkMode (TrackMatteLink tm) = tm.mode
