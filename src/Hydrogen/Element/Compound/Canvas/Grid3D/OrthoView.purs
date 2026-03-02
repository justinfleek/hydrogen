-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // grid3d // orthoview
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Standard orthographic views for 3D editing.
-- |
-- | ## Views
-- |
-- | - Top/Bottom: Looking along Z axis
-- | - Front/Back: Looking along Y axis
-- | - Left/Right: Looking along X axis

module Hydrogen.Element.Compound.Canvas.Grid3D.OrthoView
  ( -- * View Type
    OrthoView(ViewTop, ViewBottom, ViewFront, ViewBack, ViewLeft, ViewRight)
  
  -- * View Properties
  , viewPlane
  , viewUp
  , viewRight
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , negate
  )

import Hydrogen.Element.Compound.Canvas.Grid3D.Types
  ( WorldPlane(PlaneXY, PlaneXZ, PlaneYZ)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // orthographic views
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard orthographic views.
data OrthoView
  = ViewTop      -- ^ Looking down -Z axis (sees XY plane)
  | ViewBottom   -- ^ Looking up +Z axis
  | ViewFront    -- ^ Looking down -Y axis (sees XZ plane)
  | ViewBack     -- ^ Looking down +Y axis
  | ViewLeft     -- ^ Looking down +X axis (sees YZ plane)
  | ViewRight    -- ^ Looking down -X axis

derive instance eqOrthoView :: Eq OrthoView
derive instance ordOrthoView :: Ord OrthoView

instance showOrthoView :: Show OrthoView where
  show ViewTop = "top"
  show ViewBottom = "bottom"
  show ViewFront = "front"
  show ViewBack = "back"
  show ViewLeft = "left"
  show ViewRight = "right"

-- | Get the world plane visible in an orthographic view.
viewPlane :: OrthoView -> WorldPlane
viewPlane ViewTop = PlaneXY
viewPlane ViewBottom = PlaneXY
viewPlane ViewFront = PlaneXZ
viewPlane ViewBack = PlaneXZ
viewPlane ViewLeft = PlaneYZ
viewPlane ViewRight = PlaneYZ

-- | Get the "up" vector for an orthographic view.
viewUp :: OrthoView -> { x :: Number, y :: Number, z :: Number }
viewUp ViewTop = { x: 0.0, y: 1.0, z: 0.0 }     -- Y up
viewUp ViewBottom = { x: 0.0, y: 1.0, z: 0.0 }  -- Y up
viewUp ViewFront = { x: 0.0, y: 0.0, z: 1.0 }   -- Z up
viewUp ViewBack = { x: 0.0, y: 0.0, z: 1.0 }    -- Z up
viewUp ViewLeft = { x: 0.0, y: 0.0, z: 1.0 }    -- Z up
viewUp ViewRight = { x: 0.0, y: 0.0, z: 1.0 }   -- Z up

-- | Get the "right" vector for an orthographic view.
viewRight :: OrthoView -> { x :: Number, y :: Number, z :: Number }
viewRight ViewTop = { x: 1.0, y: 0.0, z: 0.0 }     -- X right
viewRight ViewBottom = { x: 1.0, y: 0.0, z: 0.0 }  -- X right (flipped Y)
viewRight ViewFront = { x: 1.0, y: 0.0, z: 0.0 }   -- X right
viewRight ViewBack = { x: negate 1.0, y: 0.0, z: 0.0 }  -- -X right
viewRight ViewLeft = { x: 0.0, y: 0.0, z: 1.0 }    -- Z right
viewRight ViewRight = { x: 0.0, y: 0.0, z: negate 1.0 } -- -Z right
