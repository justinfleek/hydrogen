-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // tour // render // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Helper Functions for Tour Rendering
-- |
-- | Utility functions used across multiple render modules for placement
-- | conversion and positioning.

module Hydrogen.Tour.Render.Helpers
  ( placementToClass
  , sideToString
  ) where

import Hydrogen.Tour.Types (Placement, Side(Bottom, Left, Right, Top))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert placement to positioning class
placementToClass :: Placement -> String
placementToClass placement = case placement.side of
  Top -> "bottom-full mb-3"
  Right -> "left-full ml-3"
  Bottom -> "top-full mt-3"
  Left -> "right-full mr-3"

-- | Convert side to string
sideToString :: Side -> String
sideToString = case _ of
  Top -> "top"
  Right -> "right"
  Bottom -> "bottom"
  Left -> "left"
