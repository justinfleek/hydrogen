-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // motion // shapes // modifiers // taper
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stroke taper properties.
-- |
-- | Tapers the stroke width from start to end of the path.
-- | After Effects introduced this in CC 2020 for shape layers.
-- | All values are bounded and composable.

module Hydrogen.Schema.Motion.Shapes.Modifiers.Taper
  ( -- * Stroke Taper
    StrokeTaper
  , strokeTaper
  , noTaper
  , defaultTaper
  , taperFromStart
  , taperToEnd
  , taperBothEnds
  ) where

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Shapes.Operators 
  ( Percent
  , percent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // stroke // taper
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke taper properties.
-- |
-- | Tapers the stroke width from start to end of the path.
-- | After Effects introduced this in CC 2020 for shape layers.
-- |
-- | ## Properties
-- |
-- | - **startLength**: How far along path to start tapering (0-100%)
-- | - **endLength**: How far from end to start tapering (0-100%)
-- | - **startWidth**: Width at start (0-100%)
-- | - **endWidth**: Width at end (0-100%)
-- | - **startEase**: Ease curve at start (0-100%)
-- | - **endEase**: Ease curve at end (0-100%)
type StrokeTaper =
  { enabled :: Boolean           -- ^ Whether taper is active
  , startLength :: Percent       -- ^ Start taper length (0-100%)
  , endLength :: Percent         -- ^ End taper length (0-100%)
  , startWidth :: Percent        -- ^ Width at start (0-100%)
  , endWidth :: Percent          -- ^ Width at end (0-100%)
  , startEase :: Percent         -- ^ Start ease (0-100%)
  , endEase :: Percent           -- ^ End ease (0-100%)
  }

-- | Create stroke taper with explicit values.
strokeTaper
  :: Boolean     -- ^ Enabled
  -> Number      -- ^ Start length (%)
  -> Number      -- ^ End length (%)
  -> Number      -- ^ Start width (%)
  -> Number      -- ^ End width (%)
  -> Number      -- ^ Start ease (%)
  -> Number      -- ^ End ease (%)
  -> StrokeTaper
strokeTaper en sl el sw ew se ee =
  { enabled: en
  , startLength: percent sl
  , endLength: percent el
  , startWidth: percent sw
  , endWidth: percent ew
  , startEase: percent se
  , endEase: percent ee
  }

-- | No taper (constant width).
noTaper :: StrokeTaper
noTaper =
  { enabled: false
  , startLength: percent 0.0
  , endLength: percent 0.0
  , startWidth: percent 100.0
  , endWidth: percent 100.0
  , startEase: percent 0.0
  , endEase: percent 0.0
  }

-- | Default taper: enabled, symmetric fade.
defaultTaper :: StrokeTaper
defaultTaper =
  { enabled: true
  , startLength: percent 10.0
  , endLength: percent 10.0
  , startWidth: percent 0.0
  , endWidth: percent 0.0
  , startEase: percent 50.0
  , endEase: percent 50.0
  }

-- | Taper to point at start.
taperFromStart :: Number -> StrokeTaper
taperFromStart lengthPercent =
  { enabled: true
  , startLength: percent (clampNumber 0.0 100.0 lengthPercent)
  , endLength: percent 0.0
  , startWidth: percent 0.0
  , endWidth: percent 100.0
  , startEase: percent 50.0
  , endEase: percent 0.0
  }

-- | Taper to point at end.
taperToEnd :: Number -> StrokeTaper
taperToEnd lengthPercent =
  { enabled: true
  , startLength: percent 0.0
  , endLength: percent (clampNumber 0.0 100.0 lengthPercent)
  , startWidth: percent 100.0
  , endWidth: percent 0.0
  , startEase: percent 0.0
  , endEase: percent 50.0
  }

-- | Taper both ends.
taperBothEnds :: Number -> Number -> StrokeTaper
taperBothEnds startLen endLen =
  { enabled: true
  , startLength: percent (clampNumber 0.0 100.0 startLen)
  , endLength: percent (clampNumber 0.0 100.0 endLen)
  , startWidth: percent 0.0
  , endWidth: percent 0.0
  , startEase: percent 50.0
  , endEase: percent 50.0
  }
