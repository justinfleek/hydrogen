-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // selection // marquee
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Marquee (rectangular drag) selection state management.
-- |
-- | ## Marquee Selection
-- |
-- | The marquee is a rectangular drag selection:
-- | 1. User presses mouse button (startMarquee)
-- | 2. User drags to define rectangle (updateMarquee)
-- | 3. User releases button (endMarquee)
-- | 4. Objects within rectangle are selected
-- |
-- | ## Dependencies
-- |
-- | - Selection.Types (MarqueeState)
-- | - Schema.Gestural.Selection (SelectionRect)

module Hydrogen.Element.Compound.Canvas.Selection.Marquee
  ( -- * Lifecycle
    startMarquee
  , updateMarquee
  , endMarquee
  
  -- * Accessors
  , marqueeRect
  , marqueeActive
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<)
  , not
  )

import Hydrogen.Schema.Gestural.Selection as GSelection
import Hydrogen.Element.Compound.Canvas.Selection.Types (MarqueeState)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // lifecycle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start a marquee selection.
startMarquee :: { x :: Number, y :: Number } -> MarqueeState
startMarquee point =
  { active: yes
  , startPoint: point
  , currentPoint: point
  }
  where
    yes = 1 < 2

-- | Update marquee position.
updateMarquee :: { x :: Number, y :: Number } -> MarqueeState -> MarqueeState
updateMarquee point state = state { currentPoint = point }

-- | End marquee selection.
endMarquee :: MarqueeState -> MarqueeState
endMarquee state = state { active = notYes }
  where
    yes = 1 < 2
    notYes = not yes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current marquee rectangle.
marqueeRect :: MarqueeState -> GSelection.SelectionRect
marqueeRect state = GSelection.rectFromPoints state.startPoint state.currentPoint

-- | Check if marquee is active.
marqueeActive :: MarqueeState -> Boolean
marqueeActive state = state.active
