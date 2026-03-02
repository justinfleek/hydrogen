-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // graph // viewport // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport Animation and Constraints — Smooth transitions and movement limits.
-- |
-- | ## Design Philosophy
-- |
-- | Viewport changes should feel natural. This module provides:
-- |
-- | - **Transitions**: How viewport changes animate (instant, linear, spring)
-- | - **Constraints**: Limits on zoom and pan to keep content visible
-- |
-- | ## Transition Types
-- |
-- | - **Instant**: No animation, immediate state change
-- | - **Linear**: Constant velocity interpolation
-- | - **EaseInOut**: Smooth acceleration/deceleration
-- | - **Spring**: Physics-based with momentum and settle
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Data.Maybe
-- | - Hydrogen.Schema.Graph.Viewport.Types
-- | - Hydrogen.Schema.Graph.Viewport.State

module Hydrogen.Schema.Graph.Viewport.Animation
  ( -- * Viewport Animation
    ViewportTransition(Instant, Linear, EaseInOut, Spring)
  , viewportTransition
  , instantTransition
  , smoothTransition
  , springTransition
  , transitionDuration
  , isAnimating
  
  -- * Viewport Constraints
  , ViewportConstraints
  , viewportConstraints
  , unconstrainedViewport
  , constrainZoom
  , constrainPan
  , withMinZoom
  , withMaxZoom
  , withPanBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (-)
  , max
  , min
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Graph.Viewport.Types
  ( ViewportZoom(ViewportZoom)
  , ViewportBounds
  , ViewportPosition
  , minZoom
  , maxZoom
  , boundsWidth
  , boundsHeight
  )

import Hydrogen.Schema.Graph.Viewport.State
  ( ViewportState
  , viewportBoundsAt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // viewport animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition style for viewport changes
data ViewportTransition
  = Instant                               -- ^ No animation
  | Linear Number                         -- ^ Linear interpolation (duration ms)
  | EaseInOut Number                      -- ^ Ease in-out (duration ms)
  | Spring Number Number                  -- ^ Spring physics (tension, friction)

derive instance eqViewportTransition :: Eq ViewportTransition

instance showViewportTransition :: Show ViewportTransition where
  show Instant = "instant"
  show (Linear d) = "linear(" <> show d <> "ms)"
  show (EaseInOut d) = "ease-in-out(" <> show d <> "ms)"
  show (Spring t f) = "spring(" <> show t <> "," <> show f <> ")"

-- | Create viewport transition
viewportTransition :: ViewportTransition -> ViewportTransition
viewportTransition t = t  -- Identity for now, could validate

-- | Instant transition (no animation)
instantTransition :: ViewportTransition
instantTransition = Instant

-- | Smooth ease-in-out transition
smoothTransition :: Number -> ViewportTransition
smoothTransition duration = EaseInOut duration

-- | Spring physics transition
springTransition :: Number -> Number -> ViewportTransition
springTransition tension friction = Spring tension friction

-- | Get transition duration in milliseconds
transitionDuration :: ViewportTransition -> Number
transitionDuration Instant = 0.0
transitionDuration (Linear d) = d
transitionDuration (EaseInOut d) = d
transitionDuration (Spring _ _) = 600.0  -- Approximate spring settle time

-- | Check if transition involves animation
isAnimating :: ViewportTransition -> Boolean
isAnimating Instant = false
isAnimating _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // viewport constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Constraints on viewport movement
type ViewportConstraints =
  { minZoom :: ViewportZoom
  , maxZoom :: ViewportZoom
  , panBounds :: Maybe ViewportBounds  -- ^ Nothing = unlimited pan
  }

-- | Create viewport constraints
viewportConstraints :: ViewportZoom -> ViewportZoom -> Maybe ViewportBounds -> ViewportConstraints
viewportConstraints minZ maxZ panB =
  { minZoom: minZ
  , maxZoom: maxZ
  , panBounds: panB
  }

-- | No constraints
unconstrainedViewport :: ViewportConstraints
unconstrainedViewport =
  { minZoom: minZoom
  , maxZoom: maxZoom
  , panBounds: Nothing
  }

-- | Constrain zoom to valid range
constrainZoom :: ViewportConstraints -> ViewportZoom -> ViewportZoom
constrainZoom c (ViewportZoom z) =
  let
    ViewportZoom minZ = c.minZoom
    ViewportZoom maxZ = c.maxZoom
  in
    ViewportZoom (max minZ (min maxZ z))

-- | Constrain pan to valid bounds
constrainPan :: ViewportConstraints -> ViewportState -> ViewportPosition -> ViewportPosition
constrainPan c v pos =
  case c.panBounds of
    Nothing -> pos
    Just bounds ->
      let
        visible = viewportBoundsAt v
        visibleW = boundsWidth visible
        visibleH = boundsHeight visible
        -- Keep viewport within pan bounds
        minX = bounds.left
        maxX = bounds.right - visibleW
        minY = bounds.top
        maxY = bounds.bottom - visibleH
      in
        { x: max minX (min maxX pos.x)
        , y: max minY (min maxY pos.y)
        }

-- | Set minimum zoom constraint
withMinZoom :: ViewportZoom -> ViewportConstraints -> ViewportConstraints
withMinZoom z c = c { minZoom = z }

-- | Set maximum zoom constraint
withMaxZoom :: ViewportZoom -> ViewportConstraints -> ViewportConstraints
withMaxZoom z c = c { maxZoom = z }

-- | Set pan bounds constraint
withPanBounds :: ViewportBounds -> ViewportConstraints -> ViewportConstraints
withPanBounds b c = c { panBounds = Just b }
