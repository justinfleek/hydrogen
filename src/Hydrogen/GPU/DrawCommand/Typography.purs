-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // gpu // draw // typography
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DrawCommand.Typography — v2 Typography as Geometry Parameters
-- |
-- | This module provides smart constructors for v2 typography commands:
-- | - GlyphPath: Character as vector bezier paths
-- | - GlyphInstance: Animated glyph with per-character transform
-- | - Word: Collection of glyphs with shared animation state
-- | - PathData: Shared/deduplicated path data for instancing
-- | - AnimationState: Per-frame animation deltas
-- |
-- | Typography as geometry enables precise control over text rendering,
-- | including per-character animation, 3D transforms, and spring physics.

module Hydrogen.GPU.DrawCommand.Typography
  ( -- * GlyphPath Parameters
    glyphPathParams
  
  -- * GlyphInstance Parameters
  , glyphInstanceParams
  
  -- * Word Parameters
  , wordParams
  
  -- * PathData Parameters
  , pathDataParams
  
  -- * AnimationState Parameters
  , animationStateParams
  
  -- * Stagger Direction Constructors
  , staggerLeftToRight
  , staggerRightToLeft
  , staggerCenterOut
  , staggerEdgesIn
  , staggerTopToBottom
  , staggerBottomToTop
  , staggerRandom
  
  -- * Easing Function Constructors (new names)
  , easingIdLinear
  , easingIdInQuad
  , easingIdOutQuad
  , easingIdInOutQuad
  , easingIdInCubic
  , easingIdOutCubic
  , easingIdInOutCubic
  , easingIdInElastic
  , easingIdOutElastic
  , easingIdInOutElastic
  , easingIdInBounce
  , easingIdOutBounce
  , easingIdSpring
  
  -- * Backward-Compatible Easing (old names)
  , easeLinear
  , easeInQuad
  , easeOutQuad
  , easeInOutQuad
  , easeInCubic
  , easeOutCubic
  , easeInOutCubic
  , easeInElastic
  , easeOutElastic
  , easeInOutElastic
  , easeInBounce
  , easeOutBounce
  , easeSpring
  ) where

import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.GPU.Coordinates as Coord
import Hydrogen.Animation.Types as AnimTypes
import Hydrogen.GPU.DrawCommand.Types
  ( Point3D
  , ContourData
  , PathSegment
  , GlyphPathParams
  , GlyphInstanceParams
  , WordParams
  , PathDataParams
  , AnimationStateParams
  , AnimationTarget
  , AnimationUpdateMode(AnimationAdditive)
  , StaggerDirection
  , EasingFunction
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // glyph path parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create glyph path parameters with defaults.
glyphPathParams
  :: forall msg
   . Int                    -- glyphId
  -> Int                    -- fontId
  -> Array ContourData      -- contours
  -> Device.Pixel           -- advanceWidth
  -> GlyphPathParams msg
glyphPathParams gId fId contours advance =
  { glyphId: gId
  , fontId: fId
  , contours
  , bounds: defaultBounds
  , advanceWidth: advance
  , depth: Coord.depthValueNear
  , pickId: Nothing
  , onClick: Nothing
  }
  where
    defaultBounds =
      { minX: Device.px 0.0, minY: Device.px 0.0, minZ: Device.px 0.0
      , maxX: Device.px 0.0, maxY: Device.px 0.0, maxZ: Device.px 0.0
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // glyph instance parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create glyph instance parameters with defaults.
glyphInstanceParams
  :: forall msg
   . Int          -- pathDataId
  -> Point3D      -- position
  -> RGB.RGBA     -- color
  -> GlyphInstanceParams msg
glyphInstanceParams pathId pos color =
  { pathDataId: pathId
  , position: pos
  , rotation: { x: 0.0, y: 0.0, z: 0.0 }
  , scale: { x: 1.0, y: 1.0, z: 1.0 }
  , color
  , animationPhase: Coord.normalizedX 0.0
  , spring: { velocity: 0.0, displacement: 0.0, tension: 0.5, damping: 0.3, mass: 1.0 }
  , depth: Coord.depthValueNear
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // word parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create word parameters with defaults.
wordParams
  :: forall msg
   . Int                -- wordId
  -> Array Int          -- glyphInstances
  -> Array Point3D      -- positions
  -> Point3D            -- origin
  -> WordParams msg
wordParams wId glyphs positions origin =
  { wordId: wId
  , glyphInstances: glyphs
  , positions
  , origin
  , stagger: 
      { direction: staggerLeftToRight
      , delayMs: 50.0
      , easing: easeOutCubic
      }
  , color: RGB.rgba 255 255 255 255
  , depth: Coord.depthValueNear
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // path data parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create path data parameters.
pathDataParams
  :: Int                    -- pathDataId
  -> Array PathSegment      -- commands
  -> PathDataParams
pathDataParams pId commands =
  { pathDataId: pId
  , commands
  , bounds:
      { minX: Device.px 0.0, minY: Device.px 0.0, minZ: Device.px 0.0
      , maxX: Device.px 0.0, maxY: Device.px 0.0, maxZ: Device.px 0.0
      }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // animation state parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create animation state parameters with defaults.
animationStateParams
  :: Array AnimationTarget
  -> AnimationStateParams
animationStateParams targets =
  { targets
  , mode: AnimationAdditive
  , frameTime: 16.666  -- 60fps default
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // stagger direction ctors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Re-exported StaggerDirection constructors for backward compatibility.
staggerLeftToRight :: StaggerDirection
staggerLeftToRight = AnimTypes.StaggerLeftToRight

staggerRightToLeft :: StaggerDirection
staggerRightToLeft = AnimTypes.StaggerRightToLeft

staggerCenterOut :: StaggerDirection
staggerCenterOut = AnimTypes.StaggerCenterOut

staggerEdgesIn :: StaggerDirection
staggerEdgesIn = AnimTypes.StaggerEdgesIn

staggerTopToBottom :: StaggerDirection
staggerTopToBottom = AnimTypes.StaggerTopToBottom

staggerBottomToTop :: StaggerDirection
staggerBottomToTop = AnimTypes.StaggerBottomToTop

staggerRandom :: Int -> StaggerDirection
staggerRandom = AnimTypes.StaggerRandom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // easing function ctors
-- ═════════════════════════════════════════════════════════════════════════════

-- | New-style easing function names (EasingId prefix).
easingIdLinear :: EasingFunction
easingIdLinear = AnimTypes.EasingIdLinear

easingIdInQuad :: EasingFunction
easingIdInQuad = AnimTypes.EasingIdInQuad

easingIdOutQuad :: EasingFunction
easingIdOutQuad = AnimTypes.EasingIdOutQuad

easingIdInOutQuad :: EasingFunction
easingIdInOutQuad = AnimTypes.EasingIdInOutQuad

easingIdInCubic :: EasingFunction
easingIdInCubic = AnimTypes.EasingIdInCubic

easingIdOutCubic :: EasingFunction
easingIdOutCubic = AnimTypes.EasingIdOutCubic

easingIdInOutCubic :: EasingFunction
easingIdInOutCubic = AnimTypes.EasingIdInOutCubic

easingIdInElastic :: EasingFunction
easingIdInElastic = AnimTypes.EasingIdInElastic

easingIdOutElastic :: EasingFunction
easingIdOutElastic = AnimTypes.EasingIdOutElastic

easingIdInOutElastic :: EasingFunction
easingIdInOutElastic = AnimTypes.EasingIdInOutElastic

easingIdInBounce :: EasingFunction
easingIdInBounce = AnimTypes.EasingIdInBounce

easingIdOutBounce :: EasingFunction
easingIdOutBounce = AnimTypes.EasingIdOutBounce

easingIdSpring :: EasingFunction
easingIdSpring = AnimTypes.EasingIdSpring

-- ═════════════════════════════════════════════════════════════════════════════
--                                         // backward-compatible easing aliases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Backward compatible aliases (old Ease* names).
easeLinear :: EasingFunction
easeLinear = easingIdLinear

easeInQuad :: EasingFunction
easeInQuad = easingIdInQuad

easeOutQuad :: EasingFunction
easeOutQuad = easingIdOutQuad

easeInOutQuad :: EasingFunction
easeInOutQuad = easingIdInOutQuad

easeInCubic :: EasingFunction
easeInCubic = easingIdInCubic

easeOutCubic :: EasingFunction
easeOutCubic = easingIdOutCubic

easeInOutCubic :: EasingFunction
easeInOutCubic = easingIdInOutCubic

easeInElastic :: EasingFunction
easeInElastic = easingIdInElastic

easeOutElastic :: EasingFunction
easeOutElastic = easingIdOutElastic

easeInOutElastic :: EasingFunction
easeInOutElastic = easingIdInOutElastic

easeInBounce :: EasingFunction
easeInBounce = easingIdInBounce

easeOutBounce :: EasingFunction
easeOutBounce = easingIdOutBounce

easeSpring :: EasingFunction
easeSpring = easingIdSpring
