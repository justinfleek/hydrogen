-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // tour // motion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Motion System — The most fluid animations ever designed for a tour.
-- |
-- | ## Architecture
-- |
-- | This module provides the complete animation vocabulary for product tours:
-- |
-- | 1. **Spotlight Morphing** — Shape interpolation between targets
-- | 2. **Tooltip Choreography** — Entrance/exit/follow behaviors
-- | 3. **Progress Animations** — Alive, anticipating progress indicators
-- | 4. **Attention Grabbers** — Non-intrusive attention patterns
-- | 5. **Responsive Motion** — Accessibility and performance scaling
-- | 6. **Spring Physics** — Physics-based animation configurations
-- |
-- | ## Schema Mapping
-- |
-- | | Type                 | Pillar    | Purpose                                |
-- | |----------------------|-----------|----------------------------------------|
-- | | MorphConfig          | Temporal  | Shape interpolation parameters         |
-- | | MorphPath            | Geometry  | Path animation for non-adjacent targets|
-- | | TooltipChoreography  | Temporal  | Entry/exit/follow coordination         |
-- | | ProgressStyle        | Temporal  | Progress indicator animation style     |
-- | | AttentionPattern     | Temporal  | Non-intrusive attention effects        |
-- | | SpringPreset         | Temporal  | Physics-based spring configurations    |
-- | | MotionScale          | Temporal  | Performance/accessibility scaling      |
-- |
-- | ## Design Philosophy
-- |
-- | Every animation serves the user's understanding. Motion should:
-- | - Guide attention without distraction
-- | - Provide spatial continuity between steps
-- | - Feel organic and responsive to input
-- | - Respect user preferences and device capabilities
-- |
-- | The animations here are designed for Frame.io-level fluidity.

module Hydrogen.Element.Component.Tour.Motion
  ( -- * Spotlight Morphing
    MorphConfig
  , defaultMorphConfig
  , snappyMorphConfig
  , elasticMorphConfig
  , MorphPath(..)
  , MorphInterpolation(..)
  , ShapeInterpolation
  , interpolateRect
  , interpolateCircle
  , interpolatePill
  , computeMorphPath
  
    -- * Tooltip Choreography
  , TooltipChoreography
  , MicroInteractionConfig
  , ChoreographyPhase(..)
  , defaultChoreography
  , minimalChoreography
  , dramaticChoreography
  , defaultMicroInteractions
  , computeEntryAnimation
  , computeExitAnimation
  , computeFollowBehavior
  
    -- * Progress Animations
  , ProgressAnimationStyle(..)
  , DotProgressConfig
  , BarProgressConfig
  , BarFillStyle(FillLinear, FillLiquid, FillElastic, FillGradient)
  , CircularProgressConfig
  , FlipCounterConfig
  , defaultDotProgress
  , liquidBarProgress
  , strokeCircularProgress
  , flipCounterConfig
  
    -- * Attention Grabbers
  , AttentionPattern(..)
  , PulseConfig
  , BeaconConfig
  , MagneticConfig
  , CelebrationConfig
  , gentlePulse
  , subtleBeacon
  , magneticPull
  , celebrationBurst
  
    -- * Responsive Motion
  , MotionScale(..)
  , ReducedMotionFallback
  , PerformanceTier(..)
  , computeMotionScale
  , reducedMotionFallbacks
  , performanceAdaptations
  
    -- * Spring Physics
  , SpringPreset(..)
  , SpringParams
  , snappySpring
  , bouncySpring
  , smoothSpring
  , preciseSpring
  , criticallyDamped
  , springToCss
  , springDuration
  
    -- * Timing Curves (CSS-ready)
  , TimingCurve
  , organicEase
  , morphEase
  , tooltipEntryEase
  , tooltipExitEase
  , progressEase
  , attentionEase
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Bounded
  , class Eq
  , class Ord
  , class Show
  , max
  , min
  , negate
  , show
  , (&&)
  , (||)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<>)
  , (<=)
  , (>)
  , (>=)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Element.Component.Tour.Types 
  ( Placement
  , Side(SideTop, SideRight, SideBottom, SideLeft)
  , placementToSide
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // spotlight morphing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Configuration for spotlight morph transitions between targets.
-- |
-- | When transitioning from step N to step N+1, the highlight doesn't just
-- | appear/disappear — it MORPHS from one shape/position to another.
type MorphConfig =
  { duration :: Number
    -- ^ Morph duration in milliseconds (default: 400ms)
  , spring :: SpringParams
    -- ^ Spring physics for organic movement
  , interpolation :: MorphInterpolation
    -- ^ How shapes blend during transition
  , pathCurve :: Number
    -- ^ Bezier control point offset (0.0 = direct, 1.0 = extreme arc)
  , scaleAtMidpoint :: Number
    -- ^ Scale multiplier at transition midpoint (1.05 = subtle pop)
  , rotateAtMidpoint :: Number
    -- ^ Rotation at midpoint in degrees (subtle tilt adds life)
  , opacityDip :: Number
    -- ^ Opacity dip at midpoint (0.0 = none, 0.2 = subtle fade)
  }

-- | Default morph configuration — balanced and professional
defaultMorphConfig :: MorphConfig
defaultMorphConfig =
  { duration: 400.0
  , spring: smoothSpring
  , interpolation: InterpolateSmooth
  , pathCurve: 0.15
  , scaleAtMidpoint: 1.02
  , rotateAtMidpoint: 0.0
  , opacityDip: 0.0
  }

-- | Snappy morph — quick and precise for power users
snappyMorphConfig :: MorphConfig
snappyMorphConfig =
  { duration: 250.0
  , spring: snappySpring
  , interpolation: InterpolateDirect
  , pathCurve: 0.0
  , scaleAtMidpoint: 1.0
  , rotateAtMidpoint: 0.0
  , opacityDip: 0.0
  }

-- | Elastic morph — playful with overshoot
elasticMorphConfig :: MorphConfig
elasticMorphConfig =
  { duration: 500.0
  , spring: bouncySpring
  , interpolation: InterpolateSmooth
  , pathCurve: 0.25
  , scaleAtMidpoint: 1.08
  , rotateAtMidpoint: 2.0
  , opacityDip: 0.05
  }

-- | How shapes interpolate during morphing
data MorphInterpolation
  = InterpolateDirect      -- ^ Linear interpolation of bounds
  | InterpolateSmooth      -- ^ Smooth bezier-curved bounds interpolation
  | InterpolateSuperellipse -- ^ Superellipse blend for organic shapes
  | InterpolateCorners     -- ^ Interpolate each corner independently

derive instance eqMorphInterpolation :: Eq MorphInterpolation
derive instance ordMorphInterpolation :: Ord MorphInterpolation

instance showMorphInterpolation :: Show MorphInterpolation where
  show InterpolateDirect = "direct"
  show InterpolateSmooth = "smooth"
  show InterpolateSuperellipse = "superellipse"
  show InterpolateCorners = "corners"

-- | Path animation strategy for non-adjacent elements
data MorphPath
  = PathDirect
    -- ^ Straight line between targets (default)
  | PathArc Number
    -- ^ Curved arc path (parameter = curvature, 0.0-1.0)
  | PathBezier
      { cx1 :: Number, cy1 :: Number }
      { cx2 :: Number, cy2 :: Number }
    -- ^ Custom bezier control points (normalized 0-1)
  | PathAvoid (Array { x :: Number, y :: Number, radius :: Number })
    -- ^ Path that avoids obstacles
  | PathFollow String
    -- ^ Follow a named SVG path

derive instance eqMorphPath :: Eq MorphPath

instance showMorphPath :: Show MorphPath where
  show PathDirect = "direct"
  show (PathArc c) = "arc(" <> show c <> ")"
  show (PathBezier _ _) = "bezier(...)"
  show (PathAvoid _) = "avoid(...)"
  show (PathFollow id) = "follow(" <> id <> ")"

-- | Shape interpolation result at time t
type ShapeInterpolation =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  , borderRadius :: Number
  , scale :: Number
  , rotation :: Number
  , opacity :: Number
  }

-- | Interpolate between two rectangles at time t (0-1)
interpolateRect 
  :: { x :: Number, y :: Number, width :: Number, height :: Number, borderRadius :: Number }
  -> { x :: Number, y :: Number, width :: Number, height :: Number, borderRadius :: Number }
  -> MorphConfig
  -> Number
  -> ShapeInterpolation
interpolateRect from to config t =
  let
    -- Apply easing to time
    easedT = evaluateSpring config.spring t
    
    -- Interpolate position with optional arc path
    pathOffset = computePathOffset config.pathCurve t
    
    -- Midpoint scale/rotation effects
    midpointEffect = computeMidpointEffect t
    scaleMult = 1.0 + (config.scaleAtMidpoint - 1.0) * midpointEffect
    rotationAdd = config.rotateAtMidpoint * midpointEffect
    opacityMult = 1.0 - config.opacityDip * midpointEffect
  in
    { x: lerp from.x to.x easedT + pathOffset.x
    , y: lerp from.y to.y easedT + pathOffset.y
    , width: lerp from.width to.width easedT
    , height: lerp from.height to.height easedT
    , borderRadius: lerp from.borderRadius to.borderRadius easedT
    , scale: scaleMult
    , rotation: rotationAdd
    , opacity: opacityMult
    }

-- | Interpolate circles (uses max dimension as diameter)
interpolateCircle
  :: { cx :: Number, cy :: Number, r :: Number }
  -> { cx :: Number, cy :: Number, r :: Number }
  -> MorphConfig
  -> Number
  -> ShapeInterpolation
interpolateCircle from to config t =
  let
    easedT = evaluateSpring config.spring t
    midpointEffect = computeMidpointEffect t
    scaleMult = 1.0 + (config.scaleAtMidpoint - 1.0) * midpointEffect
    r = lerp from.r to.r easedT
  in
    { x: lerp from.cx to.cx easedT - r
    , y: lerp from.cy to.cy easedT - r
    , width: r * 2.0
    , height: r * 2.0
    , borderRadius: r
    , scale: scaleMult
    , rotation: config.rotateAtMidpoint * midpointEffect
    , opacity: 1.0 - config.opacityDip * midpointEffect
    }

-- | Interpolate pill shapes
-- |
-- | Pills have fully rounded ends, so borderRadius = min(width, height) / 2
interpolatePill
  :: { x :: Number, y :: Number, width :: Number, height :: Number }
  -> { x :: Number, y :: Number, width :: Number, height :: Number }
  -> MorphConfig
  -> Number
  -> ShapeInterpolation
interpolatePill from to config t =
  let
    -- Convert pill bounds to rect with appropriate radius
    fromWithRadius = 
      { x: from.x
      , y: from.y
      , width: from.width
      , height: from.height
      , borderRadius: min from.width from.height / 2.0
      }
    toWithRadius = 
      { x: to.x
      , y: to.y
      , width: to.width
      , height: to.height
      , borderRadius: min to.width to.height / 2.0
      }
    result = interpolateRect fromWithRadius toWithRadius config t
    -- Pill always has fully rounded ends based on interpolated dimensions
    finalRadius = min result.width result.height / 2.0
  in
    result { borderRadius = finalRadius }

-- | Compute optimal path between two targets
-- |
-- | Returns `PathDirect` for short distances, `PathArc` for longer ones.
-- | The arc direction is chosen based on the predominant movement direction.
computeMorphPath
  :: { x :: Number, y :: Number }
  -> { x :: Number, y :: Number }
  -> Number                          -- ^ Distance threshold for arcing
  -> MorphPath
computeMorphPath from to threshold =
  let
    dx = to.x - from.x
    dy = to.y - from.y
    distance = Math.sqrt (dx * dx + dy * dy)
    
    -- Bias factors determine arc direction
    -- Vertical movement (|dy| > |dx|) uses horizontal arc offset
    -- Horizontal movement (|dx| > |dy|) uses vertical arc offset
    verticalBias = Math.abs dy / (Math.abs dx + 0.001)
    horizontalBias = Math.abs dx / (Math.abs dy + 0.001)
    
    -- Base curvature on distance
    baseCurvature = if distance > threshold
      then min 0.3 (distance / (threshold * 3.0))
      else 0.0
    
    -- Adjust curvature based on movement bias
    -- More curvature when movement is strongly directional
    biasMultiplier = if verticalBias > 2.0 || horizontalBias > 2.0
      then 1.2
      else 1.0
    
    curvature = baseCurvature * biasMultiplier
  in
    if curvature > 0.05
      then PathArc curvature
      else PathDirect

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // tooltip choreography
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete choreography configuration for tooltip animations.
-- |
-- | Tooltips don't just "appear" — they're choreographed to create
-- | spatial continuity and guide the user's attention.
type TooltipChoreography =
  { entryDuration :: Number
    -- ^ Entry animation duration (ms)
  , exitDuration :: Number
    -- ^ Exit animation duration (ms)
  , entryDelay :: Number
    -- ^ Delay before entry starts (ms) — allows spotlight to settle
  , entrySpring :: SpringParams
    -- ^ Spring for entry animation
  , exitSpring :: SpringParams
    -- ^ Spring for exit animation
  , entryDistance :: Number
    -- ^ Starting offset distance (px)
  , scaleFrom :: Number
    -- ^ Initial scale (1.0 = no scale, 0.8 = scale up from 80%)
  , opacityDuration :: Number
    -- ^ Fade duration, independent of transform (ms)
  , arrowAnimates :: Boolean
    -- ^ Whether arrow animates separately
  , arrowDelay :: Number
    -- ^ Arrow animation delay after body (ms)
  , followScroll :: Boolean
    -- ^ Whether tooltip follows target during scroll
  , followSpring :: SpringParams
    -- ^ Spring for scroll-following
  , microInteractions :: MicroInteractionConfig
    -- ^ Button hover states, etc.
  }

-- | Micro-interaction configuration
type MicroInteractionConfig =
  { buttonHoverScale :: Number
    -- ^ Button scale on hover (1.02 = subtle)
  , buttonActiveScale :: Number
    -- ^ Button scale when pressed (0.98 = subtle press)
  , buttonTransition :: Number
    -- ^ Button transition duration (ms)
  , focusRingSpread :: Number
    -- ^ Focus ring spread animation (px)
  , focusRingDuration :: Number
    -- ^ Focus ring animation duration (ms)
  }

-- | Animation phase for choreography
data ChoreographyPhase
  = PhaseIdle           -- ^ Not animating
  | PhaseEntering       -- ^ Entry animation in progress
  | PhaseVisible        -- ^ Fully visible, awaiting interaction
  | PhaseExiting        -- ^ Exit animation in progress
  | PhaseFollowing      -- ^ Following scroll/resize

derive instance eqChoreographyPhase :: Eq ChoreographyPhase

instance showChoreographyPhase :: Show ChoreographyPhase where
  show PhaseIdle = "idle"
  show PhaseEntering = "entering"
  show PhaseVisible = "visible"
  show PhaseExiting = "exiting"
  show PhaseFollowing = "following"

-- | Default choreography — balanced and professional
defaultChoreography :: TooltipChoreography
defaultChoreography =
  { entryDuration: 350.0
  , exitDuration: 250.0
  , entryDelay: 100.0
  , entrySpring: smoothSpring
  , exitSpring: snappySpring
  , entryDistance: 16.0
  , scaleFrom: 0.95
  , opacityDuration: 200.0
  , arrowAnimates: true
  , arrowDelay: 50.0
  , followScroll: true
  , followSpring: preciseSpring
  , microInteractions: defaultMicroInteractions
  }

-- | Minimal choreography — for reduced motion or fast tours
minimalChoreography :: TooltipChoreography
minimalChoreography =
  { entryDuration: 150.0
  , exitDuration: 100.0
  , entryDelay: 0.0
  , entrySpring: criticallyDamped
  , exitSpring: criticallyDamped
  , entryDistance: 0.0
  , scaleFrom: 1.0
  , opacityDuration: 150.0
  , arrowAnimates: false
  , arrowDelay: 0.0
  , followScroll: true
  , followSpring: preciseSpring
  , microInteractions: minimalMicroInteractions
  }

-- | Dramatic choreography — for first-time onboarding
dramaticChoreography :: TooltipChoreography
dramaticChoreography =
  { entryDuration: 500.0
  , exitDuration: 350.0
  , entryDelay: 200.0
  , entrySpring: bouncySpring
  , exitSpring: smoothSpring
  , entryDistance: 24.0
  , scaleFrom: 0.85
  , opacityDuration: 300.0
  , arrowAnimates: true
  , arrowDelay: 100.0
  , followScroll: true
  , followSpring: smoothSpring
  , microInteractions: dramaticMicroInteractions
  }

-- | Default micro-interactions
defaultMicroInteractions :: MicroInteractionConfig
defaultMicroInteractions =
  { buttonHoverScale: 1.02
  , buttonActiveScale: 0.98
  , buttonTransition: 150.0
  , focusRingSpread: 3.0
  , focusRingDuration: 200.0
  }

-- | Minimal micro-interactions
minimalMicroInteractions :: MicroInteractionConfig
minimalMicroInteractions =
  { buttonHoverScale: 1.0
  , buttonActiveScale: 1.0
  , buttonTransition: 0.0
  , focusRingSpread: 2.0
  , focusRingDuration: 0.0
  }

-- | Dramatic micro-interactions
dramaticMicroInteractions :: MicroInteractionConfig
dramaticMicroInteractions =
  { buttonHoverScale: 1.05
  , buttonActiveScale: 0.95
  , buttonTransition: 200.0
  , focusRingSpread: 4.0
  , focusRingDuration: 300.0
  }

-- | Compute entry animation properties based on placement
computeEntryAnimation
  :: Placement
  -> TooltipChoreography
  -> { translateX :: Number, translateY :: Number, scale :: Number, opacity :: Number }
computeEntryAnimation placement choreo =
  let
    distance = choreo.entryDistance
    
    -- Direction based on placement side
    translate = case extractSide placement of
      SideTop -> { x: 0.0, y: distance }        -- Slides down from above
      SideBottom -> { x: 0.0, y: negate distance } -- Slides up from below
      SideLeft -> { x: distance, y: 0.0 }       -- Slides right from left
      SideRight -> { x: negate distance, y: 0.0 }  -- Slides left from right
  in
    { translateX: translate.x
    , translateY: translate.y
    , scale: choreo.scaleFrom
    , opacity: 0.0
    }

-- | Compute exit animation based on next step's direction
computeExitAnimation
  :: Placement                           -- ^ Current tooltip placement
  -> Maybe { x :: Number, y :: Number }  -- ^ Next target position (Nothing = tour ending)
  -> TooltipChoreography
  -> { translateX :: Number, translateY :: Number, scale :: Number, opacity :: Number }
computeExitAnimation currentPlacement nextTarget choreo =
  case nextTarget of
    -- Exit toward next target
    Just target ->
      let
        -- Exit in direction of next target
        dirX = if target.x > 0.0 then negate 8.0 else 8.0
        dirY = if target.y > 0.0 then negate 8.0 else 8.0
      in
        { translateX: dirX
        , translateY: dirY
        , scale: 0.98
        , opacity: 0.0
        }
    -- Tour ending — exit based on placement
    Nothing ->
      let
        distance = choreo.entryDistance * 0.5
        translate = case extractSide currentPlacement of
          SideTop -> { x: 0.0, y: negate distance }
          SideBottom -> { x: 0.0, y: distance }
          SideLeft -> { x: negate distance, y: 0.0 }
          SideRight -> { x: distance, y: 0.0 }
      in
        { translateX: translate.x
        , translateY: translate.y
        , scale: 0.95
        , opacity: 0.0
        }

-- | Compute follow behavior during scroll
-- |
-- | Returns the target position and an optimized CSS transition string.
-- | The transition is dampened based on the distance moved to prevent
-- | overly bouncy behavior during rapid scroll events.
computeFollowBehavior
  :: { targetX :: Number, targetY :: Number }
  -> { currentX :: Number, currentY :: Number }
  -> TooltipChoreography
  -> { x :: Number, y :: Number, transition :: String }
computeFollowBehavior target current choreo =
  let
    spring = choreo.followSpring
    
    -- Calculate distance for adaptive dampening
    dx = target.targetX - current.currentX
    dy = target.targetY - current.currentY
    distance = Math.sqrt (dx * dx + dy * dy)
    
    -- For large movements, use faster transition to prevent lag
    -- For small adjustments, use normal spring for smoothness
    adaptedDuration = if distance > 100.0
      then springDuration spring * 0.6
      else springDuration spring
    
    easing = springToCss spring
  in
    { x: target.targetX
    , y: target.targetY
    , transition: "transform " <> show adaptedDuration <> "ms " <> easing
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // progress animations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Style of progress animation
data ProgressAnimationStyle
  = ProgressDots DotProgressConfig
    -- ^ Dot-based progress with anticipation effects
  | ProgressBar BarProgressConfig
    -- ^ Linear bar with liquid/elastic fill
  | ProgressCircular CircularProgressConfig
    -- ^ Circular progress with stroke animation
  | ProgressFlipCounter FlipCounterConfig
    -- ^ Flip-clock style numeric counter
  | ProgressNone
    -- ^ No visible progress

derive instance eqProgressAnimationStyle :: Eq ProgressAnimationStyle

instance showProgressAnimationStyle :: Show ProgressAnimationStyle where
  show (ProgressDots _) = "dots"
  show (ProgressBar _) = "bar"
  show (ProgressCircular _) = "circular"
  show (ProgressFlipCounter _) = "flip-counter"
  show ProgressNone = "none"

-- | Dot progress configuration
-- |
-- | Features anticipation: next dot glows slightly before becoming active.
type DotProgressConfig =
  { dotSize :: Number
    -- ^ Dot diameter (px)
  , dotSpacing :: Number
    -- ^ Space between dots (px)
  , activeScale :: Number
    -- ^ Scale of active dot (1.2 = 20% larger)
  , anticipationGlow :: Number
    -- ^ Glow intensity on "next" dot (0-1)
  , anticipationScale :: Number
    -- ^ Scale of "next" dot (1.05 = subtle growth)
  , transitionDuration :: Number
    -- ^ Dot transition duration (ms)
  , spring :: SpringParams
    -- ^ Spring for dot animations
  , completedOpacity :: Number
    -- ^ Opacity of completed dots (0.5 = dimmed)
  , pulseActive :: Boolean
    -- ^ Whether active dot pulses
  , pulseDuration :: Number
    -- ^ Pulse animation duration (ms)
  }

-- | Default dot progress with anticipation
defaultDotProgress :: DotProgressConfig
defaultDotProgress =
  { dotSize: 8.0
  , dotSpacing: 12.0
  , activeScale: 1.25
  , anticipationGlow: 0.3
  , anticipationScale: 1.08
  , transitionDuration: 300.0
  , spring: smoothSpring
  , completedOpacity: 0.6
  , pulseActive: true
  , pulseDuration: 2000.0
  }

-- | Bar progress configuration with liquid fill effect
type BarProgressConfig =
  { height :: Number
    -- ^ Bar height (px)
  , borderRadius :: Number
    -- ^ Bar corner radius (px)
  , fillStyle :: BarFillStyle
    -- ^ How the fill animates
  , overshoot :: Number
    -- ^ Elastic overshoot amount (0-1)
  , transitionDuration :: Number
    -- ^ Fill transition duration (ms)
  , spring :: SpringParams
    -- ^ Spring for fill animation
  , showPercentage :: Boolean
    -- ^ Show percentage text
  , glowOnProgress :: Boolean
    -- ^ Glow effect at fill edge
  }

-- | How bar fill animates
data BarFillStyle
  = FillLinear          -- ^ Simple linear fill
  | FillLiquid          -- ^ Liquid wave effect at edge
  | FillElastic         -- ^ Elastic bounce at stops
  | FillGradient        -- ^ Animated gradient fill

derive instance eqBarFillStyle :: Eq BarFillStyle

instance showBarFillStyle :: Show BarFillStyle where
  show FillLinear = "linear"
  show FillLiquid = "liquid"
  show FillElastic = "elastic"
  show FillGradient = "gradient"

-- | Liquid bar progress preset
liquidBarProgress :: BarProgressConfig
liquidBarProgress =
  { height: 4.0
  , borderRadius: 2.0
  , fillStyle: FillLiquid
  , overshoot: 0.05
  , transitionDuration: 400.0
  , spring: bouncySpring
  , showPercentage: false
  , glowOnProgress: true
  }

-- | Circular progress configuration
type CircularProgressConfig =
  { radius :: Number
    -- ^ Circle radius (px)
  , strokeWidth :: Number
    -- ^ Stroke width (px)
  , strokeLinecap :: String
    -- ^ "round" or "butt"
  , rotateStart :: Number
    -- ^ Starting rotation (degrees, -90 = top)
  , direction :: String
    -- ^ "clockwise" or "counterclockwise"
  , transitionDuration :: Number
    -- ^ Stroke transition duration (ms)
  , spring :: SpringParams
    -- ^ Spring for stroke animation
  , showCenter :: Boolean
    -- ^ Show content in center
  , glowOnProgress :: Boolean
    -- ^ Glow at stroke end
  }

-- | Stroke circular progress preset
strokeCircularProgress :: CircularProgressConfig
strokeCircularProgress =
  { radius: 20.0
  , strokeWidth: 3.0
  , strokeLinecap: "round"
  , rotateStart: -90.0
  , direction: "clockwise"
  , transitionDuration: 400.0
  , spring: smoothSpring
  , showCenter: true
  , glowOnProgress: true
  }

-- | Flip counter configuration (like airport departure boards)
type FlipCounterConfig =
  { digitHeight :: Number
    -- ^ Height of each digit (px)
  , flipDuration :: Number
    -- ^ Single flip duration (ms)
  , staggerDelay :: Number
    -- ^ Delay between digit flips (ms)
  , perspective :: Number
    -- ^ 3D perspective (px)
  , showDivider :: Boolean
    -- ^ Show " / " divider (e.g., "3 / 5")
  }

-- | Default flip counter
flipCounterConfig :: FlipCounterConfig
flipCounterConfig =
  { digitHeight: 32.0
  , flipDuration: 400.0
  , staggerDelay: 50.0
  , perspective: 500.0
  , showDivider: true
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // attention grabbers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Non-intrusive attention patterns that don't feel like errors.
data AttentionPattern
  = AttentionPulse PulseConfig
    -- ^ Gentle pulsing that doesn't alarm
  | AttentionBeacon BeaconConfig
    -- ^ Subtle beacon animation
  | AttentionMagnetic MagneticConfig
    -- ^ "Magnetic" pull effect toward target
  | AttentionCelebration CelebrationConfig
    -- ^ Particle effects for completion
  | AttentionNone
    -- ^ No attention animation

derive instance eqAttentionPattern :: Eq AttentionPattern

instance showAttentionPattern :: Show AttentionPattern where
  show (AttentionPulse _) = "pulse"
  show (AttentionBeacon _) = "beacon"
  show (AttentionMagnetic _) = "magnetic"
  show (AttentionCelebration _) = "celebration"
  show AttentionNone = "none"

-- | Pulse configuration that doesn't feel like an error
-- |
-- | Key insight: error pulses are red and fast. Friendly pulses are
-- | branded colors, slow, and subtle.
type PulseConfig =
  { scaleMin :: Number
    -- ^ Minimum scale (1.0 = no shrink)
  , scaleMax :: Number
    -- ^ Maximum scale (1.03 = very subtle)
  , opacityMin :: Number
    -- ^ Minimum opacity (0.7 = subtle dim)
  , opacityMax :: Number
    -- ^ Maximum opacity (1.0)
  , duration :: Number
    -- ^ Full pulse cycle (ms) — slow = friendly
  , easing :: String
    -- ^ "ease-in-out" for breathing feel
  , iterations :: Number
    -- ^ Number of pulses (Infinity for continuous)
  , ringExpand :: Boolean
    -- ^ Expanding ring effect
  , ringMaxScale :: Number
    -- ^ Ring maximum scale
  , ringOpacityStart :: Number
    -- ^ Ring starting opacity
  }

-- | Gentle pulse that doesn't alarm
gentlePulse :: PulseConfig
gentlePulse =
  { scaleMin: 1.0
  , scaleMax: 1.02
  , opacityMin: 0.85
  , opacityMax: 1.0
  , duration: 3000.0        -- Very slow = calming
  , easing: "ease-in-out"
  , iterations: infinity
  , ringExpand: true
  , ringMaxScale: 1.5
  , ringOpacityStart: 0.4
  }

-- | Beacon configuration
type BeaconConfig =
  { color :: String
    -- ^ Beacon color (usually brand color)
  , size :: Number
    -- ^ Beacon size (px)
  , waves :: Int
    -- ^ Number of expanding waves
  , waveDuration :: Number
    -- ^ Single wave duration (ms)
  , waveDelay :: Number
    -- ^ Delay between waves (ms)
  , waveMaxScale :: Number
    -- ^ Maximum scale of waves
  , fadeDistance :: Number
    -- ^ Distance at which waves fully fade
  }

-- | Subtle beacon effect
subtleBeacon :: BeaconConfig
subtleBeacon =
  { color: "currentColor"
  , size: 12.0
  , waves: 2
  , waveDuration: 2000.0
  , waveDelay: 700.0
  , waveMaxScale: 2.5
  , fadeDistance: 40.0
  }

-- | Magnetic pull configuration
-- |
-- | Creates a subtle "pull" toward the target, making elements
-- | feel magnetically attracted.
type MagneticConfig =
  { strength :: Number
    -- ^ Pull strength (0-1)
  , radius :: Number
    -- ^ Effect radius (px)
  , smoothing :: Number
    -- ^ Movement smoothing (0-1)
  , affectsBackground :: Boolean
    -- ^ Whether background slightly warps
  , cursorInfluence :: Boolean
    -- ^ Whether cursor position influences
  }

-- | Subtle magnetic pull
magneticPull :: MagneticConfig
magneticPull =
  { strength: 0.15
  , radius: 100.0
  , smoothing: 0.8
  , affectsBackground: false
  , cursorInfluence: true
  }

-- | Celebration configuration for completion moments
type CelebrationConfig =
  { particleCount :: Int
    -- ^ Number of particles
  , particleColors :: Array String
    -- ^ Particle colors
  , spread :: Number
    -- ^ Spread angle (degrees)
  , velocity :: Number
    -- ^ Initial velocity
  , gravity :: Number
    -- ^ Gravity effect
  , duration :: Number
    -- ^ Animation duration (ms)
  , confetti :: Boolean
    -- ^ Confetti style vs sparkles
  , sound :: Maybe String
    -- ^ Optional sound effect path
  }

-- | Celebration burst for tour completion
celebrationBurst :: CelebrationConfig
celebrationBurst =
  { particleCount: 30
  , particleColors: ["#FFD700", "#FFA500", "#FF69B4", "#00CED1", "#7B68EE"]
  , spread: 60.0
  , velocity: 400.0
  , gravity: 800.0
  , duration: 2000.0
  , confetti: true
  , sound: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // responsive motion
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Motion scale for accessibility and performance
data MotionScale
  = MotionFull           -- ^ Full animations
  | MotionReduced        -- ^ Reduced motion (prefers-reduced-motion)
  | MotionMinimal        -- ^ Minimal motion (very low performance)
  | MotionNone           -- ^ No motion at all

derive instance eqMotionScale :: Eq MotionScale
derive instance ordMotionScale :: Ord MotionScale

instance showMotionScale :: Show MotionScale where
  show MotionFull = "full"
  show MotionReduced = "reduced"
  show MotionMinimal = "minimal"
  show MotionNone = "none"

instance boundedMotionScale :: Bounded MotionScale where
  bottom = MotionFull
  top = MotionNone

-- | Reduced motion fallback configuration
type ReducedMotionFallback =
  { morphToFade :: Boolean
    -- ^ Replace morph with crossfade
  , disableSpring :: Boolean
    -- ^ Use linear timing instead of springs
  , disablePulse :: Boolean
    -- ^ Disable all pulse animations
  , instantProgress :: Boolean
    -- ^ Progress jumps instantly
  , keepOpacity :: Boolean
    -- ^ Keep opacity animations (usually safe)
  , maxDuration :: Number
    -- ^ Maximum animation duration (ms)
  }

-- | Performance tier for adaptive animations
data PerformanceTier
  = TierHigh            -- ^ Full effects, blur, shadows
  | TierMedium          -- ^ Most effects, no blur
  | TierLow             -- ^ Basic animations only
  | TierMinimal         -- ^ Opacity changes only

derive instance eqPerformanceTier :: Eq PerformanceTier
derive instance ordPerformanceTier :: Ord PerformanceTier

instance showPerformanceTier :: Show PerformanceTier where
  show TierHigh = "high"
  show TierMedium = "medium"
  show TierLow = "low"
  show TierMinimal = "minimal"

-- | Compute motion scale from user preference and device
computeMotionScale
  :: { prefersReducedMotion :: Boolean, isLowPower :: Boolean, fps :: Number }
  -> MotionScale
computeMotionScale prefs
  | prefs.prefersReducedMotion = MotionReduced
  | prefs.isLowPower = MotionMinimal
  | prefs.fps < 30.0 = MotionMinimal
  | prefs.fps < 50.0 = MotionReduced
  | true = MotionFull

-- | Get reduced motion fallbacks
reducedMotionFallbacks :: ReducedMotionFallback
reducedMotionFallbacks =
  { morphToFade: true
  , disableSpring: true
  , disablePulse: true
  , instantProgress: true
  , keepOpacity: true
  , maxDuration: 200.0
  }

-- | Adapt animations based on performance tier
performanceAdaptations :: PerformanceTier -> MorphConfig -> MorphConfig
performanceAdaptations tier config = case tier of
  TierHigh -> config
  TierMedium -> config
    { scaleAtMidpoint = 1.0
    , rotateAtMidpoint = 0.0
    }
  TierLow -> config
    { duration = config.duration * 0.7
    , spring = criticallyDamped
    , pathCurve = 0.0
    , scaleAtMidpoint = 1.0
    , rotateAtMidpoint = 0.0
    , opacityDip = 0.0
    }
  TierMinimal -> config
    { duration = 0.0
    , interpolation = InterpolateDirect
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // spring physics
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spring physics presets for different use cases.
data SpringPreset
  = Snappy        -- ^ Quick, responsive UI feedback
  | Bouncy        -- ^ Playful with visible overshoot
  | Smooth        -- ^ Elegant, no overshoot
  | Precise       -- ^ Exact positioning, minimal settling
  | Critical      -- ^ Critically damped (fastest without overshoot)

derive instance eqSpringPreset :: Eq SpringPreset
derive instance ordSpringPreset :: Ord SpringPreset

instance showSpringPreset :: Show SpringPreset where
  show Snappy = "snappy"
  show Bouncy = "bouncy"
  show Smooth = "smooth"
  show Precise = "precise"
  show Critical = "critical"

-- | Spring parameters based on Framer Motion conventions
type SpringParams =
  { stiffness :: Number
    -- ^ Spring constant (N/m equivalent). Higher = faster.
    -- ^ Range: 50-500. Default: 100.
  , damping :: Number
    -- ^ Damping coefficient. Higher = less oscillation.
    -- ^ Range: 5-40. Default: 10.
  , mass :: Number
    -- ^ Mass of the object. Higher = more inertia.
    -- ^ Range: 0.5-3. Default: 1.
  }

-- | Snappy spring — responsive UI interactions
-- |
-- | Duration: ~200ms, slight overshoot for liveliness
-- | Use for: button responses, menu opens, toggles
snappySpring :: SpringParams
snappySpring =
  { stiffness: 400.0
  , damping: 30.0
  , mass: 1.0
  }

-- | Bouncy spring — playful, attention-grabbing
-- |
-- | Duration: ~400ms, visible bounce
-- | Use for: celebrations, confirmations, first-time reveals
bouncySpring :: SpringParams
bouncySpring =
  { stiffness: 300.0
  , damping: 10.0
  , mass: 1.0
  }

-- | Smooth spring — elegant transitions
-- |
-- | Duration: ~350ms, no overshoot
-- | Use for: modal opens, page transitions, tooltips
smoothSpring :: SpringParams
smoothSpring =
  { stiffness: 150.0
  , damping: 20.0
  , mass: 1.0
  }

-- | Precise spring — accurate positioning
-- |
-- | Duration: ~180ms, minimal settling
-- | Use for: scroll following, cursor tracking, snapping
preciseSpring :: SpringParams
preciseSpring =
  { stiffness: 500.0
  , damping: 40.0
  , mass: 0.8
  }

-- | Critically damped — fastest without overshoot
-- |
-- | Duration: ~120ms, no oscillation
-- | Use for: reduced motion mode, instant feedback
criticallyDamped :: SpringParams
criticallyDamped =
  { stiffness: 300.0
  , damping: 34.64      -- sqrt(4 * stiffness * mass)
  , mass: 1.0
  }

-- | Convert spring params to CSS cubic-bezier approximation
-- |
-- | Note: True spring physics cannot be represented in CSS.
-- | This provides a visual approximation.
springToCss :: SpringParams -> String
springToCss spring
  -- Snappy springs approximate to ease-out
  | spring.stiffness >= 350.0 && spring.damping >= 25.0 =
      "cubic-bezier(0.22, 1.0, 0.36, 1.0)"
  -- Bouncy springs have overshoot
  | spring.damping < 15.0 =
      "cubic-bezier(0.34, 1.56, 0.64, 1.0)"
  -- Smooth springs are ease-out-quad
  | spring.stiffness < 200.0 && spring.damping >= 15.0 =
      "cubic-bezier(0.25, 0.46, 0.45, 0.94)"
  -- Default fallback
  | true =
      "cubic-bezier(0.33, 1.0, 0.68, 1.0)"

-- | Estimate spring animation duration in milliseconds
-- |
-- | Based on when oscillation amplitude drops below threshold.
springDuration :: SpringParams -> Number
springDuration spring =
  let
    -- Damping ratio
    omega0 = Math.sqrt (spring.stiffness / spring.mass)
    zeta = spring.damping / (2.0 * Math.sqrt (spring.stiffness * spring.mass))
    
    -- Settling time (99% of final value)
    settlingTime = if zeta >= 1.0
      -- Critically damped or overdamped
      then 4.0 / (zeta * omega0)
      -- Underdamped
      else 4.0 / (zeta * omega0)
  in
    -- Convert to milliseconds, clamp to reasonable range
    min 1000.0 (max 100.0 (settlingTime * 1000.0))

-- | Evaluate spring at time t (0-1)
evaluateSpring :: SpringParams -> Number -> Number
evaluateSpring spring t
  | t <= 0.0 = 0.0
  | t >= 1.0 = 1.0
  | true =
      let
        omega0 = Math.sqrt (spring.stiffness / spring.mass)
        zeta = spring.damping / (2.0 * Math.sqrt (spring.stiffness * spring.mass))
        
        -- Underdamped case (typical for UI springs)
        omegaD = omega0 * Math.sqrt (1.0 - zeta * zeta)
        decay = Math.exp (negate zeta * omega0 * t)
      in
        if zeta < 1.0
          -- Underdamped: oscillates
          then 1.0 - decay * (Math.cos (omegaD * t) + (zeta * omega0 / omegaD) * Math.sin (omegaD * t))
          -- Critically damped or overdamped
          else 1.0 - decay * (1.0 + omega0 * t)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // timing curves
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS-ready timing curve
type TimingCurve =
  { name :: String
  , css :: String
  , description :: String
  }

-- | Organic ease — feels natural and intentional
-- |
-- | cubic-bezier(0.22, 1.0, 0.36, 1.0)
-- | Fast start, slow settle. Like setting something down gently.
organicEase :: TimingCurve
organicEase =
  { name: "organic"
  , css: "cubic-bezier(0.22, 1.0, 0.36, 1.0)"
  , description: "Natural deceleration, used for most UI elements"
  }

-- | Morph ease — maintains perceptual continuity
-- |
-- | cubic-bezier(0.65, 0.0, 0.35, 1.0)
-- | Smooth acceleration and deceleration for shape transitions.
morphEase :: TimingCurve
morphEase =
  { name: "morph"
  , css: "cubic-bezier(0.65, 0.0, 0.35, 1.0)"
  , description: "Symmetric ease for shape morphing"
  }

-- | Tooltip entry — arrives with confidence
-- |
-- | cubic-bezier(0.34, 1.56, 0.64, 1.0)
-- | Slight overshoot creates "arrival" feeling.
tooltipEntryEase :: TimingCurve
tooltipEntryEase =
  { name: "tooltip-entry"
  , css: "cubic-bezier(0.34, 1.56, 0.64, 1.0)"
  , description: "Bouncy entry with slight overshoot"
  }

-- | Tooltip exit — departs gracefully
-- |
-- | cubic-bezier(0.36, 0.0, 0.66, -0.56)
-- | Quick departure, slight anticipation.
tooltipExitEase :: TimingCurve
tooltipExitEase =
  { name: "tooltip-exit"
  , css: "cubic-bezier(0.36, 0.0, 0.66, -0.56)"
  , description: "Quick exit with anticipation"
  }

-- | Progress ease — builds anticipation
-- |
-- | cubic-bezier(0.4, 0.0, 0.2, 1.0)
-- | Steady acceleration, then smooth arrival at destination.
progressEase :: TimingCurve
progressEase =
  { name: "progress"
  , css: "cubic-bezier(0.4, 0.0, 0.2, 1.0)"
  , description: "Material Design standard easing"
  }

-- | Attention ease — gentle breathing
-- |
-- | ease-in-out (symmetric)
-- | For continuous attention animations.
attentionEase :: TimingCurve
attentionEase =
  { name: "attention"
  , css: "ease-in-out"
  , description: "Symmetric ease for continuous animations"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // helper functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Compute path offset for curved morph paths
computePathOffset :: Number -> Number -> { x :: Number, y :: Number }
computePathOffset curvature t =
  -- Sine curve perpendicular to path
  let
    perpendicular = Math.sin (t * Math.pi)
    offset = perpendicular * curvature * 50.0  -- 50px max offset
  in
    { x: offset, y: offset * 0.5 }

-- | Compute midpoint effect strength (bell curve centered at t=0.5)
computeMidpointEffect :: Number -> Number
computeMidpointEffect t =
  let
    -- Distance from midpoint (0 at center, 0.5 at edges)
    d = Math.abs (t - 0.5)
    -- Bell curve: strongest at t=0.5, fades toward edges
    -- Using cosine for smooth falloff
  in
    Math.cos (d * Math.pi) * 0.5 + 0.5

-- | Extract side from placement
-- |
-- | Delegates to Types.placementToSide for ADT-based Placement.
extractSide :: Placement -> Side
extractSide = placementToSide

-- | Infinity constant
infinity :: Number
infinity = 1.0 / 0.0
