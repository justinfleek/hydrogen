-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // gpu // framestate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FrameState — Per-Frame Animation and Interaction State
-- |
-- | ## Design Philosophy
-- |
-- | Hyper-responsive UIs like Frame.io and Ghostty achieve their fluidity by
-- | treating animation as **external state** that flows into effects, not
-- | internal state that effects manage themselves.
-- |
-- | FrameState captures everything a render pass needs to know about "now":
-- |
-- | - **Time**: Current timestamp, delta time, frame number
-- | - **Mouse**: Position, buttons, hover state
-- | - **Animations**: Active animation phases, spring states
-- | - **Viewport**: Size, DPI, orientation
-- | - **Performance**: FPS target, GPU budget remaining
-- |
-- | ## Why External State?
-- |
-- | At billion-agent scale, internal animation state creates chaos:
-- | - Each agent has its own timers → clock drift
-- | - Animation state scattered across components → hard to serialize
-- | - No global coordination → janky frame timing
-- |
-- | With external state:
-- | - One clock source → frame-perfect sync
-- | - All animation state in FrameState → serializable, replayable
-- | - Deterministic renders → same FrameState = same pixels
-- |
-- | ## Frame.io/Ghostty Responsiveness Model
-- |
-- | ```
-- | User Input → FrameState Update → Render Effects → GPU Output
-- |     ↑                                                ↓
-- |     └──────────────── 60/120fps loop ────────────────┘
-- | ```
-- |
-- | The key: FrameState updates are **immediate** (sub-millisecond).
-- | Render is a pure function of FrameState. No async, no promises, no delays.

module Hydrogen.GPU.FrameState
  ( -- * Core Types
    FrameState
  , FrameTime
  , FrameNumber
  
  -- * Time State
  , TimeState
  , mkTimeState
  , advanceTime
  , deltaMs
  , elapsedMs
  , frameNumber
  , fps
  
  -- * Mouse State
  , MouseState
  , MouseButton(..)
  , mkMouseState
  , mousePosition
  , mouseButtons
  , mouseHoverTarget
  , mouseDelta
  , mouseVelocity
  
  -- * Animation State
  , AnimationRegistry
  , AnimationInstance
  , AnimationHandle
  , EasingType(..)
  , AnimationDirection(..)
  , AnimationIteration(..)
  , AnimationPhase(..)
  , SpringInstance
  , mkAnimationRegistry
  , registerAnimation
  , unregisterAnimation
  , getAnimationPhase
  , getAllAnimations
  , tickAnimations
  
  -- * Spring State
  , SpringRegistry
  , SpringHandle
  , mkSpringRegistry
  , registerSpring
  , getSpringValue
  , setSpringTarget
  , tickSprings
  
  -- * Viewport State
  , ViewportState
  , ViewportOrientation(..)
  , mkViewportState
  , viewportWidth
  , viewportHeight
  , viewportDPI
  , viewportOrientation
  
  -- * Performance State
  , PerformanceState
  , mkPerformanceState
  , targetFPS
  , actualFPS
  , gpuBudgetMs
  , gpuUsedMs
  , frameDropped
  
  -- * FrameState Construction
  , mkFrameState
  , emptyFrameState
  
  -- * FrameState Updates
  , updateTime
  , updateMouse
  , updateViewport
  , updatePerformance
  , tick
  
  -- * FrameState Queries
  , isHovering
  , isPressed
  , animationProgress
  , springValue
  , springValueOr
  , getSpringValueMaybe
  , timeSinceStart
  , framesPerSecond
  , animationCount
  , clampedFPS
  , hasActiveAnimations
  , frameNumberAsNumber
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , not
  , (<>)
  , (==)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (&&)
  , ($)
  , min
  , max
  , negate
  )

import Data.Array (filter, snoc, length, find)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Tuple (Tuple(Tuple))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // core types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Time in milliseconds since epoch or start
type FrameTime = Number

-- | Frame counter (monotonically increasing)
type FrameNumber = Int

-- | Complete frame state for a render pass
type FrameState =
  { time :: TimeState
  , mouse :: MouseState
  , animations :: AnimationRegistry
  , springs :: SpringRegistry
  , viewport :: ViewportState
  , performance :: PerformanceState
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // time state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Temporal state for the current frame
type TimeState =
  { current :: FrameTime       -- Current timestamp (ms since start)
  , delta :: FrameTime         -- Time since last frame (ms)
  , frame :: FrameNumber       -- Frame counter
  , start :: FrameTime         -- Timestamp when app started
  , targetFPS :: Number        -- Target frames per second
  }

-- | Create initial time state
mkTimeState :: FrameTime -> Number -> TimeState
mkTimeState startTime targetFrameRate =
  { current: startTime
  , delta: 0.0
  , frame: 0
  , start: startTime
  , targetFPS: targetFrameRate
  }

-- | Advance time by delta milliseconds
advanceTime :: FrameTime -> TimeState -> TimeState
advanceTime newTime state =
  { current: newTime
  , delta: newTime - state.current
  , frame: state.frame + 1
  , start: state.start
  , targetFPS: state.targetFPS
  }

-- | Get delta time in milliseconds
deltaMs :: TimeState -> FrameTime
deltaMs state = state.delta

-- | Get elapsed time since start in milliseconds
elapsedMs :: TimeState -> FrameTime
elapsedMs state = state.current - state.start

-- | Get current frame number
frameNumber :: TimeState -> FrameNumber
frameNumber state = state.frame

-- | Calculate actual FPS from delta time
fps :: TimeState -> Number
fps state = if state.delta > 0.0 then 1000.0 / state.delta else 0.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // mouse state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Mouse button identifiers
data MouseButton
  = MouseLeft
  | MouseMiddle
  | MouseRight
  | MouseBack
  | MouseForward

derive instance eqMouseButton :: Eq MouseButton

instance showMouseButton :: Show MouseButton where
  show MouseLeft = "MouseLeft"
  show MouseMiddle = "MouseMiddle"
  show MouseRight = "MouseRight"
  show MouseBack = "MouseBack"
  show MouseForward = "MouseForward"

-- | Mouse interaction state
type MouseState =
  { x :: Number                -- X position in viewport pixels
  , y :: Number                -- Y position in viewport pixels
  , prevX :: Number            -- Previous X position
  , prevY :: Number            -- Previous Y position
  , velocityX :: Number        -- X velocity (pixels per frame)
  , velocityY :: Number        -- Y velocity (pixels per frame)
  , buttons :: Array MouseButton  -- Currently pressed buttons
  , hoverTarget :: Maybe Int   -- PickId of element under cursor
  , activeTarget :: Maybe Int  -- PickId of element being pressed
  , dragStartX :: Number       -- Drag start X (if dragging)
  , dragStartY :: Number       -- Drag start Y (if dragging)
  , isDragging :: Boolean      -- Is a drag in progress
  }

-- | Create initial mouse state
mkMouseState :: MouseState
mkMouseState =
  { x: 0.0
  , y: 0.0
  , prevX: 0.0
  , prevY: 0.0
  , velocityX: 0.0
  , velocityY: 0.0
  , buttons: []
  , hoverTarget: Nothing
  , activeTarget: Nothing
  , dragStartX: 0.0
  , dragStartY: 0.0
  , isDragging: false
  }

-- | Get mouse position
mousePosition :: MouseState -> { x :: Number, y :: Number }
mousePosition state = { x: state.x, y: state.y }

-- | Get pressed buttons
mouseButtons :: MouseState -> Array MouseButton
mouseButtons state = state.buttons

-- | Get hover target PickId
mouseHoverTarget :: MouseState -> Maybe Int
mouseHoverTarget state = state.hoverTarget

-- | Get mouse movement since last frame
mouseDelta :: MouseState -> { dx :: Number, dy :: Number }
mouseDelta state = { dx: state.x - state.prevX, dy: state.y - state.prevY }

-- | Get mouse velocity
mouseVelocity :: MouseState -> { vx :: Number, vy :: Number }
mouseVelocity state = { vx: state.velocityX, vy: state.velocityY }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // animation state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique handle for registered animation
type AnimationHandle = Int

-- | Animation phase for effect interpolation
data AnimationPhase
  = AnimationIdle            -- Not started
  | AnimationRunning Number  -- Progress 0.0-1.0
  | AnimationComplete        -- Finished (at 1.0)
  | AnimationReversing Number -- Playing backward

derive instance eqAnimationPhase :: Eq AnimationPhase

instance showAnimationPhase :: Show AnimationPhase where
  show AnimationIdle = "AnimationIdle"
  show (AnimationRunning p) = "(AnimationRunning " <> show p <> ")"
  show AnimationComplete = "AnimationComplete"
  show (AnimationReversing p) = "(AnimationReversing " <> show p <> ")"

-- | Animation instance in the registry
type AnimationInstance =
  { handle :: AnimationHandle
  , startTime :: FrameTime
  , duration :: FrameTime      -- Duration in ms
  , delay :: FrameTime         -- Delay before start in ms
  , easing :: EasingType
  , direction :: AnimationDirection
  , iteration :: AnimationIteration
  , phase :: AnimationPhase
  }

-- | Easing function type
data EasingType
  = EasingLinear
  | EasingEaseIn
  | EasingEaseOut
  | EasingEaseInOut
  | EasingSpring

derive instance eqEasingType :: Eq EasingType

-- | Animation direction
data AnimationDirection
  = DirectionNormal
  | DirectionReverse
  | DirectionAlternate
  | DirectionAlternateReverse

derive instance eqAnimationDirection :: Eq AnimationDirection

-- | Animation iteration count
data AnimationIteration
  = IterateOnce
  | IterateCount Int
  | IterateInfinite

derive instance eqAnimationIteration :: Eq AnimationIteration

-- | Registry of active animations
type AnimationRegistry =
  { animations :: Array AnimationInstance
  , nextHandle :: AnimationHandle
  }

-- | Create empty animation registry
mkAnimationRegistry :: AnimationRegistry
mkAnimationRegistry =
  { animations: []
  , nextHandle: 1
  }

-- | Register a new animation
registerAnimation 
  :: FrameTime      -- Current time
  -> FrameTime      -- Duration
  -> FrameTime      -- Delay
  -> EasingType
  -> AnimationDirection
  -> AnimationIteration
  -> AnimationRegistry
  -> Tuple AnimationHandle AnimationRegistry
registerAnimation currentTime duration delay easing direction iteration registry =
  let
    handle = registry.nextHandle
    instance_ = 
      { handle
      , startTime: currentTime
      , duration
      , delay
      , easing
      , direction
      , iteration
      , phase: AnimationIdle
      }
    newRegistry =
      { animations: snoc registry.animations instance_
      , nextHandle: handle + 1
      }
  in
    Tuple handle newRegistry

-- | Unregister an animation
unregisterAnimation :: AnimationHandle -> AnimationRegistry -> AnimationRegistry
unregisterAnimation handle registry =
  { animations: filter (\a -> not (a.handle == handle)) registry.animations
  , nextHandle: registry.nextHandle
  }

-- | Get animation phase by handle
getAnimationPhase :: AnimationHandle -> AnimationRegistry -> AnimationPhase
getAnimationPhase handle registry =
  let
    found = Array.find (\a -> a.handle == handle) registry.animations
  in
    case found of
      Just anim -> anim.phase
      Nothing -> AnimationIdle

-- | Get all active animations
getAllAnimations :: AnimationRegistry -> Array AnimationInstance
getAllAnimations registry = registry.animations

-- | Advance all animations by delta time
tickAnimations :: FrameTime -> FrameTime -> AnimationRegistry -> AnimationRegistry
tickAnimations currentTime deltaTime registry =
  { animations: map (tickAnimation currentTime deltaTime) registry.animations
  , nextHandle: registry.nextHandle
  }

-- | Advance single animation
tickAnimation :: FrameTime -> FrameTime -> AnimationInstance -> AnimationInstance
tickAnimation currentTime _ anim =
  let
    elapsed = currentTime - anim.startTime - anim.delay
    progress = if elapsed < 0.0 then 0.0
               else if anim.duration > 0.0 then min 1.0 (elapsed / anim.duration)
               else 1.0
    newPhase = if elapsed < 0.0 then AnimationIdle
               else if progress >= 1.0 then AnimationComplete
               else AnimationRunning progress
  in
    anim { phase = newPhase }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // spring state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique handle for registered spring
type SpringHandle = Int

-- | Spring physics instance
type SpringInstance =
  { handle :: SpringHandle
  , current :: Number          -- Current value
  , target :: Number           -- Target value
  , velocity :: Number         -- Current velocity
  , stiffness :: Number        -- Spring stiffness (k)
  , damping :: Number          -- Damping coefficient
  , mass :: Number             -- Mass
  , restThreshold :: Number    -- Velocity threshold for "at rest"
  }

-- | Registry of active springs
type SpringRegistry =
  { springs :: Array SpringInstance
  , nextHandle :: SpringHandle
  }

-- | Create empty spring registry
mkSpringRegistry :: SpringRegistry
mkSpringRegistry =
  { springs: []
  , nextHandle: 1
  }

-- | Register a new spring
registerSpring
  :: Number         -- Initial value
  -> Number         -- Target value
  -> Number         -- Stiffness
  -> Number         -- Damping
  -> SpringRegistry
  -> Tuple SpringHandle SpringRegistry
registerSpring initial target stiffness damping registry =
  let
    handle = registry.nextHandle
    instance_ =
      { handle
      , current: initial
      , target
      , velocity: 0.0
      , stiffness
      , damping
      , mass: 1.0
      , restThreshold: 0.001
      }
    newRegistry =
      { springs: snoc registry.springs instance_
      , nextHandle: handle + 1
      }
  in
    Tuple handle newRegistry

-- | Get spring current value
getSpringValue :: SpringHandle -> SpringRegistry -> Number
getSpringValue handle registry =
  let
    found = Array.find (\s -> s.handle == handle) registry.springs
  in
    case found of
      Just spring -> spring.current
      Nothing -> 0.0

-- | Set spring target value
setSpringTarget :: SpringHandle -> Number -> SpringRegistry -> SpringRegistry
setSpringTarget handle newTarget registry =
  { springs: map updateTarget registry.springs
  , nextHandle: registry.nextHandle
  }
  where
    updateTarget s = if s.handle == handle then s { target = newTarget } else s

-- | Advance all springs by delta time
tickSprings :: FrameTime -> SpringRegistry -> SpringRegistry
tickSprings deltaTime registry =
  { springs: map (tickSpring deltaTime) registry.springs
  , nextHandle: registry.nextHandle
  }

-- | Advance single spring using verlet integration
tickSpring :: FrameTime -> SpringInstance -> SpringInstance
tickSpring deltaTimeMs spring =
  let
    dt = deltaTimeMs / 1000.0  -- Convert to seconds
    displacement = spring.target - spring.current
    
    -- Hooke's law: F = -kx - cv
    -- a = F/m = (-kx - cv) / m
    springForce = spring.stiffness * displacement
    dampingForce = spring.damping * spring.velocity
    acceleration = (springForce - dampingForce) / spring.mass
    
    -- Semi-implicit Euler integration
    newVelocity = spring.velocity + acceleration * dt
    newCurrent = spring.current + newVelocity * dt
    
    -- Check if at rest
    isAtRest = absNum displacement < spring.restThreshold && 
               absNum newVelocity < spring.restThreshold
    
    finalCurrent = if isAtRest then spring.target else newCurrent
    finalVelocity = if isAtRest then 0.0 else newVelocity
  in
    spring { current = finalCurrent, velocity = finalVelocity }
  where
    absNum n = if n < 0.0 then negate n else n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // viewport state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Viewport/window state
type ViewportState =
  { width :: Number            -- Width in CSS pixels
  , height :: Number           -- Height in CSS pixels
  , devicePixelRatio :: Number -- Device pixel ratio
  , orientation :: ViewportOrientation
  }

-- | Viewport orientation
data ViewportOrientation
  = OrientationPortrait
  | OrientationLandscape
  | OrientationSquare

derive instance eqViewportOrientation :: Eq ViewportOrientation

instance showViewportOrientation :: Show ViewportOrientation where
  show OrientationPortrait = "OrientationPortrait"
  show OrientationLandscape = "OrientationLandscape"
  show OrientationSquare = "OrientationSquare"

-- | Create viewport state
mkViewportState :: Number -> Number -> Number -> ViewportState
mkViewportState width height dpr =
  { width
  , height
  , devicePixelRatio: dpr
  , orientation: if width > height then OrientationLandscape
                 else if height > width then OrientationPortrait
                 else OrientationSquare
  }

-- | Get viewport width
viewportWidth :: ViewportState -> Number
viewportWidth state = state.width

-- | Get viewport height
viewportHeight :: ViewportState -> Number
viewportHeight state = state.height

-- | Get device pixel ratio
viewportDPI :: ViewportState -> Number
viewportDPI state = state.devicePixelRatio

-- | Get viewport orientation
viewportOrientation :: ViewportState -> ViewportOrientation
viewportOrientation state = state.orientation

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // performance state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Performance metrics for frame budgeting
type PerformanceState =
  { targetFPS :: Number        -- Target frame rate
  , actualFPS :: Number        -- Measured frame rate
  , gpuBudgetMs :: Number      -- GPU time budget per frame
  , gpuUsedMs :: Number        -- GPU time used this frame
  , cpuBudgetMs :: Number      -- CPU time budget per frame
  , cpuUsedMs :: Number        -- CPU time used this frame
  , droppedFrames :: Int       -- Count of dropped frames
  , lastDropTime :: FrameTime  -- Time of last frame drop
  }

-- | Create performance state
mkPerformanceState :: Number -> PerformanceState
mkPerformanceState targetFrameRate =
  let budgetMs = 1000.0 / targetFrameRate
  in
    { targetFPS: targetFrameRate
    , actualFPS: targetFrameRate
    , gpuBudgetMs: budgetMs * 0.8  -- 80% for GPU
    , gpuUsedMs: 0.0
    , cpuBudgetMs: budgetMs * 0.2  -- 20% for CPU
    , cpuUsedMs: 0.0
    , droppedFrames: 0
    , lastDropTime: 0.0
    }

-- | Get target FPS
targetFPS :: PerformanceState -> Number
targetFPS state = state.targetFPS

-- | Get actual measured FPS
actualFPS :: PerformanceState -> Number
actualFPS state = state.actualFPS

-- | Get GPU budget in milliseconds
gpuBudgetMs :: PerformanceState -> Number
gpuBudgetMs state = state.gpuBudgetMs

-- | Get GPU time used in milliseconds
gpuUsedMs :: PerformanceState -> Number
gpuUsedMs state = state.gpuUsedMs

-- | Check if last frame was dropped
frameDropped :: PerformanceState -> Boolean
frameDropped state = state.gpuUsedMs > state.gpuBudgetMs

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // framestate construction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create frame state with initial values
mkFrameState 
  :: FrameTime      -- Start time
  -> Number         -- Target FPS
  -> Number         -- Viewport width
  -> Number         -- Viewport height
  -> Number         -- Device pixel ratio
  -> FrameState
mkFrameState startTime targetFrameRate width height dpr =
  { time: mkTimeState startTime targetFrameRate
  , mouse: mkMouseState
  , animations: mkAnimationRegistry
  , springs: mkSpringRegistry
  , viewport: mkViewportState width height dpr
  , performance: mkPerformanceState targetFrameRate
  }

-- | Create empty/default frame state
emptyFrameState :: FrameState
emptyFrameState = mkFrameState 0.0 60.0 1920.0 1080.0 1.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // framestate updates
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Update time state
updateTime :: FrameTime -> FrameState -> FrameState
updateTime newTime state =
  state { time = advanceTime newTime state.time }

-- | Update mouse state
updateMouse 
  :: Number         -- New X
  -> Number         -- New Y
  -> Array MouseButton  -- Current buttons
  -> Maybe Int      -- Hover target
  -> FrameState 
  -> FrameState
updateMouse x y buttons hoverTarget state =
  let
    prevMouse = state.mouse
    newMouse = prevMouse
      { x = x
      , y = y
      , prevX = prevMouse.x
      , prevY = prevMouse.y
      , velocityX = x - prevMouse.x
      , velocityY = y - prevMouse.y
      , buttons = buttons
      , hoverTarget = hoverTarget
      }
  in
    state { mouse = newMouse }

-- | Update viewport state
updateViewport :: Number -> Number -> Number -> FrameState -> FrameState
updateViewport width height dpr state =
  state { viewport = mkViewportState width height dpr }

-- | Update performance state
updatePerformance :: Number -> Number -> FrameState -> FrameState
updatePerformance gpuMs cpuMs state =
  let
    newPerf = state.performance
      { gpuUsedMs = gpuMs
      , cpuUsedMs = cpuMs
      , actualFPS = if state.time.delta > 0.0 then 1000.0 / state.time.delta else 0.0
      }
  in
    state { performance = newPerf }

-- | Tick all animations and springs
tick :: FrameTime -> FrameState -> FrameState
tick newTime state =
  let
    timeState = advanceTime newTime state.time
    deltaTime = timeState.delta
  in
    state
      { time = timeState
      , animations = tickAnimations newTime deltaTime state.animations
      , springs = tickSprings deltaTime state.springs
      }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // framestate queries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if mouse is hovering over element with given PickId
isHovering :: Int -> FrameState -> Boolean
isHovering pickId state = state.mouse.hoverTarget == Just pickId

-- | Check if mouse button is pressed
isPressed :: MouseButton -> FrameState -> Boolean
isPressed button state = Array.elem button state.mouse.buttons

-- | Get animation progress (0.0-1.0)
animationProgress :: AnimationHandle -> FrameState -> Number
animationProgress handle state =
  case getAnimationPhase handle state.animations of
    AnimationIdle -> 0.0
    AnimationRunning p -> p
    AnimationComplete -> 1.0
    AnimationReversing p -> p

-- | Get spring current value
springValue :: SpringHandle -> FrameState -> Number
springValue handle state = getSpringValue handle state.springs

-- | Get time since app start in milliseconds
timeSinceStart :: FrameState -> FrameTime
timeSinceStart state = elapsedMs state.time

-- | Get frames per second
framesPerSecond :: FrameState -> Number
framesPerSecond state = fps state.time

-- | Get total number of active animations
animationCount :: FrameState -> Int
animationCount state = length state.animations.animations

-- | Get spring value with default (if spring not found)
springValueOr :: Number -> SpringHandle -> FrameState -> Number
springValueOr defaultValue handle state =
  fromMaybe defaultValue $ getSpringValueMaybe handle state.springs

-- | Try to get spring value (returns Maybe)
getSpringValueMaybe :: SpringHandle -> SpringRegistry -> Maybe Number
getSpringValueMaybe handle registry =
  case find (\s -> s.handle == handle) registry.springs of
    Just spring -> Just spring.current
    Nothing -> Nothing

-- | Clamp FPS to reasonable bounds
clampedFPS :: FrameState -> Number
clampedFPS state = 
  let rawFPS = fps state.time
  in min 240.0 $ max 1.0 rawFPS

-- | Check if any animations are running
hasActiveAnimations :: FrameState -> Boolean
hasActiveAnimations state = not $ length state.animations.animations == 0

-- | Get frame number as a Number (for interpolation calculations)
frameNumberAsNumber :: FrameState -> Number
frameNumberAsNumber state = Int.toNumber $ frameNumber state.time
