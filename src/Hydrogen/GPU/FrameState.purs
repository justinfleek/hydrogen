-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // gpu // frame-state
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
-- | - **Input**: Mouse, touch, stylus, gestures (via Input submodule)
-- | - **Animations**: Keyframe animations, spring physics (via Animation submodule)
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
-- | ## Module Structure
-- |
-- | - `FrameState` (this module) — Leader, composite type, construction, updates
-- | - `FrameState.Types` — Core type aliases (FrameTime, FrameNumber)
-- | - `FrameState.Time` — TimeState and temporal functions
-- | - `FrameState.Mouse` — MouseState and pointer input
-- | - `FrameState.Viewport` — ViewportState, shapes, tensor access
-- | - `FrameState.Performance` — PerformanceState and budgeting
-- | - `FrameState.Animation` — AnimationRegistry, SpringRegistry
-- | - `FrameState.Debug` — Structured debug output

module Hydrogen.GPU.FrameState
  ( -- * Core Types
    FrameState
  
  -- * Re-export Types module
  , module Types
  
  -- * Re-export Time module
  , module Time
  
  -- * Re-export Mouse module
  , module Mouse
  
  -- * Re-export MouseButton (from Gestural.Pointer via Mouse)
  , module PointerButton
  
  -- * Re-export Viewport module
  , module Viewport
  
  -- * Re-export Performance module
  , module Performance
  
  -- * Re-export Animation module
  , module Anim
  
  -- * Re-export Debug module
  , module Debug
  
  -- * Default Values (documented rationale)
  , defaultViewportWidth
  , defaultViewportHeight
  , defaultDevicePixelRatio
  , defaultTargetFPS
  , defaultStartTime
  
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
  , timeSinceStart
  , framesPerSecond
  , animationCount
  , clampedFPS
  , hasActiveAnimations
  , frameNumberAsNumber
  
  -- * Debug Output (composite FrameState)
  , showFrameState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( not
  , (<>)
  , (==)
  , (-)
  , (/)
  , (>)
  , ($)
  , min
  , max
  )

import Data.Array as Array
import Data.Int as Int
import Data.Map as Map
import Data.Maybe (Maybe(Just), fromMaybe)

-- Device units for default values
import Hydrogen.Schema.Dimension.Device 
  ( Pixel(Pixel)
  , DevicePixelRatio
  , dpr
  )

-- ─────────────────────────────────────────────────────────────────────────────
--                                                             // submodule imports
-- ─────────────────────────────────────────────────────────────────────────────

-- Core type aliases
import Hydrogen.GPU.FrameState.Types (FrameTime, FrameNumber) as Types
import Hydrogen.GPU.FrameState.Types (FrameTime)

-- Time state
import Hydrogen.GPU.FrameState.Time 
  ( TimeState
  , mkTimeState
  , advanceTime
  , deltaMs
  , elapsedMs
  , frameNumber
  , fps
  ) as Time
import Hydrogen.GPU.FrameState.Time (TimeState, advanceTime, elapsedMs, frameNumber, fps)

-- Mouse state
import Hydrogen.GPU.FrameState.Mouse
  ( MouseState
  , mkMouseState
  , mousePosition
  , mouseButtons
  , mouseHoverTarget
  , mouseDelta
  , mouseVelocity
  ) as Mouse
import Hydrogen.GPU.FrameState.Mouse (MouseState, mkMouseState)

-- Re-export MouseButton from Gestural.Pointer (via Mouse module re-export)
import Hydrogen.Schema.Gestural.Pointer
  ( MouseButton(MouseLeft, MouseMiddle, MouseRight, MouseBack, MouseForward)
  ) as PointerButton
import Hydrogen.Schema.Gestural.Pointer (MouseButton)

-- Viewport state
import Hydrogen.GPU.FrameState.Viewport
  ( ViewportState
  , ViewportOrientation(OrientationPortrait, OrientationLandscape, OrientationSquare)
  , mkViewportState
  , mkViewportStateWithShape
  , mkCircularViewport
  , mkRoundedRectViewport
  , mkPathViewport
  , mkEllipticalViewport
  , viewportWidth
  , viewportHeight
  , viewportDPI
  , viewportOrientation
  , viewportResized
  , viewportOrientationChanged
  , viewportDPRChanged
  , viewportShapeChanged
  , viewportAnyChange
  , viewportTensor
  , viewportLatentWidth
  , viewportLatentHeight
  , viewportLatentSize
  , viewportClipShape
  , viewportSafeArea
  , viewportWidthDelta
  , viewportHeightDelta
  , updateViewportState
  ) as Viewport
import Hydrogen.GPU.FrameState.Viewport (ViewportState, ViewportOrientation, mkViewportState, updateViewportState)

-- Performance state
import Hydrogen.GPU.FrameState.Performance
  ( PerformanceState
  , mkPerformanceState
  , targetFPS
  , actualFPS
  , gpuBudgetMs
  , gpuUsedMs
  , frameDropped
  ) as Performance
import Hydrogen.GPU.FrameState.Performance (PerformanceState, mkPerformanceState)

-- Animation types
import Hydrogen.GPU.FrameState.Animation
  ( AnimationHandle
  , AnimationPhase
      ( AnimationIdle
      , AnimationRunning
      , AnimationComplete
      , AnimationReversing
      )
  , AnimationInstance
  , EasingType
      ( EasingLinear
      , EasingEaseIn
      , EasingEaseOut
      , EasingEaseInOut
      , EasingSpring
      )
  , AnimationDirection
      ( DirectionNormal
      , DirectionReverse
      , DirectionAlternate
      , DirectionAlternateReverse
      )
  , AnimationIteration
      ( IterateOnce
      , IterateCount
      , IterateInfinite
      )
  , AnimationRegistry
  , mkAnimationRegistry
  , registerAnimation
  , unregisterAnimation
  , getAnimationPhase
  , getAllAnimations
  , tickAnimations
  , SpringHandle
  , SpringInstance
  , SpringRegistry
  , mkSpringRegistry
  , registerSpring
  , getSpringValue
  , getSpringValueMaybe
  , setSpringTarget
  , tickSprings
  , animationsAsList
  , springsAsList
  , runningAnimations
  , completedAnimations
  , animationHandles
  , springHandles
  , findAnimationByPhase
  , anyAnimationRunning
  , allAnimationsComplete
  ) as Anim

-- Qualified for internal use
import Hydrogen.GPU.FrameState.Animation as Animation

-- Debug output
import Hydrogen.GPU.FrameState.Debug
  ( showTimeState
  , showMouseState
  , showViewportState
  , showPerformanceState
  ) as Debug
import Hydrogen.GPU.FrameState.Debug (showTimeState, showMouseState, showViewportState, showPerformanceState)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete frame state for a render pass
-- |
-- | Aggregates all per-frame state needed for rendering:
-- | time, input, animations, viewport, and performance metrics.
type FrameState =
  { time :: TimeState
  , mouse :: MouseState
  , animations :: Animation.AnimationRegistry
  , springs :: Animation.SpringRegistry
  , viewport :: ViewportState
  , performance :: PerformanceState
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // default values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default viewport width (1920 pixels)
-- |
-- | Rationale: Full HD (1920×1080) is the most common desktop resolution globally.
-- | Bounded: Minimum sensible is ~320px (small mobile), max is ~7680px (8K).
defaultViewportWidth :: Pixel
defaultViewportWidth = Pixel 1920.0

-- | Default viewport height (1080 pixels)
-- |
-- | Rationale: Full HD (1920×1080) is the most common desktop resolution globally.
defaultViewportHeight :: Pixel
defaultViewportHeight = Pixel 1080.0

-- | Default device pixel ratio (1.0)
-- |
-- | Rationale: Standard DPR for non-retina displays.
-- | Bounded: Minimum is 0.5, maximum is ~4.0 (highest-end displays).
defaultDevicePixelRatio :: DevicePixelRatio
defaultDevicePixelRatio = dpr 1.0

-- | Default target FPS (60 frames per second)
-- |
-- | Rationale: 60 FPS is the universal baseline for smooth animation.
-- | Bounded: Minimum sensible is ~24 FPS (film), maximum is ~240 FPS (gaming).
defaultTargetFPS :: Number
defaultTargetFPS = 60.0

-- | Default start time (0.0 milliseconds)
-- |
-- | Rationale: Time is measured from application start, so 0.0 is natural origin.
defaultStartTime :: FrameTime
defaultStartTime = 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // framestate construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create frame state with initial values
mkFrameState 
  :: FrameTime
  -> Number
  -> Pixel
  -> Pixel
  -> DevicePixelRatio
  -> FrameState
mkFrameState startTime targetFrameRate width height devicePixelRatioVal =
  { time: Time.mkTimeState startTime targetFrameRate
  , mouse: mkMouseState
  , animations: Animation.mkAnimationRegistry
  , springs: Animation.mkSpringRegistry
  , viewport: mkViewportState width height devicePixelRatioVal
  , performance: mkPerformanceState targetFrameRate
  }

-- | Create empty/default frame state
-- |
-- | Uses documented default values: 1920×1080 at 1.0 DPR, 60 FPS, start at 0.0.
emptyFrameState :: FrameState
emptyFrameState = mkFrameState 
  defaultStartTime 
  defaultTargetFPS 
  defaultViewportWidth 
  defaultViewportHeight 
  defaultDevicePixelRatio

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // framestate updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update time state
updateTime :: FrameTime -> FrameState -> FrameState
updateTime newTime state =
  state { time = advanceTime newTime state.time }

-- | Update mouse state
updateMouse 
  :: Number
  -> Number
  -> Array MouseButton
  -> Maybe Int
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
updateViewport :: Pixel -> Pixel -> DevicePixelRatio -> FrameState -> FrameState
updateViewport width height devicePixelRatioVal state =
  state { viewport = updateViewportState width height devicePixelRatioVal state.viewport }

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
      , animations = Animation.tickAnimations newTime deltaTime state.animations
      , springs = Animation.tickSprings deltaTime state.springs
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // framestate queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if mouse is hovering over element with given PickId
isHovering :: Int -> FrameState -> Boolean
isHovering pickId state = state.mouse.hoverTarget == Just pickId

-- | Check if mouse button is pressed
isPressed :: MouseButton -> FrameState -> Boolean
isPressed button state = Array.elem button state.mouse.buttons

-- | Get animation progress (0.0-1.0)
animationProgress :: Animation.AnimationHandle -> FrameState -> Number
animationProgress handle state =
  case Animation.getAnimationPhase handle state.animations of
    Animation.AnimationIdle -> 0.0
    Animation.AnimationRunning p -> p
    Animation.AnimationComplete -> 1.0
    Animation.AnimationReversing p -> p

-- | Get spring current value
springValue :: Animation.SpringHandle -> FrameState -> Number
springValue handle state = Animation.getSpringValue handle state.springs

-- | Get spring value with default (if spring not found)
springValueOr :: Number -> Animation.SpringHandle -> FrameState -> Number
springValueOr defaultValue handle state =
  fromMaybe defaultValue $ Animation.getSpringValueMaybe handle state.springs

-- | Get time since app start in milliseconds
timeSinceStart :: FrameState -> FrameTime
timeSinceStart state = elapsedMs state.time

-- | Get frames per second
framesPerSecond :: FrameState -> Number
framesPerSecond state = fps state.time

-- | Get total number of active animations
animationCount :: FrameState -> Int
animationCount state = Map.size state.animations.animations

-- | Clamp FPS to reasonable bounds
clampedFPS :: FrameState -> Number
clampedFPS state = 
  let rawFPS = fps state.time
  in min 240.0 $ max 1.0 rawFPS

-- | Check if any animations are running
hasActiveAnimations :: FrameState -> Boolean
hasActiveAnimations state = not $ Map.isEmpty state.animations.animations

-- | Get frame number as a Number (for interpolation calculations)
frameNumberAsNumber :: FrameState -> Number
frameNumberAsNumber state = Int.toNumber $ frameNumber state.time

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // debug output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debug string for complete FrameState
-- |
-- | Provides full introspection for debugging at billion-agent scale.
-- | Same FrameState = same debug string = reproducible debugging.
showFrameState :: FrameState -> String
showFrameState fs =
  "(FrameState\n"
  <> "  time: " <> showTimeState fs.time <> "\n"
  <> "  mouse: " <> showMouseState fs.mouse <> "\n"
  <> "  viewport: " <> showViewportState fs.viewport <> "\n"
  <> "  performance: " <> showPerformanceState fs.performance <> "\n"
  <> "  animations: " <> Int.toStringAs Int.decimal (animationCount fs) <> " active\n"
  <> ")"
