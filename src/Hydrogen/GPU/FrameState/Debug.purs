-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // framestate // debug
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Debug — Structured Debug Output for FrameState
-- |
-- | ## Purpose
-- |
-- | Provides human-readable, machine-parseable debug output for all FrameState
-- | components. Follows SHOW_DEBUG_CONVENTION: structured, deterministic output.
-- |
-- | ## Why Structured Debug Output?
-- |
-- | At billion-agent scale, debugging requires:
-- |
-- | - **Deterministic**: Same state → same debug string (always)
-- | - **Parseable**: Agents can read each other's debug output
-- | - **Complete**: All relevant state visible at a glance
-- | - **Grep-able**: Easy to search logs for specific values
-- |
-- | ## Convention
-- |
-- | Format: `(TypeName field1:value1 field2:value2 ...)`
-- |
-- | - Parentheses wrap the entire output
-- | - Type name first
-- | - Fields in key:value format
-- | - Units included where relevant (ms, fps, etc.)

module Hydrogen.GPU.FrameState.Debug
  ( -- * Debug Functions
    showTimeState
  , showMouseState
  , showViewportState
  , showPerformanceState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , (<>)
  )

import Hydrogen.GPU.FrameState.Time (TimeState)
import Hydrogen.GPU.FrameState.Mouse (MouseState)
import Hydrogen.GPU.FrameState.Viewport
  ( ViewportState
  , viewportLatentWidth
  , viewportLatentHeight
  )
import Hydrogen.GPU.FrameState.Performance (PerformanceState)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // debug output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debug string for TimeState
-- |
-- | Format: `(TimeState frame:N current:Xms delta:Yms fps:Z)`
showTimeState :: TimeState -> String
showTimeState t = 
  "(TimeState frame:" <> show t.frame 
  <> " current:" <> show t.current <> "ms"
  <> " delta:" <> show t.delta <> "ms"
  <> " fps:" <> show t.targetFPS
  <> ")"

-- | Debug string for MouseState
-- |
-- | Format: `(MouseState pos:(X,Y) vel:(VX,VY) buttons:[...] hover:... dragging:...)`
showMouseState :: MouseState -> String
showMouseState m =
  "(MouseState pos:(" <> show m.x <> "," <> show m.y <> ")"
  <> " vel:(" <> show m.velocityX <> "," <> show m.velocityY <> ")"
  <> " buttons:" <> show m.buttons
  <> " hover:" <> show m.hoverTarget
  <> " dragging:" <> show m.isDragging
  <> ")"

-- | Debug string for ViewportState
-- |
-- | Format: `(ViewportState WxH @DPR orientation latent:LWxLH changed:[flags])`
showViewportState :: ViewportState -> String
showViewportState v =
  "(ViewportState " <> show v.width <> "×" <> show v.height
  <> " @" <> show v.devicePixelRatio
  <> " " <> show v.orientation
  <> " latent:" <> show (viewportLatentWidth v) <> "×" <> show (viewportLatentHeight v)
  <> " changed:[" 
  <> (if v.resized then "resize " else "")
  <> (if v.orientationChanged then "orient " else "")
  <> (if v.dprChanged then "dpr " else "")
  <> (if v.shapeChanged then "shape" else "")
  <> "])"

-- | Debug string for PerformanceState
-- |
-- | Format: `(PerformanceState target:Xfps actual:Yfps gpu:U/Bms dropped:N)`
showPerformanceState :: PerformanceState -> String
showPerformanceState p =
  "(PerformanceState target:" <> show p.targetFPS <> "fps"
  <> " actual:" <> show p.actualFPS <> "fps"
  <> " gpu:" <> show p.gpuUsedMs <> "/" <> show p.gpuBudgetMs <> "ms"
  <> " dropped:" <> show p.droppedFrames
  <> ")"
