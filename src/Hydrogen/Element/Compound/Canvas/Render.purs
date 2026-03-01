-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // element // compound // canvas // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Render — Pure render function for infinite canvas.
-- |
-- | ## Design Philosophy
-- |
-- | The render function is pure: CanvasState -> Element.
-- | It composes all canvas sub-modules to produce the final UI.
-- | No side effects, no DOM manipulation — just Element construction.
-- |
-- | ## Render Structure
-- |
-- | ```
-- | .canvas-container
-- |   .canvas-background
-- |   .canvas-grid-layer
-- |   .canvas-objects-layer
-- |     .canvas-object[n]
-- |   .canvas-guides-layer
-- |   .canvas-selection-layer
-- |     .selection-frame
-- |     .selection-handles
-- |   .canvas-rulers
-- |     .ruler-horizontal
-- |     .ruler-vertical
-- | ```
-- |
-- | ## Compositing Order
-- |
-- | Objects are rendered in zIndex order (lowest first).
-- | Each object applies its compositing settings:
-- | 1. Clip path (binary mask)
-- | 2. Soft mask (alpha)
-- | 3. Track matte (if referenced)
-- | 4. Blend mode
-- | 5. Opacity
-- |
-- | ## Submodules
-- |
-- | This is a leader module that re-exports from:
-- | - Render.Types (CanvasMsg, RenderConfig)
-- | - Render.Helpers (utility functions)
-- | - Render.Objects (object rendering)
-- | - Render.Selection (selection UI rendering)
-- | - Render.Grid (grid rendering)
-- | - Render.Guides (guide rendering)
-- | - Render.Rulers (ruler rendering)
-- | - Render.Layers (main render and layer composition)

module Hydrogen.Element.Compound.Canvas.Render
  ( module Types
  , module Helpers
  , module Objects
  , module Selection
  , module Grid
  , module Guides
  , module Rulers
  , module Layers
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Canvas.Render.Types as Types
import Hydrogen.Element.Compound.Canvas.Render.Helpers as Helpers
import Hydrogen.Element.Compound.Canvas.Render.Objects as Objects
import Hydrogen.Element.Compound.Canvas.Render.Selection as Selection
import Hydrogen.Element.Compound.Canvas.Render.Grid as Grid
import Hydrogen.Element.Compound.Canvas.Render.Guides as Guides
import Hydrogen.Element.Compound.Canvas.Render.Rulers as Rulers
import Hydrogen.Element.Compound.Canvas.Render.Layers as Layers
