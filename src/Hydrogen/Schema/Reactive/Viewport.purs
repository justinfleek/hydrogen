-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // reactive // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport — A first-class container for displaying content.
-- |
-- | ## Philosophy
-- |
-- | A Viewport is NOT just "the browser window." It's a **bounded viewing region**
-- | with its own identity, settings, and controls. Think:
-- |
-- | - A video player viewport (with playback controls, fullscreen toggle)
-- | - A document viewport (with zoom, scroll position, page navigation)
-- | - A 3D scene viewport (with camera controls, render settings)
-- | - A dashboard viewport (with widget arrangement, refresh interval)
-- | - A code editor viewport (with syntax highlighting, line numbers)
-- | - A split pane viewport (one of N viewports in a layout)
-- |
-- | Each viewport has:
-- | - **Identity** (UUID5) — deterministic, reproducible across sessions
-- | - **Dimensions** — current width/height in CSS pixels
-- | - **Settings** — configuration specific to the content type
-- | - **Controls** — actions available to manipulate the viewport
-- | - **Content** — what's being displayed (polymorphic)
-- |
-- | ## Breakpoints vs Viewport
-- |
-- | Breakpoints describe **size thresholds** — they're properties OF a viewport.
-- | A viewport IS the container; breakpoints describe its current state.
-- |
-- | ## Container Queries
-- |
-- | Modern responsive design responds to **container size**, not just window size.
-- | A Viewport naturally supports this — its dimensions are always known,
-- | independent of the browser window.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - `Viewport.Types` — Core type definitions
-- | - `Viewport.Breakpoints` — Breakpoint values and detection
-- | - `Viewport.Core` — Viewport type, constructors, accessors
-- | - `Viewport.Responsive` — Responsive value system
-- | - `Viewport.CSS` — CSS generation utilities
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Reactive.Viewport as Viewport
-- |
-- | -- Create a viewport for a dashboard
-- | dashboardViewport = Viewport.viewport
-- |   { namespace: "acme-corp"
-- |   , name: "main-dashboard"
-- |   , width: 1920
-- |   , height: 1080
-- |   }
-- |
-- | -- Get deterministic ID
-- | Viewport.getId dashboardViewport  -- ViewportId "a3f8c2d1-..."
-- |
-- | -- Query current breakpoint
-- | Viewport.getBreakpoint dashboardViewport  -- Xxl
-- | ```

module Hydrogen.Schema.Reactive.Viewport
  ( module Types
  , module Breakpoints
  , module Core
  , module Responsive
  , module CSS
  ) where

import Hydrogen.Schema.Reactive.Viewport.Types as Types
import Hydrogen.Schema.Reactive.Viewport.Breakpoints as Breakpoints
import Hydrogen.Schema.Reactive.Viewport.Core as Core
import Hydrogen.Schema.Reactive.Viewport.Responsive as Responsive
import Hydrogen.Schema.Reactive.Viewport.CSS as CSS
