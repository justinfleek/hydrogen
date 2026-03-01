-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // element // compound // canvas // types // guide
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Guide Types — Ruler guides, configuration, and bounds.
-- |
-- | ## Scope
-- |
-- | This module defines types for guides and canvas configuration:
-- |
-- | - **GuideOrientation**: Horizontal or vertical
-- | - **Guide**: A ruler guide at a specific position
-- | - **CanvasConfig**: Complete canvas configuration
-- | - **CanvasBounds**: Infinite or finite canvas bounds
-- |
-- | ## Guides
-- |
-- | Guides are visual alignment aids that can be snapped to.
-- | They can be horizontal or vertical and positioned in canvas coordinates.
-- |
-- | ## Canvas Bounds
-- |
-- | Canvases can be infinite (pan forever) or finite (clamped to rectangle).
-- | Design tools typically use infinite bounds; export/artboards use finite.

module Hydrogen.Element.Compound.Canvas.Types.Guide
  ( -- * Guide Types
    Guide(Guide)
  , GuideOrientation
    ( GuideHorizontal
    , GuideVertical
    )
  , guideHorizontal
  , guideVertical
  , guidePosition
  , guideId
  
  -- * Canvas Config
  , CanvasConfig
  , defaultCanvasConfig
  , withMinZoom
  , withMaxZoom
  , withGridConfig
  , withSnapConfig
  , withBackgroundColor
  
  -- * Canvas Dimensions
  , CanvasBounds
    ( Infinite
    , Finite
    )
  , infiniteBounds
  , finiteBounds
  , boundsContains
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (>=)
  , (<=)
  , (&&)
  , (+)
  )

import Hydrogen.Schema.Graph.Viewport 
  ( ViewportZoom
  , viewportZoom
  )

import Hydrogen.Element.Compound.Canvas.Types.Grid 
  ( GridConfig
  , SnapConfig
  , defaultGridConfig
  , defaultSnapConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // guide types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Guide orientation.
data GuideOrientation
  = GuideHorizontal
  | GuideVertical

derive instance eqGuideOrientation :: Eq GuideOrientation

instance showGuideOrientation :: Show GuideOrientation where
  show GuideHorizontal = "horizontal"
  show GuideVertical = "vertical"

-- | A ruler guide.
data Guide = Guide
  { id :: String
  , orientation :: GuideOrientation
  , position :: Number          -- Position in canvas coordinates
  , color :: String             -- Guide color (hex)
  , locked :: Boolean
  }

derive instance eqGuide :: Eq Guide

instance showGuide :: Show Guide where
  show (Guide g) = "Guide(" <> g.id <> " " <> show g.orientation <> " @" <> show g.position <> ")"

-- | Create horizontal guide.
guideHorizontal :: String -> Number -> Guide
guideHorizontal id pos = Guide
  { id
  , orientation: GuideHorizontal
  , position: pos
  , color: "#06b6d4"            -- Cyan-500
  , locked: false
  }

-- | Create vertical guide.
guideVertical :: String -> Number -> Guide
guideVertical id pos = Guide
  { id
  , orientation: GuideVertical
  , position: pos
  , color: "#06b6d4"            -- Cyan-500
  , locked: false
  }

-- | Get guide position.
guidePosition :: Guide -> Number
guidePosition (Guide g) = g.position

-- | Get guide ID.
guideId :: Guide -> String
guideId (Guide g) = g.id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // canvas config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete canvas configuration.
type CanvasConfig =
  { minZoom :: ViewportZoom
  , maxZoom :: ViewportZoom
  , gridConfig :: GridConfig
  , snapConfig :: SnapConfig
  , backgroundColor :: String
  , rulerVisible :: Boolean
  , rulerUnits :: String        -- "px" | "pt" | "mm" | "in"
  , scrollbarsVisible :: Boolean
  , antialiased :: Boolean
  , pixelPerfect :: Boolean     -- Snap to whole pixels when rendering
  }

-- | Default canvas configuration.
defaultCanvasConfig :: CanvasConfig
defaultCanvasConfig =
  { minZoom: viewportZoom 0.01   -- 1%
  , maxZoom: viewportZoom 64.0   -- 6400%
  , gridConfig: defaultGridConfig
  , snapConfig: defaultSnapConfig
  , backgroundColor: "#1e1e1e"  -- Dark gray
  , rulerVisible: true
  , rulerUnits: "px"
  , scrollbarsVisible: true
  , antialiased: true
  , pixelPerfect: false
  }

-- | Set minimum zoom.
withMinZoom :: ViewportZoom -> CanvasConfig -> CanvasConfig
withMinZoom z config = config { minZoom = z }

-- | Set maximum zoom.
withMaxZoom :: ViewportZoom -> CanvasConfig -> CanvasConfig
withMaxZoom z config = config { maxZoom = z }

-- | Set grid configuration.
withGridConfig :: GridConfig -> CanvasConfig -> CanvasConfig
withGridConfig grid config = config { gridConfig = grid }

-- | Set snap configuration.
withSnapConfig :: SnapConfig -> CanvasConfig -> CanvasConfig
withSnapConfig snap config = config { snapConfig = snap }

-- | Set background color.
withBackgroundColor :: String -> CanvasConfig -> CanvasConfig
withBackgroundColor color config = config { backgroundColor = color }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // canvas dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Canvas bounds (can be infinite or finite).
-- |
-- | - Infinite: No boundaries, pan forever
-- | - Finite: Clamped to specified rectangle
data CanvasBounds
  = Infinite
  | Finite { x :: Number, y :: Number, width :: Number, height :: Number }

derive instance eqCanvasBounds :: Eq CanvasBounds

instance showCanvasBounds :: Show CanvasBounds where
  show Infinite = "infinite"
  show (Finite b) = "bounds(" <> show b.width <> "x" <> show b.height <> ")"

-- | Infinite canvas bounds.
infiniteBounds :: CanvasBounds
infiniteBounds = Infinite

-- | Finite canvas bounds.
finiteBounds :: Number -> Number -> Number -> Number -> CanvasBounds
finiteBounds x y width height = Finite { x, y, width, height }

-- | Check if point is within canvas bounds.
boundsContains :: Number -> Number -> CanvasBounds -> Boolean
boundsContains _ _ Infinite = true
boundsContains px py (Finite b) =
  px >= b.x && px <= (b.x + b.width) &&
  py >= b.y && py <= (b.y + b.height)
