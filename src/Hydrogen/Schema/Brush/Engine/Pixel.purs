-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // brush // engine // pixel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pixel Engine — Raster stamp-based brush rendering configuration.
-- |
-- | ## Design Philosophy
-- |
-- | The pixel engine stamps a brush tip image at intervals along the stroke.
-- | It's the fastest and most common brush engine, suitable for general
-- | digital painting, sketching, and most everyday brush work.
-- |
-- | ## Key Parameters
-- |
-- | - **spacing**: Distance between dabs as percentage of brush diameter
-- | - **blendMode**: How dabs composite onto the canvas
-- | - **antialiasing**: Smooth edge rendering
-- | - **subpixelPositioning**: Sub-pixel accuracy for smooth diagonals
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Brush.Engine.Pixel
  ( -- * PixelEngineConfig Record
    PixelEngineConfig
  , defaultPixelEngineConfig
  , pixelEngineConfigDebugInfo
  
  -- * Presets
  , hardBrushConfig
  , softBrushConfig
  , pencilConfig
  , inkConfig
  
  -- * Queries
  , hasAntialiasing
  , hasSubpixel
  , isHighQuality
  , hasNaturalMediaFeatures
  , isFullyNaturalMedia
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (&&)
  , (||)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // pixel engine config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for the pixel (stamp-based) brush engine.
-- |
-- | ## Field Descriptions
-- |
-- | - `spacing`: Distance between dabs as percentage of diameter (1-1000%)
-- | - `antialiasing`: Enable smooth edge rendering
-- | - `subpixelPositioning`: Enable sub-pixel position accuracy
-- | - `buildUp`: Allow opacity to accumulate in single stroke
-- | - `wetEdges`: Concentrate paint at stroke edges (watercolor effect)
-- |
-- | ## Usage Notes
-- |
-- | - Lower spacing = smoother strokes but slower performance
-- | - Typical range: 10-25% for smooth strokes, 50-100% for textured
-- | - subpixelPositioning improves diagonals at cost of slight blur
type PixelEngineConfig =
  { spacing :: Number               -- 1-1000% of brush diameter
  , antialiasing :: Boolean         -- Smooth edges
  , subpixelPositioning :: Boolean  -- Sub-pixel accuracy
  , buildUp :: Boolean              -- Opacity accumulates in stroke
  , wetEdges :: Boolean             -- Paint at edges (watercolor)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default pixel engine configuration.
-- |
-- | General-purpose settings suitable for most painting tasks.
-- | Smooth strokes with antialiasing and standard spacing.
defaultPixelEngineConfig :: PixelEngineConfig
defaultPixelEngineConfig =
  { spacing: 25.0                   -- Standard smooth spacing
  , antialiasing: true              -- Smooth edges by default
  , subpixelPositioning: true       -- Accurate positioning
  , buildUp: false                  -- No opacity accumulation
  , wetEdges: false                 -- No watercolor effect
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hard brush: crisp edges, tight spacing.
-- |
-- | Used for: precise painting, clean edges, hard-edged shapes.
hardBrushConfig :: PixelEngineConfig
hardBrushConfig =
  { spacing: 10.0                   -- Tight spacing for smooth strokes
  , antialiasing: true              -- Still want smooth edges
  , subpixelPositioning: true       -- Maximum precision
  , buildUp: false                  -- Clean, flat color
  , wetEdges: false                 -- No watercolor effect
  }

-- | Soft brush: smooth blending, standard spacing.
-- |
-- | Used for: blending, soft shading, atmospheric effects.
softBrushConfig :: PixelEngineConfig
softBrushConfig =
  { spacing: 20.0                   -- Smooth spacing
  , antialiasing: true              -- Smooth edges
  , subpixelPositioning: true       -- Accurate positioning
  , buildUp: true                   -- Opacity builds up
  , wetEdges: false                 -- No watercolor effect
  }

-- | Pencil: textured strokes with visible spacing.
-- |
-- | Used for: sketching, pencil simulation, textured lines.
pencilConfig :: PixelEngineConfig
pencilConfig =
  { spacing: 35.0                   -- Visible texture
  , antialiasing: true              -- Still smooth
  , subpixelPositioning: true       -- Accurate lines
  , buildUp: true                   -- Natural pencil buildup
  , wetEdges: false                 -- No watercolor effect
  }

-- | Ink: crisp lines with buildup for overlapping strokes.
-- |
-- | Used for: inking, line art, comic illustration.
inkConfig :: PixelEngineConfig
inkConfig =
  { spacing: 15.0                   -- Smooth, dense strokes
  , antialiasing: true              -- Clean edges
  , subpixelPositioning: true       -- Precise lines
  , buildUp: false                  -- Flat, consistent ink
  , wetEdges: false                 -- No watercolor effect
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if antialiasing is enabled.
hasAntialiasing :: PixelEngineConfig -> Boolean
hasAntialiasing cfg = cfg.antialiasing

-- | Check if subpixel positioning is enabled.
hasSubpixel :: PixelEngineConfig -> Boolean
hasSubpixel cfg = cfg.subpixelPositioning

-- | Check if config has all quality features enabled.
-- |
-- | Returns true when both antialiasing and subpixel positioning
-- | are enabled. This represents maximum rendering quality.
isHighQuality :: PixelEngineConfig -> Boolean
isHighQuality cfg =
  cfg.antialiasing && cfg.subpixelPositioning

-- | Check if config has any natural media features.
-- |
-- | Returns true when buildUp OR wetEdges are enabled.
-- | Indicates the brush simulates some aspect of traditional media.
hasNaturalMediaFeatures :: PixelEngineConfig -> Boolean
hasNaturalMediaFeatures cfg =
  cfg.buildUp || cfg.wetEdges

-- | Check if config has all natural media features.
-- |
-- | Returns true when BOTH buildUp AND wetEdges are enabled.
-- | This represents full traditional media simulation.
isFullyNaturalMedia :: PixelEngineConfig -> Boolean
isFullyNaturalMedia cfg =
  cfg.buildUp && cfg.wetEdges

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info string for PixelEngineConfig.
-- |
-- | Produces a parseable, unambiguous representation.
pixelEngineConfigDebugInfo :: PixelEngineConfig -> String
pixelEngineConfigDebugInfo cfg =
  "(PixelEngineConfig { " <>
  "spacing: " <> show cfg.spacing <> "%, " <>
  "aa: " <> showBool cfg.antialiasing <> ", " <>
  "subpixel: " <> showBool cfg.subpixelPositioning <> ", " <>
  "buildUp: " <> showBool cfg.buildUp <> ", " <>
  "wetEdges: " <> showBool cfg.wetEdges <>
  " })"
  where
    showBool :: Boolean -> String
    showBool b = if b then "on" else "off"
