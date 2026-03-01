-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // brush // eraser // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Eraser Types — ADTs for removal and correction tools.
-- |
-- | ## Design Philosophy
-- |
-- | Erasers are not simply "undo" — they are tools with distinct behaviors:
-- |   - **AlphaErase**: Remove to transparency
-- |   - **BackgroundErase**: Reveal background color
-- |   - **LayerErase**: Clear current layer only
-- |   - **HistoryErase**: Restore from history state
-- |
-- | ## Dependencies
-- | - Prelude

module Hydrogen.Schema.Brush.Eraser.Types
  ( -- * EraserMode ADT
    EraserMode
      ( AlphaErase
      , BackgroundErase
      , LayerErase
      , AllLayersErase
      , AutoErase
      , HistoryErase
      )
  , allEraserModes
  , eraserModeDescription
  , eraserModeToId
  , eraserModeDebugInfo
  , affectsMultipleLayers
  , sameEraserMode
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (==)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // eraser mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode of eraser operation.
-- |
-- | Determines what the eraser reveals or restores.
data EraserMode
  = AlphaErase       -- ^ Remove to transparency
  | BackgroundErase  -- ^ Reveal background color
  | LayerErase       -- ^ Clear current layer only
  | AllLayersErase   -- ^ Clear through all layers
  | AutoErase        -- ^ Smart edge detection (magic eraser)
  | HistoryErase     -- ^ Restore from history state

derive instance eqEraserMode :: Eq EraserMode
derive instance ordEraserMode :: Ord EraserMode

instance showEraserMode :: Show EraserMode where
  show AlphaErase = "(EraserMode AlphaErase)"
  show BackgroundErase = "(EraserMode BackgroundErase)"
  show LayerErase = "(EraserMode LayerErase)"
  show AllLayersErase = "(EraserMode AllLayersErase)"
  show AutoErase = "(EraserMode AutoErase)"
  show HistoryErase = "(EraserMode HistoryErase)"

-- | All eraser mode variants.
allEraserModes :: Array EraserMode
allEraserModes =
  [ AlphaErase
  , BackgroundErase
  , LayerErase
  , AllLayersErase
  , AutoErase
  , HistoryErase
  ]

-- | Human-readable description of each eraser mode.
eraserModeDescription :: EraserMode -> String
eraserModeDescription AlphaErase =
  "Remove pixels to full transparency"
eraserModeDescription BackgroundErase =
  "Reveal the background color or pattern"
eraserModeDescription LayerErase =
  "Clear only the current layer, leave others intact"
eraserModeDescription AllLayersErase =
  "Clear through all visible layers to transparency"
eraserModeDescription AutoErase =
  "Smart eraser with color-based edge detection"
eraserModeDescription HistoryErase =
  "Restore pixels from a previous history state"

-- | Convert eraser mode to string ID.
eraserModeToId :: EraserMode -> String
eraserModeToId AlphaErase = "alpha"
eraserModeToId BackgroundErase = "background"
eraserModeToId LayerErase = "layer"
eraserModeToId AllLayersErase = "all-layers"
eraserModeToId AutoErase = "auto"
eraserModeToId HistoryErase = "history"

-- | Generate debug info for eraser mode.
eraserModeDebugInfo :: EraserMode -> String
eraserModeDebugInfo mode =
  "EraserMode: " <> eraserModeToId mode <>
  " — " <> eraserModeDescription mode

-- | Check if eraser mode affects multiple layers.
affectsMultipleLayers :: EraserMode -> Boolean
affectsMultipleLayers AllLayersErase = true
affectsMultipleLayers AutoErase = true  -- samples all layers
affectsMultipleLayers _ = false

-- | Check if two eraser modes are the same.
sameEraserMode :: EraserMode -> EraserMode -> Boolean
sameEraserMode a b = eraserModeToId a == eraserModeToId b
