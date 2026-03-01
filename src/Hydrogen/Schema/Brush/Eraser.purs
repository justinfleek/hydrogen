-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // brush // eraser
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Eraser — Removal and correction tools for digital painting.
-- |
-- | ## Module Structure
-- |
-- | - **Types**: EraserMode ADT (Alpha, Background, Layer, History, etc.)
-- | - **Config**: Configuration records and presets
-- |
-- | ## Eraser Modes
-- |
-- | - **AlphaErase**: Remove to transparency
-- | - **BackgroundErase**: Reveal background color
-- | - **LayerErase**: Clear current layer only
-- | - **AllLayersErase**: Clear through all layers
-- | - **AutoErase**: Smart edge detection (magic eraser)
-- | - **HistoryErase**: Restore from history state
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Brush.Eraser.Types
-- | - Hydrogen.Schema.Brush.Eraser.Config

module Hydrogen.Schema.Brush.Eraser
  ( module Hydrogen.Schema.Brush.Eraser.Types
  , module Hydrogen.Schema.Brush.Eraser.Config
  ) where

import Hydrogen.Schema.Brush.Eraser.Types
  ( EraserMode
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
  )

import Hydrogen.Schema.Brush.Eraser.Config
  ( EraserConfig
  , defaultEraserConfig
  , hardEraserConfig
  , softEraserConfig
  , blockEraserConfig
  , kneadedEraserConfig
  , historyBrushConfig
  , AutoEraseConfig
  , defaultAutoEraseConfig
  , preciseAutoEraseConfig
  , looseAutoEraseConfig
  , HistoryEraseConfig
  , defaultHistoryEraseConfig
  , impressionistHistoryConfig
  , eraserConfigDebugInfo
  )
