-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brush // eraser // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Eraser Config — Configuration records for eraser tools.
-- |
-- | ## Design Philosophy
-- |
-- | Erasers have configurable properties:
-- |   - Mode determines WHAT is revealed
-- |   - Hardness/Opacity determines HOW it's revealed
-- |   - Brush tip determines the SHAPE of erasure
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Brush.Eraser.Types

module Hydrogen.Schema.Brush.Eraser.Config
  ( -- * EraserConfig
    EraserConfig
  , defaultEraserConfig
  , hardEraserConfig
  , softEraserConfig
  , blockEraserConfig
  , kneadedEraserConfig
  , historyBrushConfig
  
  -- * AutoEraseConfig (Magic Eraser)
  , AutoEraseConfig
  , defaultAutoEraseConfig
  , preciseAutoEraseConfig
  , looseAutoEraseConfig
  
  -- * HistoryEraseConfig
  , HistoryEraseConfig
  , defaultHistoryEraseConfig
  , impressionistHistoryConfig
  
  -- * Debug helpers
  , eraserConfigDebugInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  )

import Hydrogen.Schema.Brush.Eraser.Types
  ( EraserMode
      ( AlphaErase
      , BackgroundErase
      , HistoryErase
      )
  , eraserModeToId
  )


-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // eraser config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Main eraser configuration.
-- |
-- | Controls how the eraser behaves when used.
type EraserConfig =
  { mode :: EraserMode               -- ^ Erase behavior
  , useBrushTip :: Boolean           -- ^ Use current brush shape
  , hardness :: Number               -- ^ Edge hardness (0-100)
  , opacity :: Number                -- ^ Erase strength (0-100)
  , flow :: Number                   -- ^ Erase per dab (0-100)
  , pressureAffectsOpacity :: Boolean -- ^ Pen pressure varies strength
  , antialiasing :: Boolean          -- ^ Smooth edges
  }

-- | Default eraser (soft alpha eraser)
defaultEraserConfig :: EraserConfig
defaultEraserConfig =
  { mode: AlphaErase
  , useBrushTip: false
  , hardness: 50.0
  , opacity: 100.0
  , flow: 100.0
  , pressureAffectsOpacity: true
  , antialiasing: true
  }

-- | Hard eraser (crisp edges, full removal)
hardEraserConfig :: EraserConfig
hardEraserConfig =
  { mode: AlphaErase
  , useBrushTip: false
  , hardness: 100.0
  , opacity: 100.0
  , flow: 100.0
  , pressureAffectsOpacity: false
  , antialiasing: false
  }

-- | Soft eraser (feathered edges)
softEraserConfig :: EraserConfig
softEraserConfig =
  { mode: AlphaErase
  , useBrushTip: false
  , hardness: 0.0
  , opacity: 100.0
  , flow: 100.0
  , pressureAffectsOpacity: true
  , antialiasing: true
  }

-- | Block eraser (square, hard edges, reveals background)
blockEraserConfig :: EraserConfig
blockEraserConfig =
  { mode: BackgroundErase
  , useBrushTip: false  -- uses square shape
  , hardness: 100.0
  , opacity: 100.0
  , flow: 100.0
  , pressureAffectsOpacity: false
  , antialiasing: false
  }

-- | Kneaded eraser (gentle lifting, like charcoal eraser)
kneadedEraserConfig :: EraserConfig
kneadedEraserConfig =
  { mode: AlphaErase
  , useBrushTip: true
  , hardness: 50.0
  , opacity: 30.0  -- gentle
  , flow: 50.0
  , pressureAffectsOpacity: true
  , antialiasing: true
  }

-- | History brush (restore from history)
historyBrushConfig :: EraserConfig
historyBrushConfig =
  { mode: HistoryErase
  , useBrushTip: true
  , hardness: 50.0
  , opacity: 100.0
  , flow: 100.0
  , pressureAffectsOpacity: true
  , antialiasing: true
  }


-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // auto erase config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Auto erase (magic eraser) configuration.
-- |
-- | Erases based on color similarity, like Photoshop's magic eraser.
type AutoEraseConfig =
  { tolerance :: Number              -- ^ Color similarity threshold (0-100)
  , contiguous :: Boolean            -- ^ Only connected areas
  , sampleAllLayers :: Boolean       -- ^ Consider all visible layers
  , antialiasedEdges :: Boolean      -- ^ Smooth removal edges
  }

-- | Default auto erase (moderate tolerance, contiguous)
defaultAutoEraseConfig :: AutoEraseConfig
defaultAutoEraseConfig =
  { tolerance: 32.0
  , contiguous: true
  , sampleAllLayers: false
  , antialiasedEdges: true
  }

-- | Precise auto erase (low tolerance, tight selection)
preciseAutoEraseConfig :: AutoEraseConfig
preciseAutoEraseConfig =
  { tolerance: 10.0
  , contiguous: true
  , sampleAllLayers: false
  , antialiasedEdges: true
  }

-- | Loose auto erase (high tolerance, broad selection)
looseAutoEraseConfig :: AutoEraseConfig
looseAutoEraseConfig =
  { tolerance: 64.0
  , contiguous: false
  , sampleAllLayers: true
  , antialiasedEdges: true
  }


-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // history erase config
-- ═════════════════════════════════════════════════════════════════════════════

-- | History erase configuration.
-- |
-- | Restores pixels from a previous history state.
-- | Can also do "impressionist" restoration with stylized brushwork.
type HistoryEraseConfig =
  { sourceStateIndex :: Int          -- ^ Which history state to restore (0 = current)
  , impressionist :: Boolean         -- ^ Stylized restoration
  , impressionistSize :: Number      -- ^ Brush size for impressionist (percent)
  }

-- | Default history erase (restore from previous state)
defaultHistoryEraseConfig :: HistoryEraseConfig
defaultHistoryEraseConfig =
  { sourceStateIndex: 1  -- one step back
  , impressionist: false
  , impressionistSize: 50.0
  }

-- | Impressionist history (painterly restoration)
impressionistHistoryConfig :: HistoryEraseConfig
impressionistHistoryConfig =
  { sourceStateIndex: 1
  , impressionist: true
  , impressionistSize: 30.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // debug helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info for eraser config.
eraserConfigDebugInfo :: EraserConfig -> String
eraserConfigDebugInfo cfg =
  "EraserConfig { " <>
  "mode: " <> eraserModeToId cfg.mode <>
  ", hardness: " <> show cfg.hardness <> "%" <>
  ", opacity: " <> show cfg.opacity <> "%" <>
  " }"
