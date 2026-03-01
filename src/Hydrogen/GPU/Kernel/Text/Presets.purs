-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // kernel // text // presets
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Preset Text Rendering Pipelines
-- |
-- | Pre-configured kernel pipelines for common text rendering scenarios:
-- | terminals, IDEs, UI labels, game HUDs, etc.

module Hydrogen.GPU.Kernel.Text.Presets
  ( -- * Terminal Presets
    ghosttyTerminalPipeline
  
  -- * Editor Presets
  , ideEditorPipeline
  
  -- * UI Presets
  , uiLabelPipeline
  
  -- * Game Presets
  , gameHUDPipeline
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  )

import Data.Int as Int

import Hydrogen.GPU.Kernel.Text.Types
  ( TextKernel
      ( KernelTextLayout
      , KernelSubpixelAA
      , KernelCursorBlink
      , KernelTextMask
      , KernelTextSequence
      )
  , TextLayoutKernel(TextLayoutKernel)
  , SubpixelAAKernel(SubpixelAAKernel)
  , CursorBlinkKernel(CursorBlinkKernel)
  , TextMaskKernel(TextMaskKernel)
  , LayoutDirection(LayoutLTR)
  , SubpixelMode(SubpixelRGB, SubpixelNone)
  , SubpixelFilter(FilterGaussian, FilterLinear)
  , CursorStyle(CursorBlock, CursorBar)
  , TextEffect(EffectOutline)
  , terminalConfig
  , editorConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // terminal presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ghostty-style terminal rendering pipeline
-- |
-- | Optimized for 120fps terminal with:
-- | - MSDF for sharp text at any size
-- | - RGB subpixel rendering
-- | - Block cursor with blink
ghosttyTerminalPipeline :: Int -> Int -> TextKernel
ghosttyTerminalPipeline cols rows =
  let
    config = terminalConfig cols rows
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.0
      , maxWidth: 0.0
      , alignX: 0.0
      , alignY: 0.0
      , tabWidth: 8
      , config
      }
    
    subpixel = KernelSubpixelAA $ SubpixelAAKernel
      { mode: SubpixelRGB
      , filter: FilterGaussian
      , gamma: 1.8
      , contrast: 0.5
      , config
      }
    
    cursor = KernelCursorBlink $ CursorBlinkKernel
      { style: CursorBlock
      , blinkRate: 1.0
      , blinkDuty: 0.5
      , fadeTime: 150.0
      , cursorX: 0
      , cursorY: 0
      , colorR: 0.9
      , colorG: 0.9
      , colorB: 0.9
      , config
      }
  in
    KernelTextSequence [layout, subpixel, cursor]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // editor presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | IDE editor pipeline
-- |
-- | Balanced quality/performance for code editing:
-- | - SDF for flexibility
-- | - Optional subpixel
-- | - Bar cursor
ideEditorPipeline :: Int -> Int -> TextKernel
ideEditorPipeline width height =
  let
    config = editorConfig width height
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.4
      , maxWidth: Int.toNumber width
      , alignX: 0.0
      , alignY: 0.0
      , tabWidth: 4
      , config
      }
    
    subpixel = KernelSubpixelAA $ SubpixelAAKernel
      { mode: SubpixelRGB
      , filter: FilterLinear
      , gamma: 2.0
      , contrast: 0.4
      , config
      }
    
    cursor = KernelCursorBlink $ CursorBlinkKernel
      { style: CursorBar
      , blinkRate: 0.5
      , blinkDuty: 0.5
      , fadeTime: 200.0
      , cursorX: 0
      , cursorY: 0
      , colorR: 0.3
      , colorG: 0.5
      , colorB: 1.0
      , config
      }
  in
    KernelTextSequence [layout, subpixel, cursor]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // ui presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | UI label pipeline
-- |
-- | High quality for UI text:
-- | - MSDF for crisp rendering
-- | - Grayscale AA (works on any display)
-- | - No cursor
uiLabelPipeline :: Int -> Int -> TextKernel
uiLabelPipeline width height =
  let
    config = editorConfig width height
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.2
      , maxWidth: Int.toNumber width
      , alignX: 0.5
      , alignY: 0.5
      , tabWidth: 4
      , config
      }
    
    subpixel = KernelSubpixelAA $ SubpixelAAKernel
      { mode: SubpixelNone
      , filter: FilterGaussian
      , gamma: 2.2
      , contrast: 0.5
      , config
      }
  in
    KernelTextSequence [layout, subpixel]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // game presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Game HUD pipeline
-- |
-- | Performance-optimized for games:
-- | - Basic SDF
-- | - No subpixel (too expensive)
-- | - Outline for visibility
gameHUDPipeline :: Int -> Int -> TextKernel
gameHUDPipeline width height =
  let
    config = editorConfig width height
    
    layout = KernelTextLayout $ TextLayoutKernel
      { runs: []
      , direction: LayoutLTR
      , lineHeight: 1.0
      , maxWidth: 0.0
      , alignX: 0.0
      , alignY: 0.0
      , tabWidth: 4
      , config
      }
    
    effects = KernelTextMask $ TextMaskKernel
      { effects: 
          [ EffectOutline
              { width: 2.0
              , colorR: 0.0
              , colorG: 0.0
              , colorB: 0.0
              , colorA: 0.8
              }
          ]
      , config
      }
  in
    KernelTextSequence [layout, effects]
