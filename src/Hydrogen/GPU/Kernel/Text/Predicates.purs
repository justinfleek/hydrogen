-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // gpu // kernel // text // predicates
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Predicate Utilities for Text Kernels
-- |
-- | Functions for testing conditions on text kernels, effects, glyphs,
-- | and related data structures.

module Hydrogen.GPU.Kernel.Text.Predicates
  ( -- * Maybe Utilities
    hasValue
  , noValue
  , valueOr
  , whenJust
  
  -- * Kernel Search
  , findKernel
  
  -- * Glyph Utilities
  , hasGlyphMatching
  , totalGlyphAdvanceX
  
  -- * Text Run Utilities
  , totalCharCount
  
  -- * Effect Predicates
  , isPlainText
  , isEffectNone
  , findFirstEffect
  
  -- * Subpixel Predicates
  , usesSubpixelRendering
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , ($)
  , (*)
  , (/=)
  , (<<<)
  , not
  )

import Data.Maybe (Maybe(Nothing, Just), fromMaybe, maybe, isJust, isNothing)
import Data.Foldable (sum, any, all, find)
import Data.String as String

import Hydrogen.GPU.Kernel.Text.Types
  ( TextKernel
      ( KernelTextSequence
      , KernelTextNoop
      )
  , GlyphInstance
  , TextRun
  , TextEffect(EffectNone)
  , SubpixelMode(SubpixelNone)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // maybe utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a Maybe value is present
hasValue :: forall a. Maybe a -> Boolean
hasValue = isJust

-- | Check if a Maybe value is absent
noValue :: forall a. Maybe a -> Boolean
noValue = isNothing

-- | Get value or default
valueOr :: forall a. a -> Maybe a -> a
valueOr = fromMaybe

-- | Apply function if value present
whenJust :: forall a b. Maybe a -> (a -> b) -> Maybe b
whenJust m f = maybe Nothing (Just <<< f) m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // kernel search
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find first kernel matching predicate
findKernel :: (TextKernel -> Boolean) -> TextKernel -> Maybe TextKernel
findKernel pred kernel =
  case kernel of
    KernelTextSequence kernels -> find pred kernels
    KernelTextNoop -> Nothing
    other -> if pred other then Just other else Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // glyph utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if any glyph in array matches predicate
hasGlyphMatching :: (GlyphInstance -> Boolean) -> Array GlyphInstance -> Boolean
hasGlyphMatching pred glyphs = any pred glyphs

-- | Sum all glyph X advances (horizontal spacing)
totalGlyphAdvanceX :: Array GlyphInstance -> Number
totalGlyphAdvanceX glyphs = sum (map (\g -> g.x * g.scaleX) glyphs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // text run utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Count total characters across all runs
totalCharCount :: Array TextRun -> Int
totalCharCount runs = sum (map (\r -> String.length r.text) runs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // effect predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if all effects are EffectNone (plain text)
isPlainText :: Array TextEffect -> Boolean
isPlainText effects = all isEffectNone effects

-- | Check if effect is EffectNone
isEffectNone :: TextEffect -> Boolean
isEffectNone EffectNone = true
isEffectNone _ = false

-- | Find first non-none effect
findFirstEffect :: Array TextEffect -> Maybe TextEffect
findFirstEffect effects = find (not <<< isEffectNone) effects

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // subpixel predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a config uses subpixel rendering
usesSubpixelRendering :: SubpixelMode -> Boolean
usesSubpixelRendering mode = mode /= SubpixelNone
