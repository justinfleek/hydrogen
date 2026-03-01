-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // text-animator // selectors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Selector types for text animation.
-- |
-- | ## Architecture
-- |
-- | Selectors determine which characters are affected by animation:
-- | - Range selectors: start/end/offset based selection
-- | - Wiggly selectors: organic procedural movement
-- | - Expression selectors: code-driven selection
-- |
-- | ## Supporting Types
-- |
-- | - CharacterBlur: per-character blur values
-- | - GroupingAlignment: alignment within groups
-- | - EaseSettings: ease in/out for selector falloff

module Hydrogen.Schema.Motion.TextAnimator.Selectors
  ( -- * Character Blur
    CharacterBlur
  , mkCharacterBlur
  
    -- * Grouping Alignment
  , GroupingAlignment
  , mkGroupingAlignment
  
    -- * Ease Settings
  , EaseSettings
  , mkEaseSettings
  , defaultEaseSettings
  
    -- * Text Range Selector
  , TextRangeSelector
  , defaultTextRangeSelector
  
    -- * Text Wiggly Selector
  , TextWigglySelector
  , defaultTextWigglySelector
  
    -- * Text Expression Selector
  , TextExpressionSelector
  , defaultTextExpressionSelector
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Schema.Motion.Property (AnimatablePropertyId)
import Hydrogen.Schema.Motion.TextAnimator.Enumerations
  ( RangeSelectorMode(RSMPercent)
  , SelectionBasedOn(SBOCharacters)
  , SelectionShape(SSSquare)
  , SelectorMode(SMAdd)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // character // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Per-character blur amount.
type CharacterBlur =
  { x :: Number  -- ^ Horizontal blur (non-negative)
  , y :: Number  -- ^ Vertical blur (non-negative)
  }

-- | Create a character blur value.
mkCharacterBlur :: Number -> Number -> CharacterBlur
mkCharacterBlur x y = { x, y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // grouping // alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Alignment within a grouping (percentages 0-100).
type GroupingAlignment =
  { x :: Number  -- ^ X alignment (0-100%)
  , y :: Number  -- ^ Y alignment (0-100%)
  }

-- | Create a grouping alignment.
mkGroupingAlignment :: Number -> Number -> GroupingAlignment
mkGroupingAlignment x y = { x, y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // ease // settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ease high/low settings for range selector.
type EaseSettings =
  { high :: Number  -- ^ High ease percentage (0-100)
  , low :: Number   -- ^ Low ease percentage (0-100)
  }

-- | Create ease settings.
mkEaseSettings :: Number -> Number -> EaseSettings
mkEaseSettings high low = { high, low }

-- | Default ease settings (no easing).
defaultEaseSettings :: EaseSettings
defaultEaseSettings = { high: 0.0, low: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // text // range // selector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Range selector for text animation.
-- |
-- | Defines which characters are affected based on start/end/offset.
type TextRangeSelector =
  { mode :: RangeSelectorMode
  , startPropertyId :: AnimatablePropertyId
  , endPropertyId :: AnimatablePropertyId
  , offsetPropertyId :: AnimatablePropertyId
  , basedOn :: SelectionBasedOn
  , shape :: SelectionShape
  , selectorMode :: Maybe SelectorMode
  , amount :: Number           -- ^ Percentage (0-100)
  , smoothness :: Number       -- ^ Percentage (0-100)
  , randomizeOrder :: Boolean
  , randomSeed :: Int
  , ease :: EaseSettings
  }

-- | Default text range selector.
defaultTextRangeSelector 
  :: AnimatablePropertyId 
  -> AnimatablePropertyId 
  -> AnimatablePropertyId 
  -> TextRangeSelector
defaultTextRangeSelector startId endId offsetId =
  { mode: RSMPercent
  , startPropertyId: startId
  , endPropertyId: endId
  , offsetPropertyId: offsetId
  , basedOn: SBOCharacters
  , shape: SSSquare
  , selectorMode: Nothing
  , amount: 100.0
  , smoothness: 0.0
  , randomizeOrder: false
  , randomSeed: 0
  , ease: defaultEaseSettings
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // text // wiggly // selector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wiggly selector for organic text animation.
type TextWigglySelector =
  { enabled :: Boolean
  , mode :: SelectorMode
  , maxAmount :: Number         -- ^ Maximum percentage
  , minAmount :: Number         -- ^ Minimum percentage
  , wigglesPerSecond :: Number  -- ^ Frequency (non-negative)
  , correlation :: Number       -- ^ How correlated between characters (0-100%)
  , lockDimensions :: Boolean
  , basedOn :: SelectionBasedOn
  , randomSeed :: Int
  }

-- | Default wiggly selector (disabled).
defaultTextWigglySelector :: TextWigglySelector
defaultTextWigglySelector =
  { enabled: false
  , mode: SMAdd
  , maxAmount: 100.0
  , minAmount: 0.0
  , wigglesPerSecond: 2.0
  , correlation: 50.0
  , lockDimensions: false
  , basedOn: SBOCharacters
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // text // expression // selector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expression selector for procedural text animation.
type TextExpressionSelector =
  { enabled :: Boolean
  , mode :: SelectorMode
  , amountExpression :: String   -- ^ Expression code
  , basedOn :: SelectionBasedOn
  }

-- | Default expression selector (disabled).
defaultTextExpressionSelector :: TextExpressionSelector
defaultTextExpressionSelector =
  { enabled: false
  , mode: SMAdd
  , amountExpression: "100"
  , basedOn: SBOCharacters
  }
