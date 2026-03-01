-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // graph // layout // spacing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layout Spacing — Spacing configuration between nodes.
-- |
-- | ## Contents
-- |
-- | - LayoutSpacing: Record type for spacing configuration
-- | - Presets: default, compact, spacious spacing
-- | - Accessors and modifiers for spacing values
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Number)

module Hydrogen.Schema.Graph.Layout.Spacing
  ( -- * Spacing Configuration
    LayoutSpacing
  , layoutSpacing
  , defaultSpacing
  , compactSpacing
  , spaciousSpacing
  
  -- * Accessors
  , siblingGap
  , levelGap
  , subtreeGap
  , padding
  
  -- * Modifiers
  , withSiblingGap
  , withLevelGap
  , withSubtreeGap
  , withPadding
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- No imports needed - Number is built-in

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // layout spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spacing between nodes at various levels
type LayoutSpacing =
  { siblingGap :: Number   -- ^ Gap between siblings (same parent)
  , levelGap :: Number     -- ^ Gap between hierarchy levels
  , subtreeGap :: Number   -- ^ Gap between subtrees
  , padding :: Number      -- ^ Padding around entire tree
  }

-- | Create layout spacing
layoutSpacing :: Number -> Number -> Number -> Number -> LayoutSpacing
layoutSpacing sib lvl sub pad =
  { siblingGap: sib
  , levelGap: lvl
  , subtreeGap: sub
  , padding: pad
  }

-- | Default spacing (balanced)
defaultSpacing :: LayoutSpacing
defaultSpacing = layoutSpacing 16.0 24.0 32.0 16.0

-- | Compact spacing (minimal gaps)
compactSpacing :: LayoutSpacing
compactSpacing = layoutSpacing 4.0 8.0 12.0 8.0

-- | Spacious spacing (generous gaps)
spaciousSpacing :: LayoutSpacing
spaciousSpacing = layoutSpacing 24.0 40.0 56.0 32.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get sibling gap
siblingGap :: LayoutSpacing -> Number
siblingGap s = s.siblingGap

-- | Get level gap
levelGap :: LayoutSpacing -> Number
levelGap s = s.levelGap

-- | Get subtree gap
subtreeGap :: LayoutSpacing -> Number
subtreeGap s = s.subtreeGap

-- | Get padding
padding :: LayoutSpacing -> Number
padding s = s.padding

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Modify sibling gap
withSiblingGap :: Number -> LayoutSpacing -> LayoutSpacing
withSiblingGap gap s = s { siblingGap = gap }

-- | Modify level gap
withLevelGap :: Number -> LayoutSpacing -> LayoutSpacing
withLevelGap gap s = s { levelGap = gap }

-- | Modify subtree gap
withSubtreeGap :: Number -> LayoutSpacing -> LayoutSpacing
withSubtreeGap gap s = s { subtreeGap = gap }

-- | Modify padding
withPadding :: Number -> LayoutSpacing -> LayoutSpacing
withPadding pad s = s { padding = pad }
