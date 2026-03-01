-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // brush // dualbrush // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dual Brush Types — ADTs for combining two brush tips.
-- |
-- | ## Design Philosophy
-- |
-- | Dual brush combines two brush tips to create complex textures and effects.
-- | Unlike texture (which applies a continuous pattern), dual brush uses a
-- | secondary brush tip that stamps within or masks the primary brush stroke.
-- |
-- | The secondary tip has its own scatter, size, and spacing, creating effects
-- | like textured brushes, vegetation, splatter, and complex marks that would
-- | be difficult to achieve with a single tip.
-- |
-- | ## Dual Brush Mode
-- |
-- | How the two brush tips combine:
-- |
-- | - **Multiply**: Darkest wins (intersection of both tips)
-- | - **ColorBurn**: Intense intersection, high contrast
-- | - **Subtract**: Secondary cuts into primary
-- | - **Intersect**: Only where both tips exist
-- | - **Overlay**: Complex blending for varied effects
-- |
-- | ## Use Cases
-- |
-- | | Primary    | Secondary | Mode      | Effect             |
-- | |------------|-----------|-----------|-------------------|
-- | | Soft Round | Speckle   | Multiply  | Textured brush    |
-- | | Hard Round | Grass     | Intersect | Detailed vegetation|
-- | | Flat       | Noise     | Subtract  | Rough edges       |
-- | | Airbrush   | Splatter  | Multiply  | Spray texture     |
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Brush.DualBrush.Types
  ( -- * DualBrushMode ADT
    DualBrushMode
      ( DualMultiply
      , DualColorBurn
      , DualSubtract
      , DualIntersect
      , DualOverlay
      )
  , allDualBrushModes
  , dualBrushModeDescription
  , isSubtractiveDualMode
  , isDarkeningDualMode
  
  -- * Debug & Serialization Helpers
  , dualBrushModeDebugInfo
  , dualBrushModeToId
  , sameDualBrushModeKind
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
--                                                            // dual brush mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How two brush tips combine to create the final mark.
-- |
-- | The primary tip defines the overall stroke shape, while the secondary
-- | tip modulates it according to the selected blend mode.
data DualBrushMode
  = DualMultiply    -- ^ Darkest wins, creates intersection effect
  | DualColorBurn   -- ^ Intense intersection with high contrast
  | DualSubtract    -- ^ Secondary cuts into primary tip
  | DualIntersect   -- ^ Only where both tips have opacity
  | DualOverlay     -- ^ Complex blending for varied effects

derive instance eqDualBrushMode :: Eq DualBrushMode
derive instance ordDualBrushMode :: Ord DualBrushMode

instance showDualBrushMode :: Show DualBrushMode where
  show DualMultiply = "(DualBrushMode Multiply)"
  show DualColorBurn = "(DualBrushMode ColorBurn)"
  show DualSubtract = "(DualBrushMode Subtract)"
  show DualIntersect = "(DualBrushMode Intersect)"
  show DualOverlay = "(DualBrushMode Overlay)"

-- | All dual brush mode variants for enumeration.
allDualBrushModes :: Array DualBrushMode
allDualBrushModes =
  [ DualMultiply
  , DualColorBurn
  , DualSubtract
  , DualIntersect
  , DualOverlay
  ]

-- | Human-readable description of each dual brush mode.
dualBrushModeDescription :: DualBrushMode -> String
dualBrushModeDescription DualMultiply =
  "Darkest wins, secondary texture shows where primary exists"
dualBrushModeDescription DualColorBurn =
  "Intense intersection, high contrast textured effect"
dualBrushModeDescription DualSubtract =
  "Secondary cuts into primary, creating gaps and holes"
dualBrushModeDescription DualIntersect =
  "Only where both tips overlap, creates masked effect"
dualBrushModeDescription DualOverlay =
  "Complex blending, varied light and dark effects"

-- | Check if mode is subtractive (removes from primary).
isSubtractiveDualMode :: DualBrushMode -> Boolean
isSubtractiveDualMode DualSubtract = true
isSubtractiveDualMode _ = false

-- | Check if mode darkens the result.
isDarkeningDualMode :: DualBrushMode -> Boolean
isDarkeningDualMode DualMultiply = true
isDarkeningDualMode DualColorBurn = true
isDarkeningDualMode _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // debug helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info for dual brush mode.
dualBrushModeDebugInfo :: DualBrushMode -> String
dualBrushModeDebugInfo mode =
  "DualBrushMode: " <> dualBrushModeToId mode <> " — " <> dualBrushModeDescription mode

-- | Convert dual brush mode to string ID for serialization.
dualBrushModeToId :: DualBrushMode -> String
dualBrushModeToId DualMultiply = "multiply"
dualBrushModeToId DualColorBurn = "color-burn"
dualBrushModeToId DualSubtract = "subtract"
dualBrushModeToId DualIntersect = "intersect"
dualBrushModeToId DualOverlay = "overlay"

-- | Check if two dual brush modes are the same kind.
sameDualBrushModeKind :: DualBrushMode -> DualBrushMode -> Boolean
sameDualBrushModeKind a b = dualBrushModeToId a == dualBrushModeToId b
