-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // brush // dualbrush // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dual Brush Configuration — Complete dual brush system configuration.
-- |
-- | ## Design Philosophy
-- |
-- | DualBrushConfig captures the full specification for combining two brush
-- | tips. The primary tip defines the overall stroke, while the secondary
-- | tip modulates it to create complex textures and effects.
-- |
-- | ## Use Cases
-- |
-- | - **Textured brushes**: Speckle pattern over soft round
-- | - **Vegetation**: Grass tips scattered along stroke
-- | - **Rough edges**: Noise pattern subtracting from clean shapes
-- | - **Complex marks**: Multiple tip shapes interacting
-- |
-- | ## Configuration Fields
-- |
-- | - **enabled**: Whether dual brush is active
-- | - **mode**: How tips combine (multiply, subtract, etc.)
-- | - **secondaryTip**: Reference to secondary tip shape
-- | - **size**: Secondary size relative to primary
-- | - **spacing**: Distance between secondary dabs
-- | - **scatter**: Perpendicular displacement
-- | - **scatterBothAxes**: Also scatter along stroke direction
-- | - **count**: Secondary dabs per primary
-- | - **usePrimaryColor**: Use primary's color vs independent
-- | - **flipX/flipY**: Mirror secondary tip
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - DualBrush.Types
-- | - DualBrush.Atoms
-- | - Tip.Types (for TipShape)

module Hydrogen.Schema.Brush.DualBrush.Config
  ( -- * DualBrushConfig Record
    DualBrushConfig
  , dualBrushConfig
  , defaultDualBrushConfig
  
  -- * Config Field Accessors
  , isDualBrushEnabled
  , getDualBrushMode
  , getSecondarySize
  , getSecondarySpacing
  , getSecondaryScatter
  , getSecondaryCount
  , isScatterBothAxes
  , usesPrimaryColor
  , isSecondaryFlippedX
  , isSecondaryFlippedY
  
  -- * Config Modifiers
  , enableDualBrush
  , disableDualBrush
  , setDualBrushMode
  , setSecondarySize
  , setSecondaryScatter
  , toggleScatterBothAxes
  , toggleFlipX
  , toggleFlipY
  
  -- * Presets
  , noDualBrush
  , texturedBrushConfig
  , foliageBrushConfig
  , roughEdgeBrushConfig
  , splatterBrushConfig
  , hatchtextureBrushConfig
  
  -- * Config Analysis
  , willDualBrushBeVisible
  , hasDualBrushScatter
  , dualBrushConfigDebugInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (&&)
  , (||)
  , not
  )

import Hydrogen.Schema.Brush.DualBrush.Types
  ( DualBrushMode
      ( DualMultiply
      , DualSubtract
      , DualIntersect
      )
  , dualBrushModeToId
  )

import Hydrogen.Schema.Brush.DualBrush.Atoms
  ( SecondarySize(SecondarySize)
  , SecondarySpacing(SecondarySpacing)
  , SecondaryScatter(SecondaryScatter)
  , SecondaryCount(SecondaryCount)
  , secondarySize
  , secondarySpacing
  , secondaryScatter
  , secondaryCount
  , unwrapSecondaryScatter
  , defaultSecondarySize
  , defaultSecondarySpacing
  , noSecondaryScatter
  , subtleSecondaryScatter
  , moderateSecondaryScatter
  , heavySecondaryScatter
  , singleSecondaryCount
  , multipleSecondaryCount
  , hasSecondaryScatter
  )

import Hydrogen.Schema.Brush.Tip.Types
  ( TipShape(TipRound, TipScatter)
  , tipShapeToId
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // dual brush config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete configuration for dual brush behavior.
-- |
-- | ## Field Descriptions
-- |
-- | - `enabled`: Whether dual brush is active
-- | - `mode`: How the two tips combine
-- | - `secondaryTip`: Shape of the secondary tip
-- | - `size`: Secondary size as % of primary
-- | - `spacing`: Distance between secondary dabs
-- | - `scatter`: Perpendicular displacement
-- | - `scatterBothAxes`: Scatter along stroke too
-- | - `count`: Secondary dabs per primary dab
-- | - `usePrimaryColor`: True=primary's color, False=independent
-- | - `flipX`: Horizontal mirror
-- | - `flipY`: Vertical mirror
type DualBrushConfig =
  { enabled :: Boolean              -- Dual brush active
  , mode :: DualBrushMode           -- How tips combine
  , secondaryTip :: TipShape        -- Secondary tip shape
  , size :: SecondarySize           -- Relative size
  , spacing :: SecondarySpacing     -- Dab distance
  , scatter :: SecondaryScatter     -- Perpendicular offset
  , scatterBothAxes :: Boolean      -- Also scatter along stroke
  , count :: SecondaryCount         -- Dabs per primary
  , usePrimaryColor :: Boolean      -- Use primary's color
  , flipX :: Boolean                -- Horizontal mirror
  , flipY :: Boolean                -- Vertical mirror
  }

-- | Create a dual brush config with explicit values.
dualBrushConfig
  :: Boolean
  -> DualBrushMode
  -> TipShape
  -> Number           -- size
  -> Number           -- spacing
  -> Number           -- scatter
  -> Boolean          -- scatterBothAxes
  -> Int              -- count
  -> Boolean          -- usePrimaryColor
  -> Boolean          -- flipX
  -> Boolean          -- flipY
  -> DualBrushConfig
dualBrushConfig en md tip sz sp sc scBoth cnt usePC fX fY =
  { enabled: en
  , mode: md
  , secondaryTip: tip
  , size: secondarySize sz
  , spacing: secondarySpacing sp
  , scatter: secondaryScatter sc
  , scatterBothAxes: scBoth
  , count: secondaryCount cnt
  , usePrimaryColor: usePC
  , flipX: fX
  , flipY: fY
  }

-- | Default dual brush config (disabled, ready with round secondary).
defaultDualBrushConfig :: DualBrushConfig
defaultDualBrushConfig =
  { enabled: false
  , mode: DualMultiply
  , secondaryTip: TipRound
  , size: defaultSecondarySize
  , spacing: defaultSecondarySpacing
  , scatter: noSecondaryScatter
  , scatterBothAxes: false
  , count: singleSecondaryCount
  , usePrimaryColor: true
  , flipX: false
  , flipY: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // field accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if dual brush is enabled.
isDualBrushEnabled :: DualBrushConfig -> Boolean
isDualBrushEnabled cfg = cfg.enabled

-- | Get the dual brush mode.
getDualBrushMode :: DualBrushConfig -> DualBrushMode
getDualBrushMode cfg = cfg.mode

-- | Get the secondary size.
getSecondarySize :: DualBrushConfig -> SecondarySize
getSecondarySize cfg = cfg.size

-- | Get the secondary spacing.
getSecondarySpacing :: DualBrushConfig -> SecondarySpacing
getSecondarySpacing cfg = cfg.spacing

-- | Get the secondary scatter.
getSecondaryScatter :: DualBrushConfig -> SecondaryScatter
getSecondaryScatter cfg = cfg.scatter

-- | Get the secondary count.
getSecondaryCount :: DualBrushConfig -> SecondaryCount
getSecondaryCount cfg = cfg.count

-- | Check if scatter applies to both axes.
isScatterBothAxes :: DualBrushConfig -> Boolean
isScatterBothAxes cfg = cfg.scatterBothAxes

-- | Check if primary color is used.
usesPrimaryColor :: DualBrushConfig -> Boolean
usesPrimaryColor cfg = cfg.usePrimaryColor

-- | Check if secondary is flipped horizontally.
isSecondaryFlippedX :: DualBrushConfig -> Boolean
isSecondaryFlippedX cfg = cfg.flipX

-- | Check if secondary is flipped vertically.
isSecondaryFlippedY :: DualBrushConfig -> Boolean
isSecondaryFlippedY cfg = cfg.flipY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // config modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable dual brush.
enableDualBrush :: DualBrushConfig -> DualBrushConfig
enableDualBrush cfg = cfg { enabled = true }

-- | Disable dual brush.
disableDualBrush :: DualBrushConfig -> DualBrushConfig
disableDualBrush cfg = cfg { enabled = false }

-- | Set the dual brush mode.
setDualBrushMode :: DualBrushMode -> DualBrushConfig -> DualBrushConfig
setDualBrushMode md cfg = cfg { mode = md }

-- | Set the secondary size.
setSecondarySize :: Number -> DualBrushConfig -> DualBrushConfig
setSecondarySize n cfg = cfg { size = secondarySize n }

-- | Set the secondary scatter.
setSecondaryScatter :: Number -> DualBrushConfig -> DualBrushConfig
setSecondaryScatter n cfg = cfg { scatter = secondaryScatter n }

-- | Toggle scatter both axes.
toggleScatterBothAxes :: DualBrushConfig -> DualBrushConfig
toggleScatterBothAxes cfg = cfg { scatterBothAxes = not cfg.scatterBothAxes }

-- | Toggle horizontal flip.
toggleFlipX :: DualBrushConfig -> DualBrushConfig
toggleFlipX cfg = cfg { flipX = not cfg.flipX }

-- | Toggle vertical flip.
toggleFlipY :: DualBrushConfig -> DualBrushConfig
toggleFlipY cfg = cfg { flipY = not cfg.flipY }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | No dual brush (disabled).
noDualBrush :: DualBrushConfig
noDualBrush = defaultDualBrushConfig

-- | Textured brush: speckle secondary with multiply.
-- | Creates texture within stroke like natural media.
texturedBrushConfig :: DualBrushConfig
texturedBrushConfig =
  { enabled: true
  , mode: DualMultiply
  , secondaryTip: TipScatter
  , size: SecondarySize 50.0
  , spacing: SecondarySpacing 25.0
  , scatter: subtleSecondaryScatter
  , scatterBothAxes: false
  , count: singleSecondaryCount
  , usePrimaryColor: true
  , flipX: false
  , flipY: false
  }

-- | Foliage brush: grass-like tips with high scatter.
-- | For vegetation, leaves, and organic scattering.
foliageBrushConfig :: DualBrushConfig
foliageBrushConfig =
  { enabled: true
  , mode: DualIntersect
  , secondaryTip: TipScatter
  , size: SecondarySize 30.0
  , spacing: SecondarySpacing 50.0
  , scatter: heavySecondaryScatter
  , scatterBothAxes: true
  , count: multipleSecondaryCount
  , usePrimaryColor: true
  , flipX: false
  , flipY: false
  }

-- | Rough edge brush: noise subtracting from primary.
-- | Creates irregular, rough stroke edges.
roughEdgeBrushConfig :: DualBrushConfig
roughEdgeBrushConfig =
  { enabled: true
  , mode: DualSubtract
  , secondaryTip: TipScatter
  , size: SecondarySize 80.0
  , spacing: SecondarySpacing 10.0
  , scatter: subtleSecondaryScatter
  , scatterBothAxes: false
  , count: singleSecondaryCount
  , usePrimaryColor: true
  , flipX: false
  , flipY: false
  }

-- | Splatter brush: scattered secondary for spray effects.
-- | Simulates paint splatter and spray.
splatterBrushConfig :: DualBrushConfig
splatterBrushConfig =
  { enabled: true
  , mode: DualMultiply
  , secondaryTip: TipRound
  , size: SecondarySize 20.0
  , spacing: SecondarySpacing 100.0
  , scatter: moderateSecondaryScatter
  , scatterBothAxes: true
  , count: SecondaryCount 8
  , usePrimaryColor: true
  , flipX: false
  , flipY: false
  }

-- | Hatch texture brush: crosshatch pattern overlay.
-- | Creates hatched shading effect.
hatchtextureBrushConfig :: DualBrushConfig
hatchtextureBrushConfig =
  { enabled: true
  , mode: DualMultiply
  , secondaryTip: TipScatter
  , size: SecondarySize 100.0
  , spacing: SecondarySpacing 15.0
  , scatter: noSecondaryScatter
  , scatterBothAxes: false
  , count: singleSecondaryCount
  , usePrimaryColor: true
  , flipX: false
  , flipY: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // config analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if dual brush will have a visible effect.
willDualBrushBeVisible :: DualBrushConfig -> Boolean
willDualBrushBeVisible cfg = cfg.enabled

-- | Check if dual brush has scatter enabled.
hasDualBrushScatter :: DualBrushConfig -> Boolean
hasDualBrushScatter cfg = 
  cfg.enabled && (hasSecondaryScatter cfg.scatter || cfg.scatterBothAxes)

-- | Generate debug info for dual brush config.
dualBrushConfigDebugInfo :: DualBrushConfig -> String
dualBrushConfigDebugInfo cfg =
  "DualBrushConfig: " <>
  (if cfg.enabled then "enabled" else "disabled") <>
  ", mode=" <> dualBrushModeToId cfg.mode <>
  ", tip=" <> tipShapeToId cfg.secondaryTip <>
  ", size=" <> show cfg.size <>
  ", spacing=" <> show cfg.spacing <>
  ", scatter=" <> show (unwrapSecondaryScatter cfg.scatter) <> "%" <>
  (if cfg.scatterBothAxes then ", scatter-both-axes" else "") <>
  ", count=" <> show cfg.count <>
  (if cfg.usePrimaryColor then "" else ", independent-color") <>
  (if cfg.flipX then ", flipX" else "") <>
  (if cfg.flipY then ", flipY" else "")
