-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // shapes // modifiers // advanced
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Advanced stroke properties with taper and wave.
-- |
-- | Extends StrokeProps with AE CC 2020+ features.
-- | All values are bounded and composable.

module Hydrogen.Schema.Motion.Shapes.Modifiers.Advanced
  ( -- * Advanced Stroke
    AdvancedStrokeProps
  , advancedStrokeProps
  , defaultAdvancedStroke
  , strokeWithTaper
  , strokeWithWave
  , strokeWithTaperAndWave
  , hasTaper
  , hasWave
  , hasAdvancedFeatures
  ) where

import Prelude
  ( (||)
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Motion.Shapes 
  ( LineCap(LCButt, LCRound)
  , LineJoin(LJMiter, LJRound)
  )
import Hydrogen.Schema.Motion.Shapes.Operators 
  ( Percent
  , percent
  , PositiveNumber
  , positiveNumber
  )
import Hydrogen.Schema.Motion.Shapes.Modifiers.Stroke (DashPattern, solidDash)
import Hydrogen.Schema.Motion.Shapes.Modifiers.Taper (StrokeTaper, noTaper)
import Hydrogen.Schema.Motion.Shapes.Modifiers.Wave (StrokeWave, noWave)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // advanced // stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Advanced stroke properties with taper and wave.
-- |
-- | Extends StrokeProps with AE CC 2020+ features.
type AdvancedStrokeProps =
  { color :: RGB             -- ^ Stroke color
  , opacity :: Percent       -- ^ Stroke opacity (0-100%)
  , width :: PositiveNumber  -- ^ Stroke width (pixels)
  , lineCap :: LineCap       -- ^ Endpoint style
  , lineJoin :: LineJoin     -- ^ Corner style
  , miterLimit :: Number     -- ^ Miter join limit
  , dashPattern :: DashPattern  -- ^ Dash pattern (empty = solid)
  , taper :: StrokeTaper     -- ^ Taper settings
  , wave :: StrokeWave       -- ^ Wave settings
  }

-- | Create AdvancedStrokeProps.
advancedStrokeProps
  :: RGB
  -> Number      -- ^ Opacity (%)
  -> Number      -- ^ Width
  -> LineCap
  -> LineJoin
  -> Number      -- ^ Miter limit
  -> DashPattern
  -> StrokeTaper
  -> StrokeWave
  -> AdvancedStrokeProps
advancedStrokeProps c o w cap join miter dash taper' wave' =
  { color: c
  , opacity: percent o
  , width: positiveNumber w
  , lineCap: cap
  , lineJoin: join
  , miterLimit: clampNumber 1.0 100.0 miter
  , dashPattern: dash
  , taper: taper'
  , wave: wave'
  }

-- | Default advanced stroke: no taper, no wave.
defaultAdvancedStroke :: AdvancedStrokeProps
defaultAdvancedStroke =
  { color: rgb 0 0 0
  , opacity: percent 100.0
  , width: positiveNumber 1.0
  , lineCap: LCButt
  , lineJoin: LJMiter
  , miterLimit: 4.0
  , dashPattern: solidDash
  , taper: noTaper
  , wave: noWave
  }

-- | Create advanced stroke with taper only.
strokeWithTaper :: RGB -> Number -> StrokeTaper -> AdvancedStrokeProps
strokeWithTaper c w taper' =
  { color: c
  , opacity: percent 100.0
  , width: positiveNumber w
  , lineCap: LCRound
  , lineJoin: LJRound
  , miterLimit: 4.0
  , dashPattern: solidDash
  , taper: taper'
  , wave: noWave
  }

-- | Create advanced stroke with wave only.
strokeWithWave :: RGB -> Number -> StrokeWave -> AdvancedStrokeProps
strokeWithWave c w wave' =
  { color: c
  , opacity: percent 100.0
  , width: positiveNumber w
  , lineCap: LCRound
  , lineJoin: LJRound
  , miterLimit: 4.0
  , dashPattern: solidDash
  , taper: noTaper
  , wave: wave'
  }

-- | Create advanced stroke with both taper and wave.
strokeWithTaperAndWave :: RGB -> Number -> StrokeTaper -> StrokeWave -> AdvancedStrokeProps
strokeWithTaperAndWave c w taper' wave' =
  { color: c
  , opacity: percent 100.0
  , width: positiveNumber w
  , lineCap: LCRound
  , lineJoin: LJRound
  , miterLimit: 4.0
  , dashPattern: solidDash
  , taper: taper'
  , wave: wave'
  }

-- | Check if stroke has taper.
hasTaper :: AdvancedStrokeProps -> Boolean
hasTaper s = s.taper.enabled

-- | Check if stroke has wave.
hasWave :: AdvancedStrokeProps -> Boolean
hasWave s = s.wave.enabled

-- | Check if stroke has any advanced features.
hasAdvancedFeatures :: AdvancedStrokeProps -> Boolean
hasAdvancedFeatures s = s.taper.enabled || s.wave.enabled
