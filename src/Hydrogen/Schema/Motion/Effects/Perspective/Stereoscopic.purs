-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--          // hydrogen // schema // motion // effects // perspective // stereoscopic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stereoscopic 3D Effects — functions for 3D Glasses effect.
-- |
-- | Implements motion graphics 3D Glasses effect for stereoscopic
-- | view generation with bounded properties.

module Hydrogen.Schema.Motion.Effects.Perspective.Stereoscopic
  ( -- * Constructors
    default3DGlasses
  , glasses3DWithDepth
  
  -- * Effect Name
  , glasses3DEffectName
  
  -- * Descriptions
  , describe3DGlasses
  
  -- * Queries
  , is3DGlassesAnaglyph
  
  -- * Serialization
  , glasses3DViewToString
  , convergenceModeToString
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  , negate
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Effects.Perspective.Types
  ( ConvergenceMode
    ( CMOffset
    )
  , Glasses3DEffect
  , Glasses3DView
    ( G3DAnaglyph
    , G3DRedCyan
    , G3DGreenMagenta
    , G3DYellowBlue
    , G3DBalanced
    )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default 3D glasses.
default3DGlasses :: Glasses3DEffect
default3DGlasses =
  { leftViewLayer: 0
  , rightViewLayer: 0
  , viewMode: G3DAnaglyph
  , convergence: 0.0
  , convergenceMode: CMOffset
  , balance: 0.0
  , swapLeftRight: false
  }

-- | Create 3D glasses with specific depth.
glasses3DWithDepth :: Int -> Int -> Number -> Glasses3DEffect
glasses3DWithDepth leftIdx rightIdx conv =
  { leftViewLayer: leftIdx
  , rightViewLayer: rightIdx
  , viewMode: G3DAnaglyph
  , convergence: clampNumber (negate 100.0) 100.0 conv
  , convergenceMode: CMOffset
  , balance: 0.0
  , swapLeftRight: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // effect // name
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for 3D Glasses.
glasses3DEffectName :: Glasses3DEffect -> String
glasses3DEffectName _ = "3D Glasses"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Describe 3D glasses effect.
describe3DGlasses :: Glasses3DEffect -> String
describe3DGlasses e =
  "3DGlasses(" <> show e.viewMode <> ", convergence: " <> show e.convergence <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if 3D glasses uses anaglyph mode.
is3DGlassesAnaglyph :: Glasses3DEffect -> Boolean
is3DGlassesAnaglyph e = case e.viewMode of
  G3DAnaglyph -> true
  G3DRedCyan -> true
  G3DGreenMagenta -> true
  G3DYellowBlue -> true
  G3DBalanced -> true
  _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Glasses3DView to string.
glasses3DViewToString :: Glasses3DView -> String
glasses3DViewToString v = show (v :: Glasses3DView)

-- | Convert ConvergenceMode to string.
convergenceModeToString :: ConvergenceMode -> String
convergenceModeToString m = show (m :: ConvergenceMode)
