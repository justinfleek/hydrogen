-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--        // hydrogen // schema // motion // effects // distortion // displacement
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Displacement Effects — Displacement Map and Turbulent Displace effects.
-- |
-- | ## Effects Included
-- |
-- | - **Displacement Map**: Displace pixels using map image
-- | - **Turbulent Displace**: Fractal-based displacement

module Hydrogen.Schema.Motion.Effects.Distortion.Displacement
  ( -- * Displacement Map Effect
    DisplacementMapEffect
  , defaultDisplacementMap
  , displacementMapWithLayer
  
  -- * Turbulent Displace Effect
  , TurbulentDisplaceEffect
  , TurbulentDisplaceType(..)
  , defaultTurbulentDisplace
  , turbulentDisplaceWithAmount
  
  -- * Serialization
  , turbulentDisplaceTypeToString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Motion.Effects.Distortion.Types 
  ( DisplacementMapType(DMTLayer)
  , DisplacementChannel(DCRed, DCGreen)
  , EdgeBehavior(EBOff)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // displacement // map
-- ═════════════════════════════════════════════════════════════════════════════

-- | Displacement Map Effect — Displace pixels using map image.
-- |
-- | ## AE Properties
-- |
-- | - Displacement Map Layer: Source layer for map
-- | - Use For Horizontal Displacement: Channel for X displacement
-- | - Use For Vertical Displacement: Channel for Y displacement
-- | - Max Horizontal Displacement: Max X offset (0-1000 pixels)
-- | - Max Vertical Displacement: Max Y offset (0-1000 pixels)
-- | - Displacement Map Behavior: Edge behavior
-- | - Edge Behavior: How to handle edges
type DisplacementMapEffect =
  { mapLayer :: Int                              -- ^ Source layer index
  , mapType :: DisplacementMapType               -- ^ Map source type
  , horizontalChannel :: DisplacementChannel     -- ^ Channel for X
  , verticalChannel :: DisplacementChannel       -- ^ Channel for Y
  , maxHorizontalDisplacement :: Number          -- ^ Max X offset (0-1000)
  , maxVerticalDisplacement :: Number            -- ^ Max Y offset (0-1000)
  , edgeBehavior :: EdgeBehavior                 -- ^ Edge handling
  , expandOutput :: Boolean                      -- ^ Expand canvas
  }

-- | Default displacement map.
defaultDisplacementMap :: DisplacementMapEffect
defaultDisplacementMap =
  { mapLayer: 1
  , mapType: DMTLayer
  , horizontalChannel: DCRed
  , verticalChannel: DCGreen
  , maxHorizontalDisplacement: 0.0
  , maxVerticalDisplacement: 0.0
  , edgeBehavior: EBOff
  , expandOutput: false
  }

-- | Create displacement map with specific layer.
displacementMapWithLayer :: Int -> Number -> Number -> DisplacementMapEffect
displacementMapWithLayer layer hDisp vDisp =
  { mapLayer: layer
  , mapType: DMTLayer
  , horizontalChannel: DCRed
  , verticalChannel: DCGreen
  , maxHorizontalDisplacement: clampNumber 0.0 1000.0 hDisp
  , maxVerticalDisplacement: clampNumber 0.0 1000.0 vDisp
  , edgeBehavior: EBOff
  , expandOutput: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // turbulent // displace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Turbulent displace type.
data TurbulentDisplaceType
  = TDTTurbulentSmooth     -- ^ Smooth turbulent
  | TDTTurbulentSharp      -- ^ Sharp turbulent
  | TDTBulgeSmooth         -- ^ Smooth bulge
  | TDTBulgeSharp          -- ^ Sharp bulge
  | TDTTwist               -- ^ Twisting

derive instance eqTurbulentDisplaceType :: Eq TurbulentDisplaceType
derive instance ordTurbulentDisplaceType :: Ord TurbulentDisplaceType

instance showTurbulentDisplaceType :: Show TurbulentDisplaceType where
  show TDTTurbulentSmooth = "turbulent-smooth"
  show TDTTurbulentSharp = "turbulent-sharp"
  show TDTBulgeSmooth = "bulge-smooth"
  show TDTBulgeSharp = "bulge-sharp"
  show TDTTwist = "twist"

-- | Turbulent Displace Effect — Fractal-based displacement.
-- |
-- | ## AE Properties
-- |
-- | - Displacement: Type of displacement
-- | - Amount: Displacement strength (0-1000)
-- | - Size: Scale of turbulence (1-2000)
-- | - Offset: Position offset for animation
-- | - Complexity: Fractal complexity (1-10)
-- | - Evolution: Animation phase (0-360 x n)
type TurbulentDisplaceEffect =
  { displacement :: TurbulentDisplaceType  -- ^ Displacement type
  , amount :: Number                        -- ^ Strength (0-1000)
  , size :: Number                          -- ^ Scale (1-2000)
  , offset :: Point2D                       -- ^ Position offset
  , complexity :: Number                    -- ^ Fractal complexity (1-10)
  , evolution :: Number                     -- ^ Animation phase (degrees)
  , cycleEvolution :: Boolean               -- ^ Loop evolution
  , cycleRevolutions :: Int                 -- ^ Revolutions per cycle
  , randomSeed :: Int                       -- ^ Random seed
  , pinAllEdges :: Boolean                  -- ^ Lock edges
  , antialiasing :: Boolean                 -- ^ Edge smoothing
  }

-- | Default turbulent displace.
defaultTurbulentDisplace :: TurbulentDisplaceEffect
defaultTurbulentDisplace =
  { displacement: TDTTurbulentSmooth
  , amount: 50.0
  , size: 100.0
  , offset: point2D 0.0 0.0
  , complexity: 2.0
  , evolution: 0.0
  , cycleEvolution: false
  , cycleRevolutions: 1
  , randomSeed: 0
  , pinAllEdges: false
  , antialiasing: true
  }

-- | Create turbulent displace with specific amount.
turbulentDisplaceWithAmount :: Number -> Number -> TurbulentDisplaceEffect
turbulentDisplaceWithAmount amt sz =
  { displacement: TDTTurbulentSmooth
  , amount: clampNumber 0.0 1000.0 amt
  , size: clampNumber 1.0 2000.0 sz
  , offset: point2D 0.0 0.0
  , complexity: 2.0
  , evolution: 0.0
  , cycleEvolution: false
  , cycleRevolutions: 1
  , randomSeed: 0
  , pinAllEdges: false
  , antialiasing: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // serialization
-- ═════════════════════════════════════════════════════════════════════════════

turbulentDisplaceTypeToString :: TurbulentDisplaceType -> String
turbulentDisplaceTypeToString = show
