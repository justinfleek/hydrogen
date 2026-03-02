-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // surface // wetness
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Surface Wetness — Water content tracking for wet media simulation.
-- |
-- | ## Design Philosophy
-- |
-- | Wetness affects paint behavior:
-- | - Wet paint flows and blends
-- | - Drying paint becomes viscous
-- | - Dry paint is fixed
-- |
-- | ## Wetness Model
-- |
-- | - **0.0**: Completely dry (paint is fixed)
-- | - **0.5**: Damp (paint is workable but not flowing)
-- | - **1.0**: Fully wet (paint flows freely)
-- |
-- | ## Drying Dynamics
-- |
-- | Paint dries over time at a rate depending on:
-- | - Ambient humidity
-- | - Temperature
-- | - Paint thickness (thicker = slower)
-- | - Paper absorption (higher = faster)
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Array
-- | - Data.Maybe

module Hydrogen.Schema.Surface.Wetness
  ( -- * Wetness Value
    WetnessValue
  , mkWetnessValue
  , wetnessRaw
  , fullyDry
  , fullyWet
  , isDry
  , isWet
  , isDamp
  
  -- * Wetness Map
  , WetnessMap
  , mkWetnessMap
  , wetnessMapWidth
  , wetnessMapHeight
  , getWetnessAt
  , setWetnessAt
  , addWetnessAt
  
  -- * Drying Configuration
  , DryingConfig
  , mkDryingConfig
  , dryingRate
  , ambientHumidity
  , defaultDrying
  , fastDrying
  , slowDrying
  
  -- * Drying Simulation
  , applyDrying
  , dryingTime
  , estimateFullDryTime
  
  -- * Wetness Interactions
  , blendWetness
  , rewet
  , absorbWetness
  
  -- * Analysis
  , averageWetness
  , totalWetArea
  , dryAreaFraction
  , wetAreaFraction
  
  -- * Display
  , displayWetnessValue
  , displayDryingConfig
  
  -- * Comparisons
  , wetnessEqual
  , isWetnessAt
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (&&)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , max
  , min
  , map
  )

import Data.Array (length, index, updateAt, replicate, filter, foldl) as Array
import Data.Maybe (fromMaybe)
import Data.Int (toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // wetness value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wetness level as a normalized value.
-- |
-- | 0.0 = fully dry, 1.0 = fully wet.
newtype WetnessValue = WetnessValue Number

derive instance eqWetnessValue :: Eq WetnessValue
derive instance ordWetnessValue :: Ord WetnessValue

instance showWetnessValue :: Show WetnessValue where
  show (WetnessValue w) = "Wetness(" <> show w <> ")"

-- | Create a wetness value, clamped to 0-1.
mkWetnessValue :: Number -> WetnessValue
mkWetnessValue w = WetnessValue (max 0.0 (min 1.0 w))

-- | Get raw wetness value.
wetnessRaw :: WetnessValue -> Number
wetnessRaw (WetnessValue w) = w

-- | Fully dry wetness value.
fullyDry :: WetnessValue
fullyDry = WetnessValue 0.0

-- | Fully wet wetness value.
fullyWet :: WetnessValue
fullyWet = WetnessValue 1.0

-- | Check if wetness is considered dry (< 0.05).
isDry :: WetnessValue -> Boolean
isDry (WetnessValue w) = w < 0.05

-- | Check if wetness is considered wet (> 0.5).
isWet :: WetnessValue -> Boolean
isWet (WetnessValue w) = w > 0.5

-- | Check if wetness is in the damp range (0.05-0.5).
isDamp :: WetnessValue -> Boolean
isDamp (WetnessValue w) = w >= 0.05 && w <= 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // wetness map
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D grid of wetness values.
type WetnessMap =
  { width :: Int
  , height :: Int
  , values :: Array WetnessValue
  }

-- | Create a wetness map initialized to dry.
mkWetnessMap :: Int -> Int -> WetnessMap
mkWetnessMap w h =
  let
    safeW = max 1 w
    safeH = max 1 h
    total = safeW * safeH
  in
    { width: safeW
    , height: safeH
    , values: Array.replicate total fullyDry
    }

-- | Get map width.
wetnessMapWidth :: WetnessMap -> Int
wetnessMapWidth m = m.width

-- | Get map height.
wetnessMapHeight :: WetnessMap -> Int
wetnessMapHeight m = m.height

-- | Get wetness at cell coordinates.
getWetnessAt :: WetnessMap -> Int -> Int -> WetnessValue
getWetnessAt m x y =
  if x >= 0 && x < m.width && y >= 0 && y < m.height
    then fromMaybe fullyDry (Array.index m.values (y * m.width + x))
    else fullyDry

-- | Set wetness at cell coordinates.
setWetnessAt :: WetnessMap -> Int -> Int -> WetnessValue -> WetnessMap
setWetnessAt m x y val =
  if x >= 0 && x < m.width && y >= 0 && y < m.height
    then
      let
        idx = y * m.width + x
        newValues = fromMaybe m.values (Array.updateAt idx val m.values)
      in
        m { values = newValues }
    else m

-- | Add to wetness at cell coordinates.
addWetnessAt :: WetnessMap -> Int -> Int -> Number -> WetnessMap
addWetnessAt m x y delta =
  let
    WetnessValue current = getWetnessAt m x y
    newWetness = mkWetnessValue (current + delta)
  in
    setWetnessAt m x y newWetness

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // drying configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for drying simulation.
type DryingConfig =
  { rate :: Number           -- ^ Base drying rate (wetness lost per second)
  , humidity :: Number       -- ^ Ambient humidity 0-1 (higher = slower drying)
  , temperature :: Number    -- ^ Temperature factor (higher = faster drying)
  }

-- | Create drying configuration.
mkDryingConfig :: Number -> Number -> Number -> DryingConfig
mkDryingConfig rate humidity temp =
  { rate: max 0.0 rate
  , humidity: max 0.0 (min 1.0 humidity)
  , temperature: max 0.0 temp
  }

-- | Get effective drying rate.
dryingRate :: DryingConfig -> Number
dryingRate config =
  let
    humidityFactor = 1.0 - config.humidity * 0.9  -- High humidity slows drying
    tempFactor = config.temperature              -- Higher temp speeds drying
  in
    config.rate * humidityFactor * tempFactor

-- | Get ambient humidity.
ambientHumidity :: DryingConfig -> Number
ambientHumidity config = config.humidity

-- | Default drying configuration.
-- |
-- | Moderate drying rate at room temperature, 50% humidity.
defaultDrying :: DryingConfig
defaultDrying = mkDryingConfig 0.05 0.5 1.0

-- | Fast drying configuration.
-- |
-- | Hot, dry environment.
fastDrying :: DryingConfig
fastDrying = mkDryingConfig 0.1 0.2 1.5

-- | Slow drying configuration.
-- |
-- | Cool, humid environment.
slowDrying :: DryingConfig
slowDrying = mkDryingConfig 0.02 0.8 0.7

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // drying simulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply drying to the entire wetness map.
-- |
-- | deltaTime is in seconds.
applyDrying :: WetnessMap -> DryingConfig -> Number -> WetnessMap
applyDrying m config deltaTime =
  let
    effectiveRate = dryingRate config
    dryAmount = effectiveRate * deltaTime
    
    dryCell (WetnessValue w) = mkWetnessValue (w - dryAmount)
    
    newValues = map dryCell m.values
  in
    m { values = newValues }

-- | Calculate time for a wetness value to reach target.
-- |
-- | Returns time in seconds.
dryingTime :: DryingConfig -> WetnessValue -> WetnessValue -> Number
dryingTime config (WetnessValue start) (WetnessValue target) =
  let
    effectiveRate = dryingRate config
    delta = start - target
  in
    if effectiveRate > 0.0 && delta > 0.0
      then delta / effectiveRate
      else 0.0

-- | Estimate time until fully dry.
estimateFullDryTime :: DryingConfig -> WetnessValue -> Number
estimateFullDryTime config wetness = dryingTime config wetness fullyDry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // wetness interactions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two wetness values.
-- |
-- | Factor 0 = first value, factor 1 = second value.
blendWetness :: WetnessValue -> WetnessValue -> Number -> WetnessValue
blendWetness (WetnessValue w1) (WetnessValue w2) factor =
  let
    t = max 0.0 (min 1.0 factor)
    inv = 1.0 - t
  in
    mkWetnessValue (w1 * inv + w2 * t)

-- | Re-wet a dry surface.
-- |
-- | Adds wetness, capped at fully wet.
rewet :: WetnessValue -> Number -> WetnessValue
rewet (WetnessValue current) amount =
  mkWetnessValue (current + max 0.0 amount)

-- | Absorb wetness into paper.
-- |
-- | Absorption rate determines how much wetness is removed.
absorbWetness :: WetnessValue -> Number -> WetnessValue
absorbWetness (WetnessValue current) absorptionRate =
  let
    absorbed = current * max 0.0 (min 1.0 absorptionRate)
  in
    mkWetnessValue (current - absorbed)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get average wetness across the map.
averageWetness :: WetnessMap -> Number
averageWetness m =
  let
    total = Array.foldl (\acc (WetnessValue w) -> acc + w) 0.0 m.values
    count = Int.toNumber (Array.length m.values)
  in
    if count > 0.0 then total / count else 0.0

-- | Get total number of wet cells.
totalWetArea :: WetnessMap -> Int
totalWetArea m = Array.length (Array.filter isWet m.values)

-- | Get fraction of map that is dry.
dryAreaFraction :: WetnessMap -> Number
dryAreaFraction m =
  let
    dryCount = Array.length (Array.filter isDry m.values)
    total = Array.length m.values
  in
    if total > 0
      then Int.toNumber dryCount / Int.toNumber total
      else 1.0

-- | Get fraction of map that is wet.
wetAreaFraction :: WetnessMap -> Number
wetAreaFraction m =
  let
    wetCount = Array.length (Array.filter isWet m.values)
    total = Array.length m.values
  in
    if total > 0
      then Int.toNumber wetCount / Int.toNumber total
      else 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display wetness value.
displayWetnessValue :: WetnessValue -> String
displayWetnessValue w
  | isDry w = "dry"
  | isDamp w = "damp"
  | isWet w = "wet"
  | true = show (wetnessRaw w)

-- | Display drying configuration.
displayDryingConfig :: DryingConfig -> String
displayDryingConfig config =
  "drying rate: " <> show (dryingRate config) <> "/s, humidity: " <> show (config.humidity * 100.0) <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // comparisons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two wetness values are equal.
wetnessEqual :: WetnessValue -> WetnessValue -> Boolean
wetnessEqual (WetnessValue a) (WetnessValue b) = a == b

-- | Check if wetness is at a specific level.
isWetnessAt :: WetnessValue -> Number -> Boolean
isWetnessAt (WetnessValue w) level = w == level
