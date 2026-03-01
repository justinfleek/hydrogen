-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // weather // wind // direction
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Wind direction primitives and cardinal compass points.
-- |
-- | ## Convention
-- |
-- | Direction wind is coming FROM (meteorological convention):
-- | - 0/360 = North (wind from north)
-- | - 90 = East (wind from east)
-- | - 180 = South (wind from south)
-- | - 270 = West (wind from west)
-- |
-- | This matches weather reports: "westerly wind" = wind from west = 270°.

module Hydrogen.Schema.Weather.Wind.Direction
  ( -- * Wind Direction
    WindDirection
  , windDirection
  , windDirectionUnsafe
  , unwrapDirection
  , directionBounds
  , degrees
  , radians
  
  -- * Cardinal Constants
  , directionNorth
  , directionNorthEast
  , directionEast
  , directionSouthEast
  , directionSouth
  , directionSouthWest
  , directionWest
  , directionNorthWest
  
  -- * Cardinal Enum
  , Cardinal(..)
  , allCardinals
  , cardinalToDegrees
  , degreesToCardinal
  , cardinalAbbreviation
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (*)
  , (/)
  , (<)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // wind // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wind direction in degrees [0, 360), wrapping.
newtype WindDirection = WindDirection Number

derive instance eqWindDirection :: Eq WindDirection
derive instance ordWindDirection :: Ord WindDirection

instance showWindDirection :: Show WindDirection where
  show (WindDirection n) = "WindDirection " <> show n <> "°"

-- | Safe constructor with wrapping.
windDirection :: Number -> WindDirection
windDirection n = WindDirection (Bounded.wrapNumber 0.0 360.0 n)

-- | Unsafe constructor for known-valid values.
windDirectionUnsafe :: Number -> WindDirection
windDirectionUnsafe = WindDirection

-- | Extract raw value.
unwrapDirection :: WindDirection -> Number
unwrapDirection (WindDirection n) = n

-- | Valid bounds documentation.
directionBounds :: Bounded.NumberBounds
directionBounds = Bounded.numberBounds 0.0 360.0 Bounded.Wraps "windDirection" "Wind direction in degrees"

-- | Get direction in degrees (identity).
degrees :: WindDirection -> Number
degrees = unwrapDirection

-- | Convert to radians.
radians :: WindDirection -> Number
radians (WindDirection n) = n * 3.14159265358979323846 / 180.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // cardinal // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | North (0°).
directionNorth :: WindDirection
directionNorth = WindDirection 0.0

-- | North-East (45°).
directionNorthEast :: WindDirection
directionNorthEast = WindDirection 45.0

-- | East (90°).
directionEast :: WindDirection
directionEast = WindDirection 90.0

-- | South-East (135°).
directionSouthEast :: WindDirection
directionSouthEast = WindDirection 135.0

-- | South (180°).
directionSouth :: WindDirection
directionSouth = WindDirection 180.0

-- | South-West (225°).
directionSouthWest :: WindDirection
directionSouthWest = WindDirection 225.0

-- | West (270°).
directionWest :: WindDirection
directionWest = WindDirection 270.0

-- | North-West (315°).
directionNorthWest :: WindDirection
directionNorthWest = WindDirection 315.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // cardinal // enum
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cardinal and intercardinal directions (16-point compass).
data Cardinal
  = N   -- ^ North (0°)
  | NNE -- ^ North-North-East (22.5°)
  | NE  -- ^ North-East (45°)
  | ENE -- ^ East-North-East (67.5°)
  | E   -- ^ East (90°)
  | ESE -- ^ East-South-East (112.5°)
  | SE  -- ^ South-East (135°)
  | SSE -- ^ South-South-East (157.5°)
  | S   -- ^ South (180°)
  | SSW -- ^ South-South-West (202.5°)
  | SW  -- ^ South-West (225°)
  | WSW -- ^ West-South-West (247.5°)
  | W   -- ^ West (270°)
  | WNW -- ^ West-North-West (292.5°)
  | NW  -- ^ North-West (315°)
  | NNW -- ^ North-North-West (337.5°)

derive instance eqCardinal :: Eq Cardinal
derive instance ordCardinal :: Ord Cardinal

instance showCardinal :: Show Cardinal where
  show N = "N"
  show NNE = "NNE"
  show NE = "NE"
  show ENE = "ENE"
  show E = "E"
  show ESE = "ESE"
  show SE = "SE"
  show SSE = "SSE"
  show S = "S"
  show SSW = "SSW"
  show SW = "SW"
  show WSW = "WSW"
  show W = "W"
  show WNW = "WNW"
  show NW = "NW"
  show NNW = "NNW"

-- | All cardinal directions for enumeration.
allCardinals :: Array Cardinal
allCardinals = [N, NNE, NE, ENE, E, ESE, SE, SSE, S, SSW, SW, WSW, W, WNW, NW, NNW]

-- | Convert cardinal to degrees.
cardinalToDegrees :: Cardinal -> WindDirection
cardinalToDegrees N = WindDirection 0.0
cardinalToDegrees NNE = WindDirection 22.5
cardinalToDegrees NE = WindDirection 45.0
cardinalToDegrees ENE = WindDirection 67.5
cardinalToDegrees E = WindDirection 90.0
cardinalToDegrees ESE = WindDirection 112.5
cardinalToDegrees SE = WindDirection 135.0
cardinalToDegrees SSE = WindDirection 157.5
cardinalToDegrees S = WindDirection 180.0
cardinalToDegrees SSW = WindDirection 202.5
cardinalToDegrees SW = WindDirection 225.0
cardinalToDegrees WSW = WindDirection 247.5
cardinalToDegrees W = WindDirection 270.0
cardinalToDegrees WNW = WindDirection 292.5
cardinalToDegrees NW = WindDirection 315.0
cardinalToDegrees NNW = WindDirection 337.5

-- | Convert degrees to nearest cardinal (16-point compass).
degreesToCardinal :: WindDirection -> Cardinal
degreesToCardinal (WindDirection d)
  | d < 11.25 = N
  | d < 33.75 = NNE
  | d < 56.25 = NE
  | d < 78.75 = ENE
  | d < 101.25 = E
  | d < 123.75 = ESE
  | d < 146.25 = SE
  | d < 168.75 = SSE
  | d < 191.25 = S
  | d < 213.75 = SSW
  | d < 236.25 = SW
  | d < 258.75 = WSW
  | d < 281.25 = W
  | d < 303.75 = WNW
  | d < 326.25 = NW
  | d < 348.75 = NNW
  | otherwise = N

-- | Standard abbreviation.
cardinalAbbreviation :: Cardinal -> String
cardinalAbbreviation = show
