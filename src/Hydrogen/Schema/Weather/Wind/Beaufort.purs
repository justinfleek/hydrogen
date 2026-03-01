-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // weather // wind // beaufort
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Beaufort wind scale classification.
-- |
-- | The Beaufort scale is an empirical measure relating wind speed to
-- | observed conditions on sea and land.
-- |
-- | Standard scale is 0-12; extended scale goes to 17 for tropical cyclones.

module Hydrogen.Schema.Weather.Wind.Beaufort
  ( -- * Beaufort Number
    BeaufortNumber
  , beaufortNumber
  , beaufortNumberUnsafe
  , unwrapBeaufort
  , beaufortBounds
  
  -- * Conversions
  , speedToBeaufort
  , beaufortToMinSpeed
  
  -- * Descriptions
  , beaufortDescription
  , beaufortSeaCondition
  , beaufortLandCondition
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<)
  , (<=)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Weather.Wind.Speed (WindSpeed, windSpeedUnsafe, unwrapSpeed)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // beaufort // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Beaufort wind scale number [0, 12].
newtype BeaufortNumber = BeaufortNumber Int

derive instance eqBeaufortNumber :: Eq BeaufortNumber
derive instance ordBeaufortNumber :: Ord BeaufortNumber

instance showBeaufortNumber :: Show BeaufortNumber where
  show (BeaufortNumber n) = "Beaufort " <> show n

-- | Safe constructor with clamping.
beaufortNumber :: Int -> BeaufortNumber
beaufortNumber n = BeaufortNumber (Bounded.clampInt 0 12 n)

-- | Unsafe constructor for known-valid values.
beaufortNumberUnsafe :: Int -> BeaufortNumber
beaufortNumberUnsafe = BeaufortNumber

-- | Extract raw value.
unwrapBeaufort :: BeaufortNumber -> Int
unwrapBeaufort (BeaufortNumber n) = n

-- | Valid bounds documentation.
beaufortBounds :: Bounded.IntBounds
beaufortBounds = Bounded.intBounds 0 12 Bounded.Clamps "beaufort" "Beaufort scale number"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert wind speed to Beaufort number.
speedToBeaufort :: WindSpeed -> BeaufortNumber
speedToBeaufort ws =
  let v = unwrapSpeed ws
  in if v < 0.5 then BeaufortNumber 0
     else if v < 1.6 then BeaufortNumber 1
     else if v < 3.4 then BeaufortNumber 2
     else if v < 5.5 then BeaufortNumber 3
     else if v < 8.0 then BeaufortNumber 4
     else if v < 10.8 then BeaufortNumber 5
     else if v < 13.9 then BeaufortNumber 6
     else if v < 17.2 then BeaufortNumber 7
     else if v < 20.8 then BeaufortNumber 8
     else if v < 24.5 then BeaufortNumber 9
     else if v < 28.5 then BeaufortNumber 10
     else if v < 32.7 then BeaufortNumber 11
     else BeaufortNumber 12

-- | Minimum wind speed for a Beaufort number.
beaufortToMinSpeed :: BeaufortNumber -> WindSpeed
beaufortToMinSpeed (BeaufortNumber n)
  | n <= 0 = windSpeedUnsafe 0.0
  | n <= 1 = windSpeedUnsafe 0.5
  | n <= 2 = windSpeedUnsafe 1.6
  | n <= 3 = windSpeedUnsafe 3.4
  | n <= 4 = windSpeedUnsafe 5.5
  | n <= 5 = windSpeedUnsafe 8.0
  | n <= 6 = windSpeedUnsafe 10.8
  | n <= 7 = windSpeedUnsafe 13.9
  | n <= 8 = windSpeedUnsafe 17.2
  | n <= 9 = windSpeedUnsafe 20.8
  | n <= 10 = windSpeedUnsafe 24.5
  | n <= 11 = windSpeedUnsafe 28.5
  | otherwise = windSpeedUnsafe 32.7

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Human-readable description.
beaufortDescription :: BeaufortNumber -> String
beaufortDescription (BeaufortNumber n)
  | n <= 0 = "Calm"
  | n <= 1 = "Light air"
  | n <= 2 = "Light breeze"
  | n <= 3 = "Gentle breeze"
  | n <= 4 = "Moderate breeze"
  | n <= 5 = "Fresh breeze"
  | n <= 6 = "Strong breeze"
  | n <= 7 = "Near gale"
  | n <= 8 = "Gale"
  | n <= 9 = "Strong gale"
  | n <= 10 = "Storm"
  | n <= 11 = "Violent storm"
  | otherwise = "Hurricane"

-- | Sea condition description.
beaufortSeaCondition :: BeaufortNumber -> String
beaufortSeaCondition (BeaufortNumber n)
  | n <= 0 = "Sea like a mirror"
  | n <= 1 = "Ripples without crests"
  | n <= 2 = "Small wavelets, crests glassy"
  | n <= 3 = "Large wavelets, crests break"
  | n <= 4 = "Small waves, frequent whitecaps"
  | n <= 5 = "Moderate waves, many whitecaps"
  | n <= 6 = "Large waves, white foam crests"
  | n <= 7 = "Sea heaps up, foam blown in streaks"
  | n <= 8 = "Moderately high waves, spray"
  | n <= 9 = "High waves, dense foam streaks"
  | n <= 10 = "Very high waves, overhanging crests"
  | n <= 11 = "Exceptionally high waves, visibility affected"
  | otherwise = "Air filled with foam and spray"

-- | Land condition description.
beaufortLandCondition :: BeaufortNumber -> String
beaufortLandCondition (BeaufortNumber n)
  | n <= 0 = "Smoke rises vertically"
  | n <= 1 = "Smoke drift indicates wind direction"
  | n <= 2 = "Wind felt on face, leaves rustle"
  | n <= 3 = "Leaves and small twigs in motion"
  | n <= 4 = "Small branches move, dust rises"
  | n <= 5 = "Small trees sway"
  | n <= 6 = "Large branches move, wires whistle"
  | n <= 7 = "Whole trees in motion, walking impeded"
  | n <= 8 = "Twigs break off trees"
  | n <= 9 = "Slight structural damage"
  | n <= 10 = "Trees uprooted, considerable damage"
  | n <= 11 = "Widespread damage"
  | otherwise = "Severe and extensive damage"
