-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- ///                                                                       ///
-- ///  HYDROGEN / SCHEMA / GAME / ROULETTE                                  ///
-- ///                                                                       ///
-- ///  Complete roulette wheel specification — European and American        ///
-- ///  layouts with physically accurate pocket ordering, color mapping,     ///
-- ///  and neighbor calculations for casino-grade accuracy.                 ///
-- ///                                                                       ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.Schema.Game.Roulette
  ( -- Wheel variants
    WheelType(European, American)
    -- Pocket representation
  , Pocket(PocketZero, PocketDoubleZero, PocketNumber)
    -- Pocket color
  , PocketColor(Red, Black, Green)
    -- Wheel layout type
  , WheelLayout
    -- Wheel section for neighbor bets
  , WheelSection
    -- Spin result with physics
  , SpinResult
    -- Wheel layouts
  , europeanWheel
  , americanWheel
    -- Pocket properties
  , pocketColor
  , pocketNumber
  , isEven
  , isOdd
  , isLow
  , isHigh
    -- Dozen and column
  , pocketDozen
  , pocketColumn
    -- Neighbor calculations
  , getNeighbors
    -- Validation
  , isValidPocket
    -- Position lookup
  , pocketPosition
    -- All pockets
  , allPockets
    -- Formatting
  , formatPocket
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , mod
  , negate
  , otherwise
  , show
  , (&&)
  , (+)
  , (-)
  , (<)
  , (<>)
  , (<=)
  , (==)
  , (>)
  , (>=)
  , (||)
  )

import Data.Array
  ( drop
  , elemIndex
  , index
  , length
  , range
  , (:)
  )

import Data.Maybe
  ( Maybe(Just, Nothing)
  , fromMaybe
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// WHEEL VARIANTS                                                        ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | The two standard roulette wheel configurations used in casinos worldwide.
-- | European wheels have a single zero (37 pockets, 2.7% house edge).
-- | American wheels have both zero and double-zero (38 pockets, 5.26% house edge).
data WheelType
  = European
  | American

derive instance eqWheelType :: Eq WheelType
derive instance ordWheelType :: Ord WheelType

instance showWheelType :: Show WheelType where
  show European = "European"
  show American = "American"

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// POCKET REPRESENTATION                                                 ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A pocket on the roulette wheel where the ball can land.
-- | PocketZero is the green 0 present on all wheels.
-- | PocketDoubleZero is the green 00 present only on American wheels.
-- | PocketNumber represents numbered pockets 1-36.
data Pocket
  = PocketZero
  | PocketDoubleZero
  | PocketNumber Int

derive instance eqPocket :: Eq Pocket
derive instance ordPocket :: Ord Pocket

instance showPocket :: Show Pocket where
  show PocketZero = "Pocket(0)"
  show PocketDoubleZero = "Pocket(00)"
  show (PocketNumber n) = "Pocket(" <> show n <> ")"

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// POCKET COLOR                                                          ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | The color of a roulette pocket.
-- | Red and Black alternate (with specific distribution for 1-36).
-- | Green is reserved for zero pockets.
data PocketColor
  = Red
  | Black
  | Green

derive instance eqPocketColor :: Eq PocketColor
derive instance ordPocketColor :: Ord PocketColor

instance showPocketColor :: Show PocketColor where
  show Red = "Red"
  show Black = "Black"
  show Green = "Green"

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// TYPE ALIASES                                                          ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Wheel layout as an array of pockets in clockwise physical order.
type WheelLayout = Array Pocket

-- | A section of the wheel for neighbor/sector bets.
-- | Center is the target pocket, neighbors are adjacent pockets on the wheel.
type WheelSection =
  { center :: Pocket
  , neighbors :: Array Pocket
  }

-- | Result of a roulette spin with physics data.
-- | wheelPosition: final resting angle of wheel (0-360 degrees)
-- | ballPosition: final resting angle of ball (0-360 degrees)
-- | spinDuration: total time for spin to complete (milliseconds)
type SpinResult =
  { pocket :: Pocket
  , wheelPosition :: Number
  , ballPosition :: Number
  , spinDuration :: Number
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// EUROPEAN WHEEL LAYOUT                                                 ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | European roulette wheel layout (single zero, 37 pockets).
-- | Pockets arranged clockwise starting from 0.
-- | This is the standard layout used in European and most international casinos.
europeanWheel :: WheelLayout
europeanWheel =
  [ PocketZero
  , PocketNumber 32
  , PocketNumber 15
  , PocketNumber 19
  , PocketNumber 4
  , PocketNumber 21
  , PocketNumber 2
  , PocketNumber 25
  , PocketNumber 17
  , PocketNumber 34
  , PocketNumber 6
  , PocketNumber 27
  , PocketNumber 13
  , PocketNumber 36
  , PocketNumber 11
  , PocketNumber 30
  , PocketNumber 8
  , PocketNumber 23
  , PocketNumber 10
  , PocketNumber 5
  , PocketNumber 24
  , PocketNumber 16
  , PocketNumber 33
  , PocketNumber 1
  , PocketNumber 20
  , PocketNumber 14
  , PocketNumber 31
  , PocketNumber 9
  , PocketNumber 22
  , PocketNumber 18
  , PocketNumber 29
  , PocketNumber 7
  , PocketNumber 28
  , PocketNumber 12
  , PocketNumber 35
  , PocketNumber 3
  , PocketNumber 26
  ]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// AMERICAN WHEEL LAYOUT                                                 ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | American roulette wheel layout (double zero, 38 pockets).
-- | Pockets arranged clockwise starting from 0.
-- | The 00 pocket is positioned opposite the 0 on the wheel.
americanWheel :: WheelLayout
americanWheel =
  [ PocketZero
  , PocketNumber 28
  , PocketNumber 9
  , PocketNumber 26
  , PocketNumber 30
  , PocketNumber 11
  , PocketNumber 7
  , PocketNumber 20
  , PocketNumber 32
  , PocketNumber 17
  , PocketNumber 5
  , PocketNumber 22
  , PocketNumber 34
  , PocketNumber 15
  , PocketNumber 3
  , PocketNumber 24
  , PocketNumber 36
  , PocketNumber 13
  , PocketNumber 1
  , PocketDoubleZero
  , PocketNumber 27
  , PocketNumber 10
  , PocketNumber 25
  , PocketNumber 29
  , PocketNumber 12
  , PocketNumber 8
  , PocketNumber 19
  , PocketNumber 31
  , PocketNumber 18
  , PocketNumber 6
  , PocketNumber 21
  , PocketNumber 33
  , PocketNumber 16
  , PocketNumber 4
  , PocketNumber 23
  , PocketNumber 35
  , PocketNumber 14
  , PocketNumber 2
  ]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// POCKET COLOR DETERMINATION                                            ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Red pocket numbers on a standard roulette wheel.
-- | These are fixed by casino standards worldwide.
redNumbers :: Array Int
redNumbers =
  [ 1, 3, 5, 7, 9, 12, 14, 16, 18, 19, 21, 23, 25, 27, 30, 32, 34, 36 ]

-- | Determine the color of a pocket.
-- | Zero pockets are always green.
-- | Numbers 1-36 are red or black per standard casino distribution.
pocketColor :: Pocket -> PocketColor
pocketColor PocketZero = Green
pocketColor PocketDoubleZero = Green
pocketColor (PocketNumber n) =
  case elemIndex n redNumbers of
    Just _ -> Red
    Nothing -> Black

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// POCKET NUMBER EXTRACTION                                              ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Extract the numeric value of a pocket.
-- | Returns Nothing for zero pockets (they have no numeric value for bets).
-- | Returns Just n for numbered pockets.
pocketNumber :: Pocket -> Maybe Int
pocketNumber PocketZero = Nothing
pocketNumber PocketDoubleZero = Nothing
pocketNumber (PocketNumber n) = Just n

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// EVEN/ODD DETERMINATION                                                ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Check if a pocket is even (for even/odd bets).
-- | Zero pockets are neither even nor odd (they lose even/odd bets).
isEven :: Pocket -> Boolean
isEven PocketZero = false
isEven PocketDoubleZero = false
isEven (PocketNumber n) = mod n 2 == 0

-- | Check if a pocket is odd (for even/odd bets).
-- | Zero pockets are neither even nor odd (they lose even/odd bets).
isOdd :: Pocket -> Boolean
isOdd PocketZero = false
isOdd PocketDoubleZero = false
isOdd (PocketNumber n) = mod n 2 == 1

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// LOW/HIGH DETERMINATION                                                ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Check if a pocket is low (1-18) for low/high bets.
-- | Zero pockets lose low/high bets.
isLow :: Pocket -> Boolean
isLow PocketZero = false
isLow PocketDoubleZero = false
isLow (PocketNumber n) = n >= 1 && n <= 18

-- | Check if a pocket is high (19-36) for low/high bets.
-- | Zero pockets lose low/high bets.
isHigh :: Pocket -> Boolean
isHigh PocketZero = false
isHigh PocketDoubleZero = false
isHigh (PocketNumber n) = n >= 19 && n <= 36

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// DOZEN DETERMINATION                                                   ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Determine which dozen a pocket belongs to (for dozen bets).
-- | First dozen: 1-12, Second dozen: 13-24, Third dozen: 25-36.
-- | Returns Nothing for zero pockets.
pocketDozen :: Pocket -> Maybe Int
pocketDozen PocketZero = Nothing
pocketDozen PocketDoubleZero = Nothing
pocketDozen (PocketNumber n)
  | n >= 1 && n <= 12 = Just 1
  | n >= 13 && n <= 24 = Just 2
  | n >= 25 && n <= 36 = Just 3
  | otherwise = Nothing

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// COLUMN DETERMINATION                                                  ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Determine which column a pocket belongs to (for column bets).
-- | First column: 1,4,7,10,13,16,19,22,25,28,31,34 (n mod 3 == 1)
-- | Second column: 2,5,8,11,14,17,20,23,26,29,32,35 (n mod 3 == 2)
-- | Third column: 3,6,9,12,15,18,21,24,27,30,33,36 (n mod 3 == 0)
-- | Returns Nothing for zero pockets.
pocketColumn :: Pocket -> Maybe Int
pocketColumn PocketZero = Nothing
pocketColumn PocketDoubleZero = Nothing
pocketColumn (PocketNumber n)
  | n < 1 || n > 36 = Nothing
  | mod n 3 == 1 = Just 1
  | mod n 3 == 2 = Just 2
  | mod n 3 == 0 = Just 3
  | otherwise = Nothing

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// WHEEL SELECTION                                                       ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Get the wheel layout for a given wheel type.
wheelFor :: WheelType -> WheelLayout
wheelFor European = europeanWheel
wheelFor American = americanWheel

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// POCKET POSITION                                                       ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Find the clockwise index position of a pocket on the wheel.
-- | Returns -1 if the pocket is not found (invalid for wheel type).
pocketPosition :: WheelType -> Pocket -> Int
pocketPosition wheelType pocket =
  let wheel = wheelFor wheelType
  in fromMaybe (-1) (elemIndex pocket wheel)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// POCKET VALIDATION                                                     ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Check if a pocket is valid for a given wheel type.
-- | European wheels do not have double zero.
-- | Numbers must be in range 1-36.
isValidPocket :: WheelType -> Pocket -> Boolean
isValidPocket European PocketDoubleZero = false
isValidPocket _ PocketZero = true
isValidPocket American PocketDoubleZero = true
isValidPocket _ (PocketNumber n) = n >= 1 && n <= 36

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// NEIGHBOR CALCULATION                                                  ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Get n neighbors on each side of a pocket (for neighbor/sector bets).
-- | Returns empty array if pocket is not valid for wheel type.
-- | Wraps around the wheel (circular array behavior).
getNeighbors :: WheelType -> Pocket -> Int -> Array Pocket
getNeighbors wheelType pocket count =
  let wheel = wheelFor wheelType
      wheelLen = length wheel
  in case elemIndex pocket wheel of
    Nothing -> []
    Just idx ->
      if count <= 0
        then []
        else gatherNeighbors wheel wheelLen idx count

-- | Helper to gather neighbors with circular wrapping.
gatherNeighbors :: WheelLayout -> Int -> Int -> Int -> Array Pocket
gatherNeighbors wheel wheelLen centerIdx count =
  let
    -- Get indices for left neighbors (counter-clockwise)
    leftIndices = map (\i -> mod (centerIdx - i + wheelLen) wheelLen) (range 1 count)
    -- Get indices for right neighbors (clockwise)
    rightIndices = map (\i -> mod (centerIdx + i) wheelLen) (range 1 count)
    -- Lookup pockets, filtering Nothing results
    lookupPocket idx = index wheel idx
    leftPockets = filterMap lookupPocket leftIndices
    rightPockets = filterMap lookupPocket rightIndices
  in
    -- Return left neighbors (reversed to be outward from center) then right
    reverseArray leftPockets <> rightPockets

-- | Filter and map: apply function, keep only Just values.
filterMap :: forall a b. (a -> Maybe b) -> Array a -> Array b
filterMap f arr = 
  let mapped = map f arr
  in catMaybes mapped

-- | Extract Just values from array of Maybes.
catMaybes :: forall a. Array (Maybe a) -> Array a
catMaybes arr = 
  let
    step :: Maybe a -> Array a -> Array a
    step Nothing acc = acc
    step (Just x) acc = x : acc
  in foldrArray step [] arr

-- | Fold right over an array.
foldrArray :: forall a b. (a -> b -> b) -> b -> Array a -> b
foldrArray f init arr =
  case index arr 0 of
    Nothing -> init
    Just x -> f x (foldrArray f init (drop 1 arr))

-- | Reverse an array.
reverseArray :: forall a. Array a -> Array a
reverseArray arr = foldrArray (\x acc -> acc <> [x]) [] arr

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// ALL POCKETS                                                           ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Get all pockets for a wheel type in wheel order.
allPockets :: WheelType -> Array Pocket
allPockets = wheelFor

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- /// POCKET FORMATTING                                                     ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Format a pocket for display.
-- | Returns "0", "00", or the number as a string.
formatPocket :: Pocket -> String
formatPocket PocketZero = "0"
formatPocket PocketDoubleZero = "00"
formatPocket (PocketNumber n) = show n

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- ///                                                                       ///
-- ///  END OF MODULE                                                        ///
-- ///                                                                       ///
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
