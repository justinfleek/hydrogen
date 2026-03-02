-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // audio // automation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Automation — parameter changes over time.
-- |
-- | ## What Is Automation?
-- | Automation records how a parameter should change during playback:
-- | - Volume fades (intro fade-in, outro fade-out)
-- | - Filter sweeps (rising low-pass for builds)
-- | - Panning (stereo movement)
-- | - Send levels (reverb swells)
-- | - Any continuous parameter
-- |
-- | ## Automation Points
-- | An automation curve is defined by points with:
-- | - Position (when in the timeline)
-- | - Value (0.0-1.0 normalized, mapped to parameter range)
-- | - Curve type (how to interpolate to next point)
-- |
-- | ## Curve Types
-- | - Linear: straight line between points
-- | - Exponential: fast start, slow end (natural for volume)
-- | - Logarithmic: slow start, fast end (natural for frequency)
-- | - S-Curve: smooth ease in/out
-- | - Hold: stay at value until next point (step function)
-- |
-- | ## Automation Lanes
-- | Each parameter gets its own lane of automation:
-- | - Track volume lane
-- | - Track pan lane
-- | - Plugin parameter lanes
-- | - Send level lanes

module Hydrogen.Schema.Audio.Automation
  ( -- * Automation Value
    AutomationValue
  , automationValue
  , unwrapAutomationValue
  
  -- * Curve Types
  , CurveType(Linear, Exponential, Logarithmic, SCurve, Hold)
  
  -- * Automation Point
  , AutomationPoint
  , automationPoint
  , pointPosition
  , pointValue
  , pointCurve
  
  -- * Automation Lane
  , AutomationLane
  , automationLane
  , emptyLane
  , laneName
  , lanePoints
  , laneDefaultValue
  
  -- * Lane Operations
  , addPoint
  , removePoint
  , valueAtPosition
  , setLaneName
  
  -- * Interpolation
  , interpolate
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int as Int
import Data.Number (sqrt) as Number
import Hydrogen.Schema.Audio.Tick (TickPosition, unwrapTickPosition)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // automation value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized automation value in range [0.0, 1.0].
-- |
-- | All automation is stored normalized. The parameter being automated
-- | maps this to its actual range (e.g., 0.0-1.0 → -inf to +6dB for volume).
newtype AutomationValue = AutomationValue Number

-- | Create an automation value, clamped to [0.0, 1.0].
automationValue :: Number -> AutomationValue
automationValue n = AutomationValue (max 0.0 (min 1.0 n))

-- | Unwrap to raw number.
unwrapAutomationValue :: AutomationValue -> Number
unwrapAutomationValue (AutomationValue n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // curve types
-- ═════════════════════════════════════════════════════════════════════════════

-- | How to interpolate between automation points.
data CurveType
  = Linear        -- Straight line (default)
  | Exponential   -- Fast start, slow end (natural for volume)
  | Logarithmic   -- Slow start, fast end (natural for frequency)
  | SCurve        -- Smooth ease in/out
  | Hold          -- Step function (stay at value until next point)

derive instance eqCurveType :: Eq CurveType
derive instance ordCurveType :: Ord CurveType

instance showCurveType :: Show CurveType where
  show Linear = "Linear"
  show Exponential = "Exponential"
  show Logarithmic = "Logarithmic"
  show SCurve = "S-Curve"
  show Hold = "Hold"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // automation point
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single point on an automation curve.
-- |
-- | The curve type determines how to interpolate FROM this point to the next.
type AutomationPoint =
  { position :: TickPosition
  , value :: AutomationValue
  , curve :: CurveType
  }

-- | Create an automation point.
automationPoint :: TickPosition -> AutomationValue -> CurveType -> AutomationPoint
automationPoint position value curve = { position, value, curve }

-- | Get point position.
pointPosition :: AutomationPoint -> TickPosition
pointPosition p = p.position

-- | Get point value.
pointValue :: AutomationPoint -> AutomationValue
pointValue p = p.value

-- | Get point curve type.
pointCurve :: AutomationPoint -> CurveType
pointCurve p = p.curve

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // automation lane
-- ═════════════════════════════════════════════════════════════════════════════

-- | An automation lane for a single parameter.
-- |
-- | Each automatable parameter (volume, pan, filter cutoff, etc.)
-- | gets its own lane with its own set of points.
newtype AutomationLane = AutomationLane
  { name :: String                    -- Parameter name (e.g., "Volume", "Pan")
  , points :: Array AutomationPoint   -- Sorted by position
  , defaultValue :: AutomationValue   -- Value when no automation
  }

-- | Create an automation lane with points.
automationLane :: String -> AutomationValue -> Array AutomationPoint -> AutomationLane
automationLane name defaultVal points = AutomationLane
  { name
  , points: sortPointsByPosition points
  , defaultValue: defaultVal
  }

-- | Create an empty automation lane.
emptyLane :: String -> AutomationValue -> AutomationLane
emptyLane name defaultVal = automationLane name defaultVal []

-- | Get lane name.
laneName :: AutomationLane -> String
laneName (AutomationLane l) = l.name

-- | Get all points in the lane.
lanePoints :: AutomationLane -> Array AutomationPoint
lanePoints (AutomationLane l) = l.points

-- | Get default value (used when no automation exists).
laneDefaultValue :: AutomationLane -> AutomationValue
laneDefaultValue (AutomationLane l) = l.defaultValue

-- | Sort points by position.
sortPointsByPosition :: Array AutomationPoint -> Array AutomationPoint
sortPointsByPosition = Array.sortBy compareByPosition
  where
    compareByPosition a b = compare
      (unwrapTickPosition a.position)
      (unwrapTickPosition b.position)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // lane operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a point to the lane, keeping points sorted.
addPoint :: AutomationPoint -> AutomationLane -> AutomationLane
addPoint point (AutomationLane l) = AutomationLane l
  { points = sortPointsByPosition (Array.cons point l.points) }

-- | Remove a point at a specific index.
removePoint :: Int -> AutomationLane -> AutomationLane
removePoint idx (AutomationLane l) = AutomationLane l
  { points = case Array.deleteAt idx l.points of
      Just newPoints -> newPoints
      Nothing -> l.points
  }

-- | Set the lane name.
setLaneName :: String -> AutomationLane -> AutomationLane
setLaneName name (AutomationLane l) = AutomationLane l { name = name }

-- | Get the automation value at a specific position.
-- | Interpolates between surrounding points based on curve type.
valueAtPosition :: TickPosition -> AutomationLane -> AutomationValue
valueAtPosition pos (AutomationLane l) =
  case findSurroundingPoints pos l.points of
    Nothing -> l.defaultValue
    Just { before: Nothing, after: Nothing } -> l.defaultValue
    Just { before: Just p, after: Nothing } -> p.value
    Just { before: Nothing, after: Just p } -> p.value
    Just { before: Just p1, after: Just p2 } ->
      interpolate p1.curve p1.position p1.value p2.position p2.value pos

-- | Find points before and after a position.
findSurroundingPoints :: TickPosition -> Array AutomationPoint
  -> Maybe { before :: Maybe AutomationPoint, after :: Maybe AutomationPoint }
findSurroundingPoints pos points =
  let posTicks = unwrapTickPosition pos
      before = Array.last (Array.filter (\p -> unwrapTickPosition p.position <= posTicks) points)
      after = Array.head (Array.filter (\p -> unwrapTickPosition p.position > posTicks) points)
  in Just { before, after }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interpolate between two points based on curve type.
interpolate :: CurveType -> TickPosition -> AutomationValue 
            -> TickPosition -> AutomationValue 
            -> TickPosition -> AutomationValue
interpolate curveType startPos startVal endPos endVal currentPos =
  let startTicks = Int.toNumber (unwrapTickPosition startPos)
      endTicks = Int.toNumber (unwrapTickPosition endPos)
      currentTicks = Int.toNumber (unwrapTickPosition currentPos)
      
      -- Normalized position [0, 1]
      t = if endTicks == startTicks
            then 0.0
            else (currentTicks - startTicks) / (endTicks - startTicks)
      
      v1 = unwrapAutomationValue startVal
      v2 = unwrapAutomationValue endVal
      
      -- Apply curve function to get interpolated value
      interpolated = case curveType of
        Hold -> v1  -- Stay at start value until end
        Linear -> linearInterp v1 v2 t
        Exponential -> exponentialInterp v1 v2 t
        Logarithmic -> logarithmicInterp v1 v2 t
        SCurve -> sCurveInterp v1 v2 t
        
  in automationValue interpolated

-- | Linear interpolation: straight line.
linearInterp :: Number -> Number -> Number -> Number
linearInterp v1 v2 t = v1 + (v2 - v1) * t

-- | Exponential interpolation: fast start, slow end.
-- | Good for volume fades (perceived as linear due to logarithmic hearing).
exponentialInterp :: Number -> Number -> Number -> Number
exponentialInterp v1 v2 t =
  let curved = t * t  -- Square for exponential feel
  in v1 + (v2 - v1) * curved

-- | Logarithmic interpolation: slow start, fast end.
-- | Good for frequency sweeps.
logarithmicInterp :: Number -> Number -> Number -> Number
logarithmicInterp v1 v2 t =
  let curved = Number.sqrt t  -- Square root for logarithmic feel
  in v1 + (v2 - v1) * curved

-- | S-Curve interpolation: smooth ease in/out.
-- | Uses smoothstep: 3t² - 2t³
sCurveInterp :: Number -> Number -> Number -> Number
sCurveInterp v1 v2 t =
  let curved = t * t * (3.0 - 2.0 * t)  -- Smoothstep
  in v1 + (v2 - v1) * curved
