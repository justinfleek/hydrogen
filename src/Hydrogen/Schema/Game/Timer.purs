-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // game // timer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Complete game timing — chess clocks, turn timers, time controls.
-- | Time bounded 0-86400000ms (24 hours). Deterministic at billion-agent scale.

module Hydrogen.Schema.Game.Timer
  ( Milliseconds, mkMilliseconds, unwrapMilliseconds, millisecondsBounds
  , milliseconds, seconds, minutes, hours
  , toSeconds, toMinutes, toHours, formatTime, formatTimeCompact
  , TimeControl(Untimed, Sudden, Increment, Delay, Bronstein, Hourglass)
  , StandardTimeControl(Bullet1Min, Bullet2Min, Blitz3Min, Blitz5Min, Rapid10Min, Rapid15Min, Classical30Min, Classical60Min, Correspondence)
  , standardTimeControl, allStandardTimeControls, timeControlCategory, formatTimeControl
  , Player(Player1, Player2), opposingPlayer, allPlayers
  , ChessClock, mkChessClock, clockWhiteTime, clockBlackTime, clockActivePlayer, clockTimeControl
  , startClock, stopClock, switchPlayer, addIncrement, tickClock, setTime
  , ClockEvent(ClockStarted, ClockPaused, ClockResumed, MoveMade, TimeExpired, IncrementAdded)
  , isTimeExpired, hasLowTime, timeRemaining, activeTimeRemaining, percentRemaining
  , TurnTimer, mkTurnTimer, timerRemaining, timerTurnLimit, timerExtensions
  , startTurn, usedTime, extendTime, tickTimer, resetTimer
  , addTime, subtractTime, multiplyTime, minTime, maxTime, zeroTime, maxBoundedTime
  , LowTimeThreshold, mkLowTimeThreshold, defaultLowTimeThreshold, criticalTimeThreshold
  ) where

import Prelude
  ( class Eq, class Ord, class Show, show, otherwise
  , (==), (<), (>), (<=), (>=), (+), (-), (*), (/), (<>), mod, max, min )
import Hydrogen.Schema.Bounded (IntBounds, BoundsBehavior(Clamps), intBounds, clampInt)
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // milliseconds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time in milliseconds, bounded 0-86400000 (24 hours). Clamped at bounds.
newtype Milliseconds = Milliseconds Int
derive instance eqMilliseconds :: Eq Milliseconds
derive instance ordMilliseconds :: Ord Milliseconds
instance showMilliseconds :: Show Milliseconds where
  show (Milliseconds ms) = "Milliseconds " <> show ms

millisecondsBounds :: IntBounds
millisecondsBounds = intBounds 0 86400000 Clamps "milliseconds" "Time in milliseconds (0 to 24 hours)"

maxMilliseconds :: Int
maxMilliseconds = 86400000

mkMilliseconds :: Int -> Milliseconds
mkMilliseconds n = Milliseconds (clampInt 0 maxMilliseconds n)

unwrapMilliseconds :: Milliseconds -> Int
unwrapMilliseconds (Milliseconds ms) = ms

milliseconds :: Int -> Milliseconds
milliseconds = mkMilliseconds

seconds :: Int -> Milliseconds
seconds s = mkMilliseconds (s * 1000)

minutes :: Int -> Milliseconds
minutes m = mkMilliseconds (m * 60000)

hours :: Int -> Milliseconds
hours h = mkMilliseconds (h * 3600000)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // conversions
-- ═════════════════════════════════════════════════════════════════════════════

toSeconds :: Milliseconds -> Int
toSeconds (Milliseconds ms) = ms / 1000

toMinutes :: Milliseconds -> Int
toMinutes (Milliseconds ms) = ms / 60000

toHours :: Milliseconds -> Int
toHours (Milliseconds ms) = ms / 3600000

-- | Format as "H:MM:SS" or "M:SS". E.g., 90000ms -> "1:30"
formatTime :: Milliseconds -> String
formatTime (Milliseconds ms) =
  let totalSeconds = ms / 1000
      totalMinutes = totalSeconds / 60
      hrs = totalMinutes / 60
      mins = totalMinutes `mod` 60
      secs = totalSeconds `mod` 60
  in if hrs > 0
     then show hrs <> ":" <> padZero mins <> ":" <> padZero secs
     else show mins <> ":" <> padZero secs

-- | Format as "M:SS.mmm" with milliseconds.
formatTimeCompact :: Milliseconds -> String
formatTimeCompact (Milliseconds ms) =
  let totalSeconds = ms / 1000
      totalMinutes = totalSeconds / 60
      hrs = totalMinutes / 60
      mins = totalMinutes `mod` 60
      secs = totalSeconds `mod` 60
      millis = ms `mod` 1000
  in if hrs > 0
     then show hrs <> ":" <> padZero mins <> ":" <> padZero secs <> "." <> padMillis millis
     else show mins <> ":" <> padZero secs <> "." <> padMillis millis

padZero :: Int -> String
padZero n | n < 10 = "0" <> show n | otherwise = show n

padMillis :: Int -> String
padMillis n | n < 10 = "00" <> show n | n < 100 = "0" <> show n | otherwise = show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // time control
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time control types for competitive games.
data TimeControl
  = Untimed                              -- No clock
  | Sudden Milliseconds                  -- All moves in base time
  | Increment Milliseconds Milliseconds  -- Base + per-move increment
  | Delay Milliseconds Milliseconds      -- Base + delay before clock starts
  | Bronstein Milliseconds Milliseconds  -- Base + Bronstein delay
  | Hourglass Milliseconds               -- Time transfers on move

derive instance eqTimeControl :: Eq TimeControl
instance showTimeControl :: Show TimeControl where
  show Untimed = "Untimed"
  show (Sudden base) = "Sudden " <> show base
  show (Increment base inc) = "Increment " <> show base <> " " <> show inc
  show (Delay base d) = "Delay " <> show base <> " " <> show d
  show (Bronstein base b) = "Bronstein " <> show base <> " " <> show b
  show (Hourglass base) = "Hourglass " <> show base

-- | Format for display: "5+3", "10|0", "3d5", "3b5", "Hourglass 5"
formatTimeControl :: TimeControl -> String
formatTimeControl Untimed = "Untimed"
formatTimeControl (Sudden base) = show (toMinutes base) <> "|0"
formatTimeControl (Increment base inc) = show (toMinutes base) <> "+" <> show (toSeconds inc)
formatTimeControl (Delay base d) = show (toMinutes base) <> "d" <> show (toSeconds d)
formatTimeControl (Bronstein base b) = show (toMinutes base) <> "b" <> show (toSeconds b)
formatTimeControl (Hourglass base) = "Hourglass " <> show (toMinutes base)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // standard time controls
-- ═════════════════════════════════════════════════════════════════════════════

-- | FIDE/Lichess standard presets: Bullet (<3m), Blitz (3-10m), Rapid (10-30m), Classical (30+m)
data StandardTimeControl
  = Bullet1Min | Bullet2Min | Blitz3Min | Blitz5Min
  | Rapid10Min | Rapid15Min | Classical30Min | Classical60Min | Correspondence

derive instance eqStandardTimeControl :: Eq StandardTimeControl
derive instance ordStandardTimeControl :: Ord StandardTimeControl
instance showStandardTimeControl :: Show StandardTimeControl where
  show Bullet1Min = "Bullet1Min"
  show Bullet2Min = "Bullet2Min"
  show Blitz3Min = "Blitz3Min"
  show Blitz5Min = "Blitz5Min"
  show Rapid10Min = "Rapid10Min"
  show Rapid15Min = "Rapid15Min"
  show Classical30Min = "Classical30Min"
  show Classical60Min = "Classical60Min"
  show Correspondence = "Correspondence"

allStandardTimeControls :: Array StandardTimeControl
allStandardTimeControls =
  [Bullet1Min, Bullet2Min, Blitz3Min, Blitz5Min, Rapid10Min, Rapid15Min, Classical30Min, Classical60Min, Correspondence]

standardTimeControl :: StandardTimeControl -> TimeControl
standardTimeControl Bullet1Min = Increment (minutes 1) (seconds 0)
standardTimeControl Bullet2Min = Increment (minutes 2) (seconds 1)
standardTimeControl Blitz3Min = Increment (minutes 3) (seconds 0)
standardTimeControl Blitz5Min = Increment (minutes 5) (seconds 3)
standardTimeControl Rapid10Min = Increment (minutes 10) (seconds 0)
standardTimeControl Rapid15Min = Increment (minutes 15) (seconds 10)
standardTimeControl Classical30Min = Sudden (minutes 30)
standardTimeControl Classical60Min = Sudden (minutes 60)
standardTimeControl Correspondence = Sudden (hours 24)

timeControlCategory :: StandardTimeControl -> String
timeControlCategory Bullet1Min = "Bullet"
timeControlCategory Bullet2Min = "Bullet"
timeControlCategory Blitz3Min = "Blitz"
timeControlCategory Blitz5Min = "Blitz"
timeControlCategory Rapid10Min = "Rapid"
timeControlCategory Rapid15Min = "Rapid"
timeControlCategory Classical30Min = "Classical"
timeControlCategory Classical60Min = "Classical"
timeControlCategory Correspondence = "Correspondence"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // player
-- ═════════════════════════════════════════════════════════════════════════════

data Player = Player1 | Player2
derive instance eqPlayer :: Eq Player
derive instance ordPlayer :: Ord Player
instance showPlayer :: Show Player where
  show Player1 = "Player1"
  show Player2 = "Player2"

opposingPlayer :: Player -> Player
opposingPlayer Player1 = Player2
opposingPlayer Player2 = Player1

allPlayers :: Array Player
allPlayers = [Player1, Player2]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // chess clock
-- ═════════════════════════════════════════════════════════════════════════════

type ChessClock =
  { whiteTime :: Milliseconds
  , blackTime :: Milliseconds
  , activePlayer :: Maybe Player
  , timeControl :: TimeControl
  }

mkChessClock :: TimeControl -> ChessClock
mkChessClock tc =
  { whiteTime: initialTime tc, blackTime: initialTime tc
  , activePlayer: Nothing, timeControl: tc }

initialTime :: TimeControl -> Milliseconds
initialTime Untimed = maxBoundedTime
initialTime (Sudden base) = base
initialTime (Increment base _) = base
initialTime (Delay base _) = base
initialTime (Bronstein base _) = base
initialTime (Hourglass base) = base

clockWhiteTime :: ChessClock -> Milliseconds
clockWhiteTime clock = clock.whiteTime

clockBlackTime :: ChessClock -> Milliseconds
clockBlackTime clock = clock.blackTime

clockActivePlayer :: ChessClock -> Maybe Player
clockActivePlayer clock = clock.activePlayer

clockTimeControl :: ChessClock -> TimeControl
clockTimeControl clock = clock.timeControl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // clock operations
-- ═════════════════════════════════════════════════════════════════════════════

startClock :: Player -> ChessClock -> ChessClock
startClock player clock = clock { activePlayer = Just player }

stopClock :: ChessClock -> ChessClock
stopClock clock = clock { activePlayer = Nothing }

switchPlayer :: ChessClock -> ChessClock
switchPlayer clock = case clock.activePlayer of
  Nothing -> clock
  Just Player1 -> clock { activePlayer = Just Player2 }
  Just Player2 -> clock { activePlayer = Just Player1 }

addIncrement :: Player -> Milliseconds -> ChessClock -> ChessClock
addIncrement Player1 inc clock = clock { whiteTime = addTime clock.whiteTime inc }
addIncrement Player2 inc clock = clock { blackTime = addTime clock.blackTime inc }

tickClock :: Milliseconds -> ChessClock -> ChessClock
tickClock elapsed clock = case clock.activePlayer of
  Nothing -> clock
  Just Player1 -> clock { whiteTime = subtractTime clock.whiteTime elapsed }
  Just Player2 -> clock { blackTime = subtractTime clock.blackTime elapsed }

setTime :: Player -> Milliseconds -> ChessClock -> ChessClock
setTime Player1 t clock = clock { whiteTime = t }
setTime Player2 t clock = clock { blackTime = t }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // clock events
-- ═════════════════════════════════════════════════════════════════════════════

data ClockEvent
  = ClockStarted | ClockPaused | ClockResumed
  | MoveMade Player Milliseconds
  | TimeExpired Player
  | IncrementAdded Player Milliseconds

derive instance eqClockEvent :: Eq ClockEvent
instance showClockEvent :: Show ClockEvent where
  show ClockStarted = "ClockStarted"
  show ClockPaused = "ClockPaused"
  show ClockResumed = "ClockResumed"
  show (MoveMade p t) = "MoveMade " <> show p <> " " <> show t
  show (TimeExpired p) = "TimeExpired " <> show p
  show (IncrementAdded p t) = "IncrementAdded " <> show p <> " " <> show t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // clock queries
-- ═════════════════════════════════════════════════════════════════════════════

isTimeExpired :: Player -> ChessClock -> Boolean
isTimeExpired Player1 clock = unwrapMilliseconds clock.whiteTime <= 0
isTimeExpired Player2 clock = unwrapMilliseconds clock.blackTime <= 0

hasLowTime :: Player -> LowTimeThreshold -> ChessClock -> Boolean
hasLowTime Player1 (LowTimeThreshold threshold) clock =
  unwrapMilliseconds clock.whiteTime < unwrapMilliseconds threshold
hasLowTime Player2 (LowTimeThreshold threshold) clock =
  unwrapMilliseconds clock.blackTime < unwrapMilliseconds threshold

timeRemaining :: Player -> ChessClock -> Milliseconds
timeRemaining Player1 clock = clock.whiteTime
timeRemaining Player2 clock = clock.blackTime

activeTimeRemaining :: ChessClock -> Maybe Milliseconds
activeTimeRemaining clock = case clock.activePlayer of
  Nothing -> Nothing
  Just p -> Just (timeRemaining p clock)

percentRemaining :: Player -> ChessClock -> Int
percentRemaining player clock =
  let remaining = unwrapMilliseconds (timeRemaining player clock)
      initial = unwrapMilliseconds (initialTime clock.timeControl)
  in if initial <= 0 then 100 else clampInt 0 100 ((remaining * 100) / initial)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // turn timer
-- ═════════════════════════════════════════════════════════════════════════════

type TurnTimer =
  { remaining :: Milliseconds
  , turnLimit :: Milliseconds
  , extensions :: Int
  }

mkTurnTimer :: Milliseconds -> Int -> TurnTimer
mkTurnTimer limit ext =
  { remaining: limit, turnLimit: limit, extensions: clampInt 0 99 ext }

timerRemaining :: TurnTimer -> Milliseconds
timerRemaining timer = timer.remaining

timerTurnLimit :: TurnTimer -> Milliseconds
timerTurnLimit timer = timer.turnLimit

timerExtensions :: TurnTimer -> Int
timerExtensions timer = timer.extensions

startTurn :: TurnTimer -> TurnTimer
startTurn timer = timer { remaining = timer.turnLimit }

usedTime :: TurnTimer -> Milliseconds
usedTime timer = subtractTime timer.turnLimit timer.remaining

extendTime :: TurnTimer -> Maybe TurnTimer
extendTime timer
  | timer.extensions <= 0 = Nothing
  | otherwise =
      let bonus = mkMilliseconds (unwrapMilliseconds timer.turnLimit / 2)
      in Just timer { remaining = addTime timer.remaining bonus, extensions = timer.extensions - 1 }

tickTimer :: Milliseconds -> TurnTimer -> TurnTimer
tickTimer elapsed timer = timer { remaining = subtractTime timer.remaining elapsed }

resetTimer :: Milliseconds -> Int -> TurnTimer -> TurnTimer
resetTimer limit ext _ = mkTurnTimer limit ext

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // time arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

addTime :: Milliseconds -> Milliseconds -> Milliseconds
addTime (Milliseconds a) (Milliseconds b) = mkMilliseconds (a + b)

subtractTime :: Milliseconds -> Milliseconds -> Milliseconds
subtractTime (Milliseconds a) (Milliseconds b) = mkMilliseconds (a - b)

multiplyTime :: Milliseconds -> Int -> Milliseconds
multiplyTime (Milliseconds ms) factor = mkMilliseconds (ms * factor)

minTime :: Milliseconds -> Milliseconds -> Milliseconds
minTime (Milliseconds a) (Milliseconds b) = Milliseconds (min a b)

maxTime :: Milliseconds -> Milliseconds -> Milliseconds
maxTime (Milliseconds a) (Milliseconds b) = Milliseconds (max a b)

zeroTime :: Milliseconds
zeroTime = Milliseconds 0

maxBoundedTime :: Milliseconds
maxBoundedTime = Milliseconds maxMilliseconds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // low time threshold
-- ═════════════════════════════════════════════════════════════════════════════

newtype LowTimeThreshold = LowTimeThreshold Milliseconds
derive instance eqLowTimeThreshold :: Eq LowTimeThreshold
derive instance ordLowTimeThreshold :: Ord LowTimeThreshold
instance showLowTimeThreshold :: Show LowTimeThreshold where
  show (LowTimeThreshold ms) = "LowTimeThreshold " <> show ms

mkLowTimeThreshold :: Milliseconds -> LowTimeThreshold
mkLowTimeThreshold = LowTimeThreshold

defaultLowTimeThreshold :: LowTimeThreshold
defaultLowTimeThreshold = LowTimeThreshold (seconds 30)

criticalTimeThreshold :: LowTimeThreshold
criticalTimeThreshold = LowTimeThreshold (seconds 10)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                       // end
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
