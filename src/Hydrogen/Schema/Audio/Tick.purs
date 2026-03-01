-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // audio // tick
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Musical time atoms — tick-based positioning for MIDI sequencing.
-- |
-- | ## PPQ (Pulses Per Quarter Note)
-- | The resolution of the sequencer's timing grid. Common values:
-- | - 24 PPQ: Original MIDI clock resolution
-- | - 96 PPQ: Basic DAW resolution
-- | - 480 PPQ: Standard professional resolution (Pro Tools, Cubase)
-- | - 960 PPQ: High resolution (Ableton Live, FL Studio)
-- |
-- | ## BarBeatTick
-- | Musical position as bars.beats.ticks — the way producers think about time.
-- | Example: 2.3.120 means bar 2, beat 3, tick 120.
-- |
-- | ## Absolute vs Relative
-- | - TickPosition: Absolute position from start (0, 1, 2, ...)
-- | - TickDuration: Relative length (can be used for note duration)
-- |
-- | ## Time Signature Dependency
-- | Converting BarBeatTick to absolute ticks requires knowing:
-- | - PPQ (ticks per beat)
-- | - Time signature (beats per bar)

module Hydrogen.Schema.Audio.Tick
  ( -- * PPQ (Resolution)
    PPQ(..)
  , ppq
  , unwrapPPQ
  , ppqBounds
  , ppq24
  , ppq96
  , ppq480
  , ppq960
  
  -- * Tick Position (Absolute)
  , TickPosition(..)
  , tickPosition
  , unwrapTickPosition
  , tickPositionBounds
  , tickZero
  
  -- * Tick Duration (Relative)
  , TickDuration(..)
  , tickDuration
  , unwrapTickDuration
  , tickDurationBounds
  
  -- * Bar/Beat/Tick (Musical Position)
  , BarBeatTick
  , barBeatTick
  , bbtBar
  , bbtBeat
  , bbtTick
  
  -- * Time Signature
  , TimeSignature
  , timeSignature
  , tsNumerator
  , tsDenominator
  , ts4_4
  , ts3_4
  , ts6_8
  
  -- * Conversions
  , bbtToTicks
  , ticksToBBT
  , ticksPerBar
  , ticksPerBeat
  
  -- * Operations
  , addTicks
  , subtractTicks
  , addBBT
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // ppq
-- ═════════════════════════════════════════════════════════════════════════════

-- | PPQ - Pulses Per Quarter note (sequencer resolution).
-- | Higher values = finer timing resolution.
-- | Bounded to standard DAW values: 24-960.
newtype PPQ = PPQ Int

derive instance eqPPQ :: Eq PPQ
derive instance ordPPQ :: Ord PPQ

instance showPPQ :: Show PPQ where
  show (PPQ n) = show n <> " PPQ"

-- | Create a PPQ value (clamped to 24-960)
ppq :: Int -> PPQ
ppq n
  | n < 24 = PPQ 24
  | n > 960 = PPQ 960
  | otherwise = PPQ n

unwrapPPQ :: PPQ -> Int
unwrapPPQ (PPQ n) = n

-- Standard PPQ values
ppq24 :: PPQ
ppq24 = PPQ 24

ppq96 :: PPQ
ppq96 = PPQ 96

ppq480 :: PPQ
ppq480 = PPQ 480

ppq960 :: PPQ
ppq960 = PPQ 960

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // tick position
-- ═════════════════════════════════════════════════════════════════════════════

-- | TickPosition - Absolute position in ticks from song start.
-- | Non-negative integer. Position 0 = start of song.
newtype TickPosition = TickPosition Int

derive instance eqTickPosition :: Eq TickPosition
derive instance ordTickPosition :: Ord TickPosition

instance showTickPosition :: Show TickPosition where
  show (TickPosition n) = "tick " <> show n

-- | Create a TickPosition (clamped to non-negative)
tickPosition :: Int -> TickPosition
tickPosition n
  | n < 0 = TickPosition 0
  | otherwise = TickPosition n

unwrapTickPosition :: TickPosition -> Int
unwrapTickPosition (TickPosition n) = n

-- | Start of song (tick 0)
tickZero :: TickPosition
tickZero = TickPosition 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // tick duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | TickDuration - Length in ticks (for note duration, etc.).
-- | Non-negative integer. Duration 0 = instantaneous.
newtype TickDuration = TickDuration Int

derive instance eqTickDuration :: Eq TickDuration
derive instance ordTickDuration :: Ord TickDuration

instance showTickDuration :: Show TickDuration where
  show (TickDuration n) = show n <> " ticks"

-- | Create a TickDuration (clamped to non-negative)
tickDuration :: Int -> TickDuration
tickDuration n
  | n < 0 = TickDuration 0
  | otherwise = TickDuration n

unwrapTickDuration :: TickDuration -> Int
unwrapTickDuration (TickDuration n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // bar beat tick
-- ═════════════════════════════════════════════════════════════════════════════

-- | BarBeatTick - Musical position in bars.beats.ticks format.
-- | This is how producers think about time.
-- | Bar and beat are 1-indexed (bar 1 = first bar, beat 1 = first beat).
-- | Tick is 0-indexed within the beat (0 to PPQ-1).
type BarBeatTick =
  { bar :: Int      -- 1-indexed bar number
  , beat :: Int     -- 1-indexed beat within bar
  , tick :: Int     -- 0-indexed tick within beat
  }

-- | Create a BarBeatTick with validation
barBeatTick :: Int -> Int -> Int -> BarBeatTick
barBeatTick b bt t =
  { bar: max 1 b
  , beat: max 1 bt
  , tick: max 0 t
  }

-- Accessors
bbtBar :: BarBeatTick -> Int
bbtBar bbt = bbt.bar

bbtBeat :: BarBeatTick -> Int
bbtBeat bbt = bbt.beat

bbtTick :: BarBeatTick -> Int
bbtTick bbt = bbt.tick

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // time signature
-- ═════════════════════════════════════════════════════════════════════════════

-- | TimeSignature - Musical meter (e.g., 4/4, 3/4, 6/8).
-- | Numerator = beats per bar, Denominator = beat unit.
type TimeSignature =
  { numerator :: Int    -- Beats per bar (1-32)
  , denominator :: Int  -- Beat unit (1, 2, 4, 8, 16, 32)
  }

-- | Create a TimeSignature with validation
timeSignature :: Int -> Int -> TimeSignature
timeSignature num denom =
  { numerator: clamp 1 32 num
  , denominator: clampDenom denom
  }
  where
    clamp lo hi x
      | x < lo = lo
      | x > hi = hi
      | otherwise = x
    clampDenom d
      | d <= 1 = 1
      | d <= 2 = 2
      | d <= 4 = 4
      | d <= 8 = 8
      | d <= 16 = 16
      | otherwise = 32

tsNumerator :: TimeSignature -> Int
tsNumerator ts = ts.numerator

tsDenominator :: TimeSignature -> Int
tsDenominator ts = ts.denominator

-- Common time signatures
ts4_4 :: TimeSignature
ts4_4 = { numerator: 4, denominator: 4 }

ts3_4 :: TimeSignature
ts3_4 = { numerator: 3, denominator: 4 }

ts6_8 :: TimeSignature
ts6_8 = { numerator: 6, denominator: 8 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ticks per beat (same as PPQ)
ticksPerBeat :: PPQ -> Int
ticksPerBeat (PPQ n) = n

-- | Ticks per bar (depends on time signature and PPQ)
-- | For 4/4 at 480 PPQ: 4 * 480 = 1920 ticks per bar
ticksPerBar :: PPQ -> TimeSignature -> Int
ticksPerBar (PPQ ppqVal) ts = ts.numerator * ppqVal

-- | Convert BarBeatTick to absolute tick position.
-- | Assumes constant time signature throughout.
bbtToTicks :: PPQ -> TimeSignature -> BarBeatTick -> TickPosition
bbtToTicks resolution ts bbt =
  let barTicks = (bbt.bar - 1) * ticksPerBar resolution ts
      beatTicks = (bbt.beat - 1) * ticksPerBeat resolution
      totalTicks = barTicks + beatTicks + bbt.tick
  in tickPosition totalTicks

-- | Convert absolute tick position to BarBeatTick.
-- | Assumes constant time signature throughout.
ticksToBBT :: PPQ -> TimeSignature -> TickPosition -> BarBeatTick
ticksToBBT resolution ts (TickPosition totalTicks) =
  let tpBar = ticksPerBar resolution ts
      tpBeat = ticksPerBeat resolution
      bars = totalTicks / tpBar
      remainderAfterBars = totalTicks `mod` tpBar
      beats = remainderAfterBars / tpBeat
      ticks = remainderAfterBars `mod` tpBeat
  in { bar: bars + 1
     , beat: beats + 1
     , tick: ticks
     }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add ticks to a position
addTicks :: TickPosition -> TickDuration -> TickPosition
addTicks (TickPosition pos) (TickDuration dur) =
  tickPosition (pos + dur)

-- | Subtract ticks from a position (clamped to 0)
subtractTicks :: TickPosition -> TickDuration -> TickPosition
subtractTicks (TickPosition pos) (TickDuration dur) =
  tickPosition (pos - dur)

-- | Add two BarBeatTick positions (requires time signature for carry)
addBBT :: PPQ -> TimeSignature -> BarBeatTick -> BarBeatTick -> BarBeatTick
addBBT resolution ts a b =
  let tickA = bbtToTicks resolution ts a
      tickB = bbtToTicks resolution ts b
      (TickPosition total) = addTicks tickA (TickDuration (unwrapTickPosition tickB))
  in ticksToBBT resolution ts (TickPosition total)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for PPQ (24-960)
ppqBounds :: Bounded.IntBounds
ppqBounds = Bounded.intBounds 24 960 Bounded.Clamps "ppq" "Pulses per quarter note (24-960)"

-- | Bounds for TickPosition (non-negative)
tickPositionBounds :: Bounded.IntBounds
tickPositionBounds = Bounded.intBounds 0 2147483647 Bounded.Clamps "tickPosition" "Absolute tick position (0+)"

-- | Bounds for TickDuration (non-negative)
tickDurationBounds :: Bounded.IntBounds
tickDurationBounds = Bounded.intBounds 0 2147483647 Bounded.Clamps "tickDuration" "Tick duration (0+)"
