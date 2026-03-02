-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // audio // midi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MIDI protocol atoms — the foundation for note sequencing.
-- |
-- | ## MIDI 1.0 Specification
-- | MIDI uses 7-bit values (0-127) for most parameters and 14-bit for pitch bend.
-- | This module provides bounded types that match the MIDI spec exactly.
-- |
-- | ## Channel
-- | MIDI channels are 1-16 in user-facing display but 0-15 in protocol.
-- | We store as 1-16 to match what producers expect.
-- |
-- | ## Velocity
-- | Note-on velocity is 1-127 (0 means note-off in MIDI spec).
-- | Note-off velocity exists but is rarely used.
-- |
-- | ## Pitch Bend
-- | 14-bit signed: -8192 to +8191, center = 0.
-- | Range interpretation depends on synth (typically ±2 semitones).
-- |
-- | ## Control Change (CC)
-- | 128 controllers (0-127), each with 7-bit value (0-127).
-- | Some CCs have defined meanings (1=mod wheel, 7=volume, 10=pan, etc.)

module Hydrogen.Schema.Audio.MIDI
  ( -- * Channel
    Channel(Channel)
  , channel
  , unwrapChannel
  , channelBounds
  
  -- * Velocity
  , Velocity(Velocity)
  , velocity
  , unwrapVelocity
  , velocityBounds
  , velocityToLinear
  , linearToVelocity
  
  -- * Pitch Bend
  , PitchBend(PitchBend)
  , pitchBend
  , unwrapPitchBend
  , pitchBendBounds
  , pitchBendCenter
  , pitchBendToNormalized
  , normalizedToPitchBend
  
  -- * Control Change
  , CCNumber(CCNumber)
  , CCValue(CCValue)
  , ccNumber
  , ccValue
  , unwrapCCNumber
  , unwrapCCValue
  , ccNumberBounds
  , ccValueBounds
  
  -- * Standard CC Numbers
  , ccModWheel
  , ccBreath
  , ccVolume
  , ccPan
  , ccExpression
  , ccSustain
  , ccPortamento
  , ccAllNotesOff
  
  -- * Aftertouch
  , Aftertouch(Aftertouch)
  , aftertouch
  , unwrapAftertouch
  , aftertouchBounds
  
  -- * Program Change
  , Program(Program)
  , program
  , unwrapProgram
  , programBounds
  ) where

import Prelude

import Data.Int as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Channel - MIDI channel (1-16).
-- | Stored as 1-16 to match user expectation (not 0-15 protocol value).
newtype Channel = Channel Int

derive instance eqChannel :: Eq Channel
derive instance ordChannel :: Ord Channel

instance showChannel :: Show Channel where
  show (Channel n) = "Ch " <> show n

-- | Create a Channel value (clamped to 1-16)
channel :: Int -> Channel
channel n
  | n < 1 = Channel 1
  | n > 16 = Channel 16
  | otherwise = Channel n

unwrapChannel :: Channel -> Int
unwrapChannel (Channel n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // velocity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Velocity - note-on velocity (1-127).
-- | 0 is reserved for note-off in MIDI spec, so minimum is 1.
-- | 127 is maximum ("fff" dynamics).
newtype Velocity = Velocity Int

derive instance eqVelocity :: Eq Velocity
derive instance ordVelocity :: Ord Velocity

instance showVelocity :: Show Velocity where
  show (Velocity n) = "vel " <> show n

-- | Create a Velocity value (clamped to 1-127)
velocity :: Int -> Velocity
velocity n
  | n < 1 = Velocity 1
  | n > 127 = Velocity 127
  | otherwise = Velocity n

unwrapVelocity :: Velocity -> Int
unwrapVelocity (Velocity n) = n

-- | Convert velocity to linear amplitude (0.0-1.0)
-- | 1 -> ~0.008, 127 -> 1.0
velocityToLinear :: Velocity -> Number
velocityToLinear (Velocity n) = Int.toNumber n / 127.0

-- | Convert linear amplitude to velocity
-- | 0.0 -> 1, 1.0 -> 127
linearToVelocity :: Number -> Velocity
linearToVelocity lin
  | lin <= 0.0 = Velocity 1
  | lin >= 1.0 = Velocity 127
  | otherwise = velocity (Int.round (lin * 127.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // pitch bend
-- ═════════════════════════════════════════════════════════════════════════════

-- | PitchBend - 14-bit signed pitch bend (-8192 to +8191).
-- | Center position is 0. Full range depends on synth configuration
-- | (typically ±2 semitones, sometimes ±12 or ±24).
newtype PitchBend = PitchBend Int

derive instance eqPitchBend :: Eq PitchBend
derive instance ordPitchBend :: Ord PitchBend

instance showPitchBend :: Show PitchBend where
  show (PitchBend n) = "bend " <> show n

-- | Create a PitchBend value (clamped to -8192 to +8191)
pitchBend :: Int -> PitchBend
pitchBend n
  | n < (-8192) = PitchBend (-8192)
  | n > 8191 = PitchBend 8191
  | otherwise = PitchBend n

unwrapPitchBend :: PitchBend -> Int
unwrapPitchBend (PitchBend n) = n

-- | Center position (no bend)
pitchBendCenter :: PitchBend
pitchBendCenter = PitchBend 0

-- | Convert pitch bend to normalized (-1.0 to +1.0)
pitchBendToNormalized :: PitchBend -> Number
pitchBendToNormalized (PitchBend n)
  | n >= 0 = Int.toNumber n / 8191.0
  | otherwise = Int.toNumber n / 8192.0

-- | Convert normalized (-1.0 to +1.0) to pitch bend
normalizedToPitchBend :: Number -> PitchBend
normalizedToPitchBend norm
  | norm >= 0.0 = pitchBend (Int.round (norm * 8191.0))
  | otherwise = pitchBend (Int.round (norm * 8192.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // control change
-- ═════════════════════════════════════════════════════════════════════════════

-- | CCNumber - Control Change controller number (0-127).
-- | Some numbers have standard meanings (see ccModWheel, ccVolume, etc.)
newtype CCNumber = CCNumber Int

derive instance eqCCNumber :: Eq CCNumber
derive instance ordCCNumber :: Ord CCNumber

instance showCCNumber :: Show CCNumber where
  show (CCNumber n) = "CC" <> show n

-- | Create a CCNumber value (clamped to 0-127)
ccNumber :: Int -> CCNumber
ccNumber n
  | n < 0 = CCNumber 0
  | n > 127 = CCNumber 127
  | otherwise = CCNumber n

unwrapCCNumber :: CCNumber -> Int
unwrapCCNumber (CCNumber n) = n

-- | CCValue - Control Change value (0-127).
newtype CCValue = CCValue Int

derive instance eqCCValue :: Eq CCValue
derive instance ordCCValue :: Ord CCValue

instance showCCValue :: Show CCValue where
  show (CCValue n) = show n

-- | Create a CCValue (clamped to 0-127)
ccValue :: Int -> CCValue
ccValue n
  | n < 0 = CCValue 0
  | n > 127 = CCValue 127
  | otherwise = CCValue n

unwrapCCValue :: CCValue -> Int
unwrapCCValue (CCValue n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // standard cc numbers
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC1 - Modulation wheel
ccModWheel :: CCNumber
ccModWheel = CCNumber 1

-- | CC2 - Breath controller
ccBreath :: CCNumber
ccBreath = CCNumber 2

-- | CC7 - Channel volume
ccVolume :: CCNumber
ccVolume = CCNumber 7

-- | CC10 - Pan position (0=left, 64=center, 127=right)
ccPan :: CCNumber
ccPan = CCNumber 10

-- | CC11 - Expression controller
ccExpression :: CCNumber
ccExpression = CCNumber 11

-- | CC64 - Sustain pedal (0-63=off, 64-127=on)
ccSustain :: CCNumber
ccSustain = CCNumber 64

-- | CC65 - Portamento on/off
ccPortamento :: CCNumber
ccPortamento = CCNumber 65

-- | CC123 - All notes off
ccAllNotesOff :: CCNumber
ccAllNotesOff = CCNumber 123

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // aftertouch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Aftertouch - channel pressure (0-127).
-- | Also used for polyphonic aftertouch (per-note pressure).
newtype Aftertouch = Aftertouch Int

derive instance eqAftertouch :: Eq Aftertouch
derive instance ordAftertouch :: Ord Aftertouch

instance showAftertouch :: Show Aftertouch where
  show (Aftertouch n) = "AT " <> show n

-- | Create an Aftertouch value (clamped to 0-127)
aftertouch :: Int -> Aftertouch
aftertouch n
  | n < 0 = Aftertouch 0
  | n > 127 = Aftertouch 127
  | otherwise = Aftertouch n

unwrapAftertouch :: Aftertouch -> Int
unwrapAftertouch (Aftertouch n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // program change
-- ═════════════════════════════════════════════════════════════════════════════

-- | Program - program/patch number (0-127).
-- | Selects instrument preset on a synth.
newtype Program = Program Int

derive instance eqProgram :: Eq Program
derive instance ordProgram :: Ord Program

instance showProgram :: Show Program where
  show (Program n) = "Pgm " <> show n

-- | Create a Program value (clamped to 0-127)
program :: Int -> Program
program n
  | n < 0 = Program 0
  | n > 127 = Program 127
  | otherwise = Program n

unwrapProgram :: Program -> Int
unwrapProgram (Program n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Channel (1-16)
channelBounds :: Bounded.IntBounds
channelBounds = Bounded.intBounds 1 16 Bounded.Clamps "channel" "MIDI channel (1-16)"

-- | Bounds for Velocity (1-127)
velocityBounds :: Bounded.IntBounds
velocityBounds = Bounded.intBounds 1 127 Bounded.Clamps "velocity" "Note velocity (1-127)"

-- | Bounds for PitchBend (-8192 to +8191)
pitchBendBounds :: Bounded.IntBounds
pitchBendBounds = Bounded.intBounds (-8192) 8191 Bounded.Clamps "pitchBend" "Pitch bend (-8192 to +8191)"

-- | Bounds for CCNumber (0-127)
ccNumberBounds :: Bounded.IntBounds
ccNumberBounds = Bounded.intBounds 0 127 Bounded.Clamps "ccNumber" "Control change number (0-127)"

-- | Bounds for CCValue (0-127)
ccValueBounds :: Bounded.IntBounds
ccValueBounds = Bounded.intBounds 0 127 Bounded.Clamps "ccValue" "Control change value (0-127)"

-- | Bounds for Aftertouch (0-127)
aftertouchBounds :: Bounded.IntBounds
aftertouchBounds = Bounded.intBounds 0 127 Bounded.Clamps "aftertouch" "Aftertouch pressure (0-127)"

-- | Bounds for Program (0-127)
programBounds :: Bounded.IntBounds
programBounds = Bounded.intBounds 0 127 Bounded.Clamps "program" "Program/patch number (0-127)"
