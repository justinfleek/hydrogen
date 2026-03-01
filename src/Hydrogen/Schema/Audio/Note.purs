-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // audio // note
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MIDI Note compound — the actual notes producers play and sequence.
-- |
-- | ## Note Anatomy
-- | A MIDI note has:
-- | - Pitch (which key, 0-127)
-- | - Velocity (how hard, 1-127)
-- | - Start position (when it begins)
-- | - Duration (how long it lasts)
-- | - Channel (which MIDI channel)
-- |
-- | ## Modern Extensions
-- | Professional DAWs add:
-- | - Note probability (chance of playing, for generative music)
-- | - Velocity range (humanization)
-- | - Mute flag (silence without deleting)
-- |
-- | ## Ableton-Style Features
-- | - Note color (for visual organization)
-- | - Note expression (MPE-style per-note modulation)

module Hydrogen.Schema.Audio.Note
  ( -- * MIDI Note
    Note
  , note
  , noteWithChannel
  
  -- * Accessors
  , notePitch
  , noteVelocity
  , noteStart
  , noteDuration
  , noteChannel
  , noteEnd
  
  -- * Extended Properties
  , NoteProbability(..)
  , noteProbability
  , unwrapNoteProbability
  
  , VelocityRange(..)
  , velocityRange
  , unwrapVelocityRange
  
  -- * Operations
  , transposeNote
  , moveNote
  , stretchNote
  , setNoteVelocity
  , scaleNoteVelocity
  , adjustNoteVelocity
  , noteVelocityRaw
  
  -- * Predicates
  , noteOverlaps
  , noteContains
  , noteAtPosition
  
  -- * Note Collections
  , sortByStart
  , notesInRange
  ) where

import Prelude

import Data.Array as Array
import Data.Int as Int
import Hydrogen.Schema.Audio.MIDI (Channel, Velocity, channel, velocity, unwrapVelocity)
import Hydrogen.Schema.Audio.Tick (TickPosition, TickDuration, tickPosition, tickDuration, unwrapTickPosition, unwrapTickDuration)
import Hydrogen.Schema.Audio.Frequency (MidiNote, midiNote, unwrapMidiNote)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // note
-- ═════════════════════════════════════════════════════════════════════════════

-- | Note - A MIDI note with position, duration, and expression.
type Note =
  { pitch :: MidiNote         -- Which key (0-127)
  , velocity :: Velocity      -- How hard (1-127)
  , start :: TickPosition     -- When it starts
  , duration :: TickDuration  -- How long it lasts
  , channel :: Channel        -- MIDI channel (1-16)
  }

-- | Create a note on channel 1 (most common case)
note :: Int -> Int -> Int -> Int -> Note
note pitchVal vel startTick durationTicks =
  { pitch: midiNote pitchVal
  , velocity: velocity vel
  , start: tickPosition startTick
  , duration: tickDuration durationTicks
  , channel: channel 1
  }

-- | Create a note with explicit channel
noteWithChannel :: Int -> Int -> Int -> Int -> Int -> Note
noteWithChannel pitchVal vel startTick durationTicks chan =
  { pitch: midiNote pitchVal
  , velocity: velocity vel
  , start: tickPosition startTick
  , duration: tickDuration durationTicks
  , channel: channel chan
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

notePitch :: Note -> MidiNote
notePitch n = n.pitch

noteVelocity :: Note -> Velocity
noteVelocity n = n.velocity

noteStart :: Note -> TickPosition
noteStart n = n.start

noteDuration :: Note -> TickDuration
noteDuration n = n.duration

noteChannel :: Note -> Channel
noteChannel n = n.channel

-- | Calculate note end position (start + duration)
noteEnd :: Note -> TickPosition
noteEnd n =
  tickPosition (unwrapTickPosition n.start + unwrapTickDuration n.duration)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // extended properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | NoteProbability - Chance of note playing (0-100%).
-- | Ableton Live feature for generative/random sequences.
newtype NoteProbability = NoteProbability Int

derive instance eqNoteProbability :: Eq NoteProbability
derive instance ordNoteProbability :: Ord NoteProbability

instance showNoteProbability :: Show NoteProbability where
  show (NoteProbability n) = show n <> "%"

-- | Create probability (clamped to 0-100)
noteProbability :: Int -> NoteProbability
noteProbability n
  | n < 0 = NoteProbability 0
  | n > 100 = NoteProbability 100
  | otherwise = NoteProbability n

unwrapNoteProbability :: NoteProbability -> Int
unwrapNoteProbability (NoteProbability n) = n

-- | VelocityRange - Velocity deviation for humanization.
-- | The actual velocity can vary by ± this amount.
newtype VelocityRange = VelocityRange Int

derive instance eqVelocityRange :: Eq VelocityRange
derive instance ordVelocityRange :: Ord VelocityRange

instance showVelocityRange :: Show VelocityRange where
  show (VelocityRange n) = "±" <> show n

-- | Create velocity range (clamped to 0-64)
velocityRange :: Int -> VelocityRange
velocityRange n
  | n < 0 = VelocityRange 0
  | n > 64 = VelocityRange 64
  | otherwise = VelocityRange n

unwrapVelocityRange :: VelocityRange -> Int
unwrapVelocityRange (VelocityRange n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transpose a note by semitones
transposeNote :: Int -> Note -> Note
transposeNote semitones n =
  n { pitch = midiNote (unwrapMidiNote n.pitch + semitones) }

-- | Move a note to a new start position
moveNote :: TickPosition -> Note -> Note
moveNote newStart n = n { start = newStart }

-- | Stretch/compress note duration
stretchNote :: TickDuration -> Note -> Note
stretchNote newDuration n = n { duration = newDuration }

-- | Set note velocity
setNoteVelocity :: Velocity -> Note -> Note
setNoteVelocity vel n = n { velocity = vel }

-- | Scale note velocity by a factor (0.0 to 2.0)
-- | 0.5 = half velocity, 1.0 = unchanged, 2.0 = double (clamped to 127)
scaleNoteVelocity :: Number -> Note -> Note
scaleNoteVelocity factor n =
  let rawVel = unwrapVelocity n.velocity
      scaled = Int.round (Int.toNumber rawVel * factor)
  in n { velocity = velocity scaled }

-- | Adjust velocity by offset (positive or negative)
-- | Useful for accent patterns: +20 for accented beats
adjustNoteVelocity :: Int -> Note -> Note
adjustNoteVelocity offset n =
  let rawVel = unwrapVelocity n.velocity
  in n { velocity = velocity (rawVel + offset) }

-- | Get raw velocity value for calculations
noteVelocityRaw :: Note -> Int
noteVelocityRaw n = unwrapVelocity n.velocity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two notes overlap in time
noteOverlaps :: Note -> Note -> Boolean
noteOverlaps a b =
  let aStart = unwrapTickPosition a.start
      aEnd = unwrapTickPosition (noteEnd a)
      bStart = unwrapTickPosition b.start
      bEnd = unwrapTickPosition (noteEnd b)
  in aStart < bEnd && bStart < aEnd

-- | Check if a tick position is within a note
noteContains :: TickPosition -> Note -> Boolean
noteContains pos n =
  let p = unwrapTickPosition pos
      start = unwrapTickPosition n.start
      end = unwrapTickPosition (noteEnd n)
  in p >= start && p < end

-- | Check if a note starts at exactly this position
noteAtPosition :: TickPosition -> Note -> Boolean
noteAtPosition pos n = n.start == pos

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // note collections
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort notes by start position
sortByStart :: Array Note -> Array Note
sortByStart = Array.sortBy compareByStart
  where
    compareByStart a b = compare a.start b.start

-- | Get notes that fall within a tick range
notesInRange :: TickPosition -> TickPosition -> Array Note -> Array Note
notesInRange rangeStart rangeEnd = Array.filter inRange
  where
    inRange n =
      let nStart = unwrapTickPosition n.start
          nEnd = unwrapTickPosition (noteEnd n)
          rStart = unwrapTickPosition rangeStart
          rEnd = unwrapTickPosition rangeEnd
      in nStart < rEnd && nEnd > rStart
