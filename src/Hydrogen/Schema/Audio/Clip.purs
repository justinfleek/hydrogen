-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // audio // clip
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MIDI Clip — the container that holds notes in a DAW.
-- |
-- | ## What Is A Clip?
-- | A clip is a container of musical content that can be:
-- | - Placed on a track at a position
-- | - Looped to repeat content
-- | - Colored for visual organization
-- | - Muted without deleting
-- |
-- | ## MIDI vs Audio Clips
-- | This module defines MIDI clips (containing notes).
-- | Audio clips (containing waveforms) are a separate concern.
-- |
-- | ## Loop Behavior
-- | When looped:
-- | - Clip plays from loopStart to loopEnd
-- | - Then jumps back to loopStart
-- | - Continues until arrangement position ends
-- |
-- | ## Clip Length
-- | The clip's total length determines its footprint in the arrangement.
-- | Loop regions must be within this length.

module Hydrogen.Schema.Audio.Clip
  ( -- * MIDI Clip
    MIDIClip
  , midiClip
  , emptyClip
  
  -- * Accessors
  , clipNotes
  , clipLength
  , clipName
  , clipColor
  , clipMuted
  
  -- * Loop Settings
  , LoopSettings
  , loopSettings
  , loopEnabled
  , loopStart
  , loopEnd
  , clipLoop
  
  -- * Note Operations
  , addNote
  , removeNoteAt
  , notesAtPosition
  , allNotes
  , noteCount
  
  -- * Clip Operations
  , setClipLength
  , setClipLoop
  , muteClip
  , unmuteClip
  , setClipName
  , setClipColor
  
  -- * Transformations
  , transposeClip
  , quantizeClip
  , quantizeToGrid
  , reverseClip
  , scaleClipVelocities
  
  -- * Grid Helpers
  , gridSixteenthNotes
  , gridEighthNotes
  , gridQuarterNotes
  , clipDurationBeats
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Hydrogen.Schema.Audio.Note (Note, transposeNote, scaleNoteVelocity, noteStart, noteEnd, noteDuration, sortByStart, moveNote)
import Hydrogen.Schema.Audio.Tick (TickPosition, TickDuration, tickPosition, tickDuration, unwrapTickPosition, unwrapTickDuration, PPQ, ticksPerBeat)
import Hydrogen.Schema.Color.SRGB (SRGB, srgb)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // loop settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Loop configuration for a clip.
-- | When enabled, playback cycles between loopStart and loopEnd positions.
-- |
-- | Invariant: loopEnd > loopStart (enforced by smart constructor)
newtype LoopSettings = LoopSettings
  { enabled :: Boolean
  , start :: TickPosition    -- Where the loop begins
  , end :: TickPosition      -- Where the loop ends (exclusive)
  }

-- | Create loop settings with validation.
-- | Returns Nothing if start >= end.
loopSettings :: Boolean -> TickPosition -> TickPosition -> Maybe LoopSettings
loopSettings enabled start end =
  if unwrapTickPosition end > unwrapTickPosition start
    then Just (LoopSettings { enabled, start, end })
    else Nothing

-- | Check if looping is enabled.
loopEnabled :: LoopSettings -> Boolean
loopEnabled (LoopSettings ls) = ls.enabled

-- | Get loop start position.
loopStart :: LoopSettings -> TickPosition
loopStart (LoopSettings ls) = ls.start

-- | Get loop end position.
loopEnd :: LoopSettings -> TickPosition
loopEnd (LoopSettings ls) = ls.end

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // midi clip
-- ═════════════════════════════════════════════════════════════════════════════

-- | A MIDI clip containing notes.
-- |
-- | This is the fundamental container for musical content in a DAW.
-- | Clips hold notes and can be placed on tracks, looped, muted, and colored.
newtype MIDIClip = MIDIClip
  { name :: String                    -- User-visible name
  , color :: SRGB                     -- Visual color for UI
  , notes :: Array Note               -- The actual musical content
  , length :: TickDuration            -- Total clip length
  , loop :: Maybe LoopSettings        -- Optional loop region
  , muted :: Boolean                  -- If true, clip produces no output
  }

-- | Default clip color — a neutral gray.
-- | Channel values: R=128, G=128, B=128 (mid-gray)
defaultClipColor :: SRGB
defaultClipColor = srgb 128 128 128

-- | Create a MIDI clip with notes.
-- | Length is required; if notes extend beyond length, they will be clipped on playback.
midiClip :: String -> TickDuration -> Array Note -> MIDIClip
midiClip name length notes = MIDIClip
  { name
  , color: defaultClipColor
  , notes: sortByStart notes
  , length
  , loop: Nothing
  , muted: false
  }

-- | Create an empty clip with a given length.
emptyClip :: PPQ -> TickDuration -> MIDIClip
emptyClip _ppq length = MIDIClip
  { name: "New Clip"
  , color: defaultClipColor
  , notes: []
  , length
  , loop: Nothing
  , muted: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all notes in the clip.
clipNotes :: MIDIClip -> Array Note
clipNotes (MIDIClip c) = c.notes

-- | Get clip length.
clipLength :: MIDIClip -> TickDuration
clipLength (MIDIClip c) = c.length

-- | Get clip name.
clipName :: MIDIClip -> String
clipName (MIDIClip c) = c.name

-- | Get clip color.
clipColor :: MIDIClip -> SRGB
clipColor (MIDIClip c) = c.color

-- | Check if clip is muted.
clipMuted :: MIDIClip -> Boolean
clipMuted (MIDIClip c) = c.muted

-- | Get clip loop settings (if any).
clipLoop :: MIDIClip -> Maybe LoopSettings
clipLoop (MIDIClip c) = c.loop

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // note operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a note to the clip.
-- | Notes are kept sorted by start position.
addNote :: Note -> MIDIClip -> MIDIClip
addNote note (MIDIClip c) = MIDIClip c
  { notes = sortByStart (Array.cons note c.notes) }

-- | Remove a note at a specific index.
-- | Returns the clip unchanged if index is out of bounds.
removeNoteAt :: Int -> MIDIClip -> MIDIClip
removeNoteAt idx (MIDIClip c) = MIDIClip c
  { notes = case Array.deleteAt idx c.notes of
      Just newNotes -> newNotes
      Nothing -> c.notes
  }

-- | Find all notes that are sounding at a given position.
-- | A note is "at" a position if start <= position < end.
notesAtPosition :: TickPosition -> MIDIClip -> Array Note
notesAtPosition pos (MIDIClip c) = Array.filter (noteAtPos pos) c.notes
  where
    noteAtPos :: TickPosition -> Note -> Boolean
    noteAtPos p n =
      let posVal = unwrapTickPosition p
          startVal = unwrapTickPosition (noteStart n)
          endVal = unwrapTickPosition (noteEnd n)
      in startVal <= posVal && posVal < endVal

-- | Get all notes (alias for clipNotes for API consistency).
allNotes :: MIDIClip -> Array Note
allNotes = clipNotes

-- | Count the number of notes in the clip.
noteCount :: MIDIClip -> Int
noteCount (MIDIClip c) = Array.length c.notes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // clip operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the clip length.
setClipLength :: TickDuration -> MIDIClip -> MIDIClip
setClipLength len (MIDIClip c) = MIDIClip c { length = len }

-- | Set loop settings.
setClipLoop :: Maybe LoopSettings -> MIDIClip -> MIDIClip
setClipLoop loop (MIDIClip c) = MIDIClip c { loop = loop }

-- | Mute the clip.
muteClip :: MIDIClip -> MIDIClip
muteClip (MIDIClip c) = MIDIClip c { muted = true }

-- | Unmute the clip.
unmuteClip :: MIDIClip -> MIDIClip
unmuteClip (MIDIClip c) = MIDIClip c { muted = false }

-- | Set the clip name.
setClipName :: String -> MIDIClip -> MIDIClip
setClipName name (MIDIClip c) = MIDIClip c { name = name }

-- | Set the clip color.
setClipColor :: SRGB -> MIDIClip -> MIDIClip
setClipColor color (MIDIClip c) = MIDIClip c { color = color }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transpose all notes in the clip by a number of semitones.
-- | Notes that would go out of MIDI range (0-127) are clamped.
transposeClip :: Int -> MIDIClip -> MIDIClip
transposeClip semitones (MIDIClip c) = MIDIClip c
  { notes = map (transposeNote semitones) c.notes }

-- | Scale all note velocities by a factor.
-- | Factor of 1.0 = no change, 0.5 = half velocity, 2.0 = double (clamped to 127).
scaleClipVelocities :: Number -> MIDIClip -> MIDIClip
scaleClipVelocities factor (MIDIClip c) = MIDIClip c
  { notes = map (scaleNoteVelocity factor) c.notes }

-- | Quantize all notes to a grid.
-- | Grid size is specified in ticks (e.g., PPQ/4 for 16th notes at standard PPQ).
-- | Each note's start position is snapped to the nearest grid line.
quantizeClip :: Int -> MIDIClip -> MIDIClip
quantizeClip gridSize (MIDIClip c) = MIDIClip c
  { notes = sortByStart (map (quantizeNote gridSize) c.notes) }
  where
    quantizeNote :: Int -> Note -> Note
    quantizeNote grid n =
      let startTicks = unwrapTickPosition (noteStart n)
          -- Round to nearest grid line
          quantized = (startTicks + grid / 2) / grid * grid
          newStart = tickPosition quantized
      in moveNote newStart n

-- | Reverse all notes in the clip.
-- | Notes are mirrored around the clip's length.
-- | A note at position 0 moves to (length - noteDuration), etc.
reverseClip :: MIDIClip -> MIDIClip
reverseClip (MIDIClip c) = MIDIClip c
  { notes = sortByStart (map reverseNote c.notes) }
  where
    clipLen :: Int
    clipLen = unwrapTickDuration c.length
    
    reverseNote :: Note -> Note
    reverseNote n =
      let startTicks = unwrapTickPosition (noteStart n)
          durTicks = unwrapTickDuration (noteDuration n)
          -- New start = length - (oldStart + duration)
          newStartTicks = clipLen - startTicks - durTicks
          safeStart = max 0 newStartTicks
          newStart = tickPosition safeStart
      in moveNote newStart n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // grid helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate grid size for 16th notes at given PPQ.
gridSixteenthNotes :: PPQ -> Int
gridSixteenthNotes ppq = ticksPerBeat ppq / 4

-- | Calculate grid size for 8th notes at given PPQ.
gridEighthNotes :: PPQ -> Int
gridEighthNotes ppq = ticksPerBeat ppq / 2

-- | Calculate grid size for quarter notes at given PPQ.
gridQuarterNotes :: PPQ -> Int
gridQuarterNotes ppq = ticksPerBeat ppq

-- | Quantize to a named grid division.
-- | Convenience wrapper that calculates grid from PPQ and note value.
quantizeToGrid :: PPQ -> Int -> MIDIClip -> MIDIClip
quantizeToGrid ppq divisor clip = quantizeClip (ticksPerBeat ppq / divisor) clip

-- | Create a clip duration from beats.
-- | Example: clipDurationBeats ppq 4 = duration of 4 beats
clipDurationBeats :: PPQ -> Int -> TickDuration
clipDurationBeats ppq beats = tickDuration (ticksPerBeat ppq * beats)
