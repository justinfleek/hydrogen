-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // audio // frequency // notes
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Musical note name representation and MIDI mapping.
-- |
-- | This module provides:
-- | - NoteName type for chromatic scale note names
-- | - Conversion between MIDI notes and note names
-- | - Octave number extraction from MIDI notes

module Hydrogen.Schema.Audio.Frequency.Notes
  ( -- * Note Name Type
    NoteName(C, CSharp, D, DSharp, E, F, FSharp, G, GSharp, A, ASharp, B)
  
  -- * Enumeration
  , allNoteNames
  
  -- * MIDI Mapping
  , midiToNoteName
  , midiToOctaveNumber
  
  -- * String Conversion
  , noteNameToString
  ) where

import Prelude (class Eq, class Ord, class Show, mod, (-), (/))

import Hydrogen.Schema.Audio.Frequency.Types (MidiNote(MidiNote))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // note names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Musical note names (chromatic scale)
data NoteName
  = C
  | CSharp
  | D
  | DSharp
  | E
  | F
  | FSharp
  | G
  | GSharp
  | A
  | ASharp
  | B

derive instance eqNoteName :: Eq NoteName
derive instance ordNoteName :: Ord NoteName

instance showNoteName :: Show NoteName where
  show n = noteNameToString n

-- | All note names for enumeration (chromatic scale)
allNoteNames :: Array NoteName
allNoteNames = [ C, CSharp, D, DSharp, E, F, FSharp, G, GSharp, A, ASharp, B ]

-- | Convert note name to string representation
noteNameToString :: NoteName -> String
noteNameToString C = "C"
noteNameToString CSharp = "C#"
noteNameToString D = "D"
noteNameToString DSharp = "D#"
noteNameToString E = "E"
noteNameToString F = "F"
noteNameToString FSharp = "F#"
noteNameToString G = "G"
noteNameToString GSharp = "G#"
noteNameToString A = "A"
noteNameToString ASharp = "A#"
noteNameToString B = "B"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // midi mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the note name from a MIDI note number
midiToNoteName :: MidiNote -> NoteName
midiToNoteName (MidiNote n) =
  case n `mod` 12 of
    0 -> C
    1 -> CSharp
    2 -> D
    3 -> DSharp
    4 -> E
    5 -> F
    6 -> FSharp
    7 -> G
    8 -> GSharp
    9 -> A
    10 -> ASharp
    _ -> B  -- 11

-- | Get the octave number from a MIDI note number.
-- | MIDI 0-11 = octave -1, 12-23 = octave 0, 60-71 = octave 4
midiToOctaveNumber :: MidiNote -> Int
midiToOctaveNumber (MidiNote n) = (n / 12) - 1
