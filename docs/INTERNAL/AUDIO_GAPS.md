# Audio Framework Gaps — 20-Year Veteran Perspective

**Author:** Session 14, thinking like someone who's been in Ableton/Logic/FL/Pro Tools since the early 2000s  
**Date:** 2026-02-28  
**Purpose:** Document what's actually missing vs. what spec says we need

---

## What We Have (Substantial)

The Schema/Audio layer is surprisingly complete for **synthesis and effects**:

| Module | Lines | Coverage |
|--------|-------|----------|
| Effects.purs | 574 | Reverb, Delay, Compressor, EQ, Distortion, Gate, Limiter |
| Envelope.purs | 362 | ADSR, AHDSR, time scaling |
| Modulation.purs | 287 | LFO, sync ratios, depth |
| Time.purs | 318 | BPM, beats, bars, samples, conversions |
| Oscillator.purs | 211 | All waveforms including noise colors |
| Filter.purs | 182 | All filter types, slopes, key tracking |
| Synthesis.purs | 400+ | Cutoff, resonance, drive, mix, feedback |

The DAW layer has:
- Types.purs (387 lines) — Decibel, Frequency, Pan, Velocity
- Mixer.purs (483 lines) — Channel strips, EQ, buses
- Control.purs (643 lines) — Knobs, sliders, pads, XY pads

---

## What's Actually Missing (Veteran's View)

### 1. **CLIP & ARRANGEMENT — The Big Gap**

This is the elephant in the room. We have great synthesis atoms but **no way to represent what's actually in a project**.

```
What Ableton has that we don't:

┌─────────────────────────────────────────────────────────────────┐
│ ARRANGEMENT VIEW                                                 │
├─────────────────────────────────────────────────────────────────┤
│ Track 1  │▓▓▓▓▓▓▓▓│        │▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│    │▓▓▓▓│       │
│ Track 2  │        │▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│        │▓▓▓▓│             │
│ Track 3  │▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓│
└─────────────────────────────────────────────────────────────────┘
         │ Each block is a CLIP with:                             │
         │ - Start/end position (bars.beats.ticks)                │
         │ - Audio/MIDI content reference                         │
         │ - Per-clip gain, pitch, warp settings                  │
         │ - Fade in/out curves                                   │
         │ - Loop settings                                        │
         │ - Automation lanes                                     │
```

**Missing types:**
- `Clip` — The fundamental unit of arrangement
- `ClipSlot` — Position + clip reference
- `Arrangement` — Timeline of clips across tracks
- `Region` — Selection within arrangement
- `Marker` — Named position (verse, chorus, drop)
- `Locator` — Cue points for navigation
- `Loop` — Loop region definition

### 2. **MIDI — Only Half There**

We have `Velocity` but that's it. A producer expects:

```purescript
-- What we NEED for MIDI editing
type MIDINote =
  { pitch :: NoteNumber        -- 0-127
  , velocity :: Velocity       -- 1-127 (0 = note off)
  , startTime :: TickPosition  -- Position in ticks
  , duration :: TickDuration   -- Length in ticks
  , channel :: MIDIChannel     -- 1-16
  , probability :: Percent     -- Ableton's note probability
  , velocityRange :: VelocityRange  -- Humanization
  }

type MIDIClip =
  { notes :: Array MIDINote
  , length :: BarBeatTick
  , loopEnabled :: Boolean
  , loopStart :: BarBeatTick
  , loopEnd :: BarBeatTick
  , scale :: Maybe Scale       -- Scale/chord awareness
  , groove :: Maybe GrooveRef  -- Groove template reference
  }
```

**Missing types:**
- `NoteNumber` (0-127)
- `MIDIChannel` (1-16)
- `TickPosition` / `TickDuration`
- `BarBeatTick` compound
- `PitchBend` (14-bit, -8192 to +8191)
- `CCValue` (0-127)
- `AfterTouch` (channel and poly)
- `MPE` types (slide, pressure per note)
- `NoteExpression` (VST3 style)
- `Scale` / `Key` for scale-aware editing
- `Chord` for chord detection/suggestion

### 3. **AUTOMATION — Completely Missing**

Every parameter in a DAW can be automated. We have **zero automation types**.

```purescript
-- What automation looks like
type AutomationPoint =
  { time :: BarBeatTick
  , value :: NormalizedValue   -- 0.0-1.0, maps to parameter range
  , curve :: AutomationCurve   -- Linear, bezier, hold, etc.
  }

data AutomationCurve
  = Linear           -- Straight line
  | Hold             -- Step/jump
  | Bezier Number Number  -- Control points
  | SCurve           -- Smooth S-curve
  | Exponential Number    -- Exp curve with tension
  | Logarithmic Number    -- Log curve with tension

type AutomationLane =
  { parameter :: ParameterRef
  , points :: Array AutomationPoint
  , mode :: AutomationMode     -- Read, Write, Touch, Latch
  , visible :: Boolean
  }

data AutomationMode
  = AutoOff      -- Ignore automation
  | AutoRead     -- Play back automation
  | AutoWrite    -- Overwrite on playback
  | AutoTouch    -- Write while touching, return to read
  | AutoLatch    -- Write while touching, hold value
```

### 4. **AUDIO CLIPS & WARP — Missing**

We have sample rate but no audio clip representation:

```purescript
type AudioClip =
  { fileRef :: AudioFileRef    -- Path to audio file
  , sampleRate :: SampleRate
  , bitDepth :: BitDepth
  , channels :: ChannelCount   -- Mono, stereo, 5.1, etc.
  , originalBPM :: Maybe BPM   -- Detected or tagged tempo
  , warpMode :: WarpMode
  , warpMarkers :: Array WarpMarker
  , gain :: ClipGain
  , transpose :: Semitones
  , detune :: Cents
  , reverse :: Boolean
  , fadeIn :: FadeCurve
  , fadeOut :: FadeCurve
  }

data WarpMode
  = Beats          -- For rhythmic material
  | Tones          -- For pitched material (vocals, instruments)
  | Texture        -- For atonal textures, ambience
  | Repitch        -- Classic sampler style (pitch = speed)
  | Complex        -- High quality, CPU heavy
  | ComplexPro     -- Formant preservation

type WarpMarker =
  { samplePosition :: SampleCount   -- Position in source file
  , beatPosition :: BarBeatTick     -- Position in project
  }
```

### 5. **ROUTING & I/O — Basic Only**

The mixer has buses but no proper routing graph:

```purescript
-- What we need for professional routing
type RoutingPoint =
  { source :: AudioSource
  , destination :: AudioDestination
  , gain :: Decibel
  , pan :: Pan
  }

data AudioSource
  = HardwareInput Int          -- Physical input
  | TrackOutput TrackId
  | BusOutput BusId
  | SendReturn SendId
  | Sidechain TrackId          -- Sidechain source
  | Resampling                 -- Internal audio

data AudioDestination
  = HardwareOutput Int
  | TrackInput TrackId
  | BusInput BusId
  | MasterInput
  | External ExternalId        -- ReWire, etc.

-- Sidechain is HUGE for modern production
type SidechainConfig =
  { source :: AudioSource
  , filterEnabled :: Boolean
  , filterCutoff :: Frequency
  , filterType :: FilterType
  }
```

### 6. **PLUGIN SYSTEM — Missing**

No representation for VST/AU/AAX plugins:

```purescript
data PluginFormat = VST2 | VST3 | AU | AAX | CLAP | LV2

type PluginRef =
  { format :: PluginFormat
  , identifier :: String       -- Unique plugin ID
  , name :: String
  , vendor :: String
  , version :: PluginVersion
  }

type PluginInstance =
  { plugin :: PluginRef
  , state :: PluginState       -- Serialized state blob
  , parameters :: Array PluginParameter
  , bypass :: Boolean
  , sidechain :: Maybe SidechainConfig
  , latency :: SampleCount     -- Plugin-reported latency
  }

type PluginParameter =
  { id :: Int                  -- Parameter index
  , name :: String
  , value :: NormalizedValue   -- 0.0-1.0
  , displayValue :: String     -- "12.5 dB", "-3 semitones", etc.
  , automation :: Maybe AutomationLane
  }
```

### 7. **TIME SIGNATURE & METER — Incomplete**

We have BPM but complex meter changes are missing:

```purescript
type TimeSignature =
  { numerator :: Int           -- Beats per bar (1-32)
  , denominator :: Int         -- Beat unit (1, 2, 4, 8, 16, 32)
  }

type TempoChange =
  { position :: BarBeatTick
  , tempo :: BPM
  , curve :: TempoCurve        -- Linear or instant
  }

type MeterChange =
  { position :: BarBeatTick
  , signature :: TimeSignature
  }

type TempoMap =
  { initialTempo :: BPM
  , initialSignature :: TimeSignature
  , tempoChanges :: Array TempoChange
  , meterChanges :: Array MeterChange
  }
```

### 8. **QUANTIZATION & GROOVE — Missing**

Every DAW has quantize. We don't:

```purescript
type QuantizeSettings =
  { grid :: NoteValue          -- 1/4, 1/8, 1/16, etc.
  , strength :: Percent        -- 0-100% (how much to move)
  , swing :: Percent           -- Swing amount
  , triplets :: Boolean
  , humanize :: HumanizeSettings
  }

data NoteValue
  = N1   -- Whole note
  | N2   -- Half
  | N4   -- Quarter
  | N8   -- Eighth
  | N16  -- Sixteenth
  | N32  -- Thirty-second
  | N64  -- Sixty-fourth
  | N1T  -- Whole triplet
  | N2T  | N4T | N8T | N16T | N32T  -- Triplets
  | N1D  -- Whole dotted
  | N2D  | N4D | N8D | N16D | N32D  -- Dotted

type GrooveTemplate =
  { name :: String
  , timing :: Array Number     -- Timing offsets per step (-1.0 to 1.0)
  , velocity :: Array Number   -- Velocity scales per step
  , base :: NoteValue          -- What grid the groove is based on
  }
```

### 9. **UNDO/REDO SYSTEM — Missing**

Professional DAWs have deep undo. We have no action history:

```purescript
type Action =
  { id :: ActionId
  , timestamp :: DateTime
  , description :: String
  , category :: ActionCategory
  , inverse :: Action          -- How to undo this
  }

data ActionCategory
  = EditAction       -- Note/clip editing
  | MixAction        -- Volume, pan, etc.
  | ArrangeAction    -- Moving clips
  | PluginAction     -- Plugin changes
  | RecordAction     -- Recording
```

### 10. **PROJECT STRUCTURE — Missing**

No way to represent a complete project:

```purescript
type Project =
  { name :: String
  , path :: FilePath
  , sampleRate :: SampleRate
  , bitDepth :: BitDepth
  , tempoMap :: TempoMap
  , tracks :: Array Track
  , buses :: Array Bus
  , master :: MasterBus
  , arrangement :: Arrangement
  , markers :: Array Marker
  , selectedTrack :: Maybe TrackId
  , playhead :: BarBeatTick
  , loopRegion :: Maybe Region
  , soloMode :: SoloMode
  , metadata :: ProjectMetadata
  }
```

---

## Priority Order (What a Producer Hits First)

### P0 — Can't Make Music Without These

1. **MIDI Types** — NoteNumber, Channel, PitchBend, CC, BarBeatTick
2. **MIDINote & MIDIClip** — The actual notes in a clip
3. **Clip** — Container for audio or MIDI content
4. **Arrangement** — Timeline of clips

### P1 — Can't Mix Without These

5. **Automation** — AutomationPoint, AutomationLane
6. **Audio Clip** — File ref, warp, fades
7. **Routing** — Sidechain, send/return

### P2 — Can't Polish Without These

8. **Quantization** — Grid, strength, swing
9. **Time Signature** — Meter changes
10. **Plugin System** — VST/AU representation

### P3 — Professional Features

11. **Tempo Map** — Complex tempo automation
12. **Groove Templates** — Humanization
13. **Project** — Complete project structure
14. **Undo System** — Action history

---

## Recommended Next Session

Start with **MIDI foundation** because everything else depends on it:

1. `Schema/Audio/MIDI.purs` — Core MIDI atoms
   - NoteNumber, MIDIChannel, CCValue, PitchBend
   - BarBeatTick, TickPosition, TickDuration
   - PPQ (pulses per quarter)

2. `Schema/Audio/Note.purs` — Note representation
   - MIDINote compound
   - Velocity, duration, probability

3. `Schema/Audio/Clip.purs` — Clip container
   - MIDIClip, AudioClip
   - Loop settings, fade curves

Then we have the atoms to build arrangement and automation on top.

---

## The 20-Year Veteran's Honest Assessment

What's here is **really solid** for synthesis parameters. The bounded types, presets, and atomic design are exactly right.

But it's like having a synth engine with no sequencer. You can make sounds, but you can't make a song.

The MIDI/Clip/Arrangement layer is where producers actually live. That's where the gaps are.

---

*Document finalized 2026-02-28, Session 14*
