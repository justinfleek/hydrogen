━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                 // 10b // audio
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Audio Pillar

Audio synthesis, MIDI protocol, effects processing, and spatial positioning.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Audio/`
- **Files**: 44 modules
- **Key features**: MIDI protocol, synthesis, effects, spatial audio, speech

## Purpose

Audio provides bounded, deterministic primitives for:
- MIDI protocol (notes, velocity, pitch bend, CC)
- Oscillator waveforms and synthesis
- ADSR envelopes
- Filter types (low-pass, high-pass, etc.)
- Effects (reverb, delay, compression, EQ)
- Stereo and 3D spatial positioning
- Musical time (tempo, time signatures, timecode)
- Speech synthesis and recognition

────────────────────────────────────────────────────────────────────────────────
                                                                 // midi // atoms
────────────────────────────────────────────────────────────────────────────────

## MIDI Protocol

MIDI 1.0 specification atoms. 7-bit values (0-127) for most parameters,
14-bit for pitch bend.

### Channel

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Channel | Int | 1 | 16 | clamps | MIDI channel (user-facing 1-16) |

### Velocity

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Velocity | Int | 1 | 127 | clamps | Note-on velocity (0 = note-off in MIDI spec) |

**Conversions:**
- `velocityToLinear` — Velocity to 0.0-1.0 amplitude
- `linearToVelocity` — 0.0-1.0 to velocity

### Pitch Bend

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| PitchBend | Int | -8192 | 8191 | clamps | 14-bit signed, center = 0 |

**Presets:**
- `pitchBendCenter` — No bend (0)

**Conversions:**
- `pitchBendToNormalized` — To -1.0 to +1.0
- `normalizedToPitchBend` — From -1.0 to +1.0

### Control Change

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| CCNumber | Int | 0 | 127 | clamps | Controller number |
| CCValue | Int | 0 | 127 | clamps | Controller value |

**Standard CC Numbers:**

| Name | CC# | Purpose |
|------|-----|---------|
| `ccModWheel` | 1 | Modulation wheel |
| `ccBreath` | 2 | Breath controller |
| `ccVolume` | 7 | Channel volume |
| `ccPan` | 10 | Pan position (0=L, 64=C, 127=R) |
| `ccExpression` | 11 | Expression controller |
| `ccSustain` | 64 | Sustain pedal (0-63=off, 64-127=on) |
| `ccPortamento` | 65 | Portamento on/off |
| `ccAllNotesOff` | 123 | All notes off |

### Aftertouch

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Aftertouch | Int | 0 | 127 | clamps | Channel or polyphonic pressure |

### Program Change

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Program | Int | 0 | 127 | clamps | Instrument preset selection |

────────────────────────────────────────────────────────────────────────────────
                                                            // frequency // atoms
────────────────────────────────────────────────────────────────────────────────

## Frequency and Pitch

MIDI note numbers, frequency in Hz, and digital audio parameters.

### MIDI Notes

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| MidiNote | Int | 0 | 127 | clamps | MIDI note number (60 = Middle C, 69 = A4) |

**Formula:** `frequency = 440 × 2^((note - 69) / 12)`

**Conversions:**
- `midiToHertz` — MIDI note to Hz
- `hertzToMidi` — Hz to nearest MIDI note
- `midiToNoteName` — MIDI note to name (e.g., "C4", "A#5")

### Frequency

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Hertz | Number | 20.0 | 20000.0 | clamps | Audible frequency range |

**Standard Pitches:**
- `a4` — 440 Hz (concert pitch)
- `middleC` — 261.63 Hz (C4)

### Cents and Semitones

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Semitones | Int | -127 | 127 | clamps | Pitch offset in half steps |
| Cents | Int | -100 | 100 | wraps | Pitch offset in cents (100 = 1 semitone) |

**Relationships:**
- 1 semitone = 100 cents = factor of 2^(1/12) ≈ 1.0595
- 1 octave = 12 semitones = 1200 cents = factor of 2

### Sample Rate

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| SampleRate | Int | 8000 | 192000 | clamps | Samples per second |

**Presets:**

| Name | Value | Use |
|------|-------|-----|
| `sr44100` | 44100 | CD quality |
| `sr48000` | 48000 | Professional video |
| `sr96000` | 96000 | High-resolution audio |
| `sr192000` | 192000 | Archival/mastering |

### Bit Depth

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| BitDepth | Int | 8 | 32 | clamps | Bits per sample |

**Presets:**

| Name | Value | Dynamic Range |
|------|-------|---------------|
| `bit16` | 16 | 96 dB (CD quality) |
| `bit24` | 24 | 144 dB (professional) |
| `bit32` | 32 | 192 dB (float) |

────────────────────────────────────────────────────────────────────────────────
                                                                // level // atoms
────────────────────────────────────────────────────────────────────────────────

## Amplitude and Level

Logarithmic and linear amplitude scales for audio processing.

### Decibel

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Decibel | Number | -120.0 | 0.0 | clamps | Relative amplitude (-120 = silence) |
| DecibelFS | Number | -60.0 | 12.0 | clamps | dB Full Scale (0 = digital max) |

**Presets:**
- `unity` — 0 dB (no change)
- `minus3dB` — Half power
- `minus6dB` — Half amplitude
- `minus12dB` — Quarter amplitude
- `minus20dB` — 0.1 linear

**Conversions:**
- `decibelToLinear` — dB to linear: `10^(dB/20)`
- `linearToDecibel` — Linear to dB: `20 × log₁₀(linear)`

### Linear Gain

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| LinearGain | Number | 0.0 | 1.0 | clamps | Linear amplitude multiplier |

**Presets:**
- `unity` — 1.0 (no change)
- `silence` — 0.0 (mute)

### Percent

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Percent | Number | 0.0 | 100.0 | clamps | User-facing percentage |

**Conversions:**
- `percentToLinear` — Percent to 0.0-1.0
- `linearToPercent` — 0.0-1.0 to percent

────────────────────────────────────────────────────────────────────────────────
                                                             // envelope // atoms
────────────────────────────────────────────────────────────────────────────────

## Envelopes

Classic synthesizer envelope models for amplitude and filter modulation.

### ADSR Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| AttackTime | Number | 0.0 | 10.0 | clamps | Time to reach peak (seconds) |
| DecayTime | Number | 0.0 | 10.0 | clamps | Time to fall to sustain (seconds) |
| SustainLevel | Number | 0.0 | 1.0 | clamps | Level held while pressed |
| ReleaseTime | Number | 0.0 | 30.0 | clamps | Time to fall to 0 after release |
| HoldTime | Number | 0.0 | 10.0 | clamps | Time at peak (AHDSR only) |

### ADSR Molecule

```purescript
type ADSR =
  { attack :: AttackTime
  , decay :: DecayTime
  , sustain :: SustainLevel
  , release :: ReleaseTime
  }
```

**Presets:**

| Name | A | D | S | R | Use |
|------|---|---|---|---|-----|
| `adsrDefault` | 0.01 | 0.1 | 0.7 | 0.3 | General purpose |
| `adsrSnappy` | 0.001 | 0.05 | 0.0 | 0.05 | Drums, percussion |
| `adsrPad` | 0.5 | 1.0 | 0.8 | 2.0 | Ambient pads, strings |
| `adsrPluck` | 0.001 | 0.3 | 0.0 | 0.1 | Plucked strings |

### AHDSR Molecule

Extended envelope with Hold stage between Attack and Decay.

```purescript
type AHDSR =
  { attack :: AttackTime
  , hold :: HoldTime
  , decay :: DecayTime
  , sustain :: SustainLevel
  , release :: ReleaseTime
  }
```

**Operations:**
- `totalAdsrTime` — Sum of A + D + R (sustain is indefinite)
- `scaleAdsrTimes` — Scale all times by factor (tempo sync)

────────────────────────────────────────────────────────────────────────────────
                                                           // oscillator // types
────────────────────────────────────────────────────────────────────────────────

## Oscillators

Waveform generators for audio synthesis.

### OscillatorType Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Sine` | `"Sine"` | Pure sine wave (fundamental only) |
| `Cosine` | `"Cosine"` | Cosine wave (90° phase shifted) |
| `Square` | `"Square"` | 50% duty cycle (odd harmonics) |
| `Pulse` | `"Pulse"` | Variable duty cycle (PWM) |
| `Sawtooth` | `"Sawtooth"` | Rising sawtooth (all harmonics) |
| `ReverseSaw` | `"Reverse Saw"` | Falling sawtooth |
| `Triangle` | `"Triangle"` | Triangle wave (odd harmonics, 12dB/oct rolloff) |
| `NoiseWhite` | `"White Noise"` | Equal energy per frequency |
| `NoisePink` | `"Pink Noise"` | -3dB/octave (equal energy per octave) |
| `NoiseBrown` | `"Brown Noise"` | -6dB/octave (Brownian motion) |
| `NoiseBlue` | `"Blue Noise"` | +3dB/octave |
| `NoiseViolet` | `"Violet Noise"` | +6dB/octave |
| `Sample` | `"Sample"` | Audio file playback |

### Oscillator Molecule

```purescript
type Oscillator =
  { oscType :: OscillatorType
  , frequency :: Hertz
  , phase :: Number           -- 0-360 degrees
  , gain :: LinearGain
  , pulseWidth :: Number      -- 0.0-1.0 duty cycle
  , sync :: Boolean           -- Hard sync to another oscillator
  }
```

**Presets:**
- `sineOsc` — Sine at A4 (440Hz)
- `squareOsc` — Square at A4
- `sawOsc` — Sawtooth at A4
- `triangleOsc` — Triangle at A4
- `whiteNoiseOsc` — White noise generator

────────────────────────────────────────────────────────────────────────────────
                                                               // filter // types
────────────────────────────────────────────────────────────────────────────────

## Filters

Subtractive synthesis filters for frequency shaping.

### FilterType Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `LowPass` | `"Low Pass"` | Passes frequencies below cutoff |
| `HighPass` | `"High Pass"` | Passes frequencies above cutoff |
| `BandPass` | `"Band Pass"` | Passes frequencies within band |
| `BandStop` | `"Band Stop"` | Attenuates frequencies within band |
| `Notch` | `"Notch"` | Narrow bandstop filter |
| `AllPass` | `"All Pass"` | Phase shift only |
| `Peak` | `"Peak"` | Parametric EQ boost/cut |
| `LowShelf` | `"Low Shelf"` | Boost/cut below frequency |
| `HighShelf` | `"High Shelf"` | Boost/cut above frequency |
| `Resonant` | `"Resonant"` | Resonant low-pass (classic synth) |

### FilterSlope Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Slope6dB` | `"6dB/oct"` | 1-pole, gentle |
| `Slope12dB` | `"12dB/oct"` | 2-pole, common |
| `Slope18dB` | `"18dB/oct"` | 3-pole |
| `Slope24dB` | `"24dB/oct"` | 4-pole, classic Moog |
| `Slope36dB` | `"36dB/oct"` | 6-pole, very steep |
| `Slope48dB` | `"48dB/oct"` | 8-pole, extreme |

### Filter Molecule

```purescript
type Filter =
  { filterType :: FilterType
  , cutoff :: CutoffFreq       -- 20-20000 Hz
  , resonance :: Resonance     -- 0.0-1.0
  , slope :: FilterSlope
  , envelope :: ADSR           -- Modulates cutoff
  , envelopeAmount :: Number   -- -1.0 to 1.0
  , keyTrack :: Number         -- 0.0-1.0 (cutoff tracks keyboard)
  }
```

**Presets:**
- `lowPassFilter` — 24dB/oct low-pass
- `highPassFilter` — 12dB/oct high-pass
- `bandPassFilter` — 12dB/oct band-pass

────────────────────────────────────────────────────────────────────────────────
                                                              // effects // types
────────────────────────────────────────────────────────────────────────────────

## Effects

Audio effects processors for mixing and sound design.

### Reverb

Simulates acoustic space reflections.

**ReverbAlgorithm Enum:**

| Constructor | Description |
|-------------|-------------|
| `Hall` | Large concert hall |
| `Room` | Medium room |
| `Chamber` | Small chamber |
| `Plate` | Plate reverb (metallic) |
| `Spring` | Spring reverb (vintage) |
| `Convolution` | Impulse response based |
| `Algorithmic` | Digital algorithm |

**Reverb Molecule:**

```purescript
type Reverb =
  { algorithm :: ReverbAlgorithm
  , roomSize :: Number       -- 0.0-1.0
  , damping :: Number        -- 0.0=bright, 1.0=dark
  , mix :: Mix               -- Wet/dry
  , preDelayMs :: Number     -- Pre-delay
  , diffusion :: Number      -- 0.0=sparse, 1.0=dense
  }
```

**Presets:** `reverbHall`, `reverbRoom`, `reverbPlate`, `reverbAmbient`

### Delay

Echo effect with feedback.

```purescript
type Delay =
  { timeMs :: Number         -- 0-5000ms
  , feedback :: Feedback     -- 0.0-1.0
  , mix :: Mix
  , filterCutoff :: CutoffFreq
  , pingPong :: Boolean      -- L/R alternating
  }
```

**Presets:** `delayQuarter` (500ms), `delayEighth` (250ms)

### Compressor

Dynamic range control.

```purescript
type Compressor =
  { thresholdDb :: Number    -- -60 to 0
  , ratio :: Number          -- 1:1 to 20:1
  , attackMs :: Number       -- 0.1-500ms
  , releaseMs :: Number      -- 10-2000ms
  , kneeDb :: Number         -- Soft knee width
  , makeupDb :: Number       -- Makeup gain
  }
```

**Presets:**

| Name | Threshold | Ratio | Use |
|------|-----------|-------|-----|
| `compressorGentle` | -12dB | 2:1 | Transparent bus |
| `compressorHard` | -20dB | 8:1 | Aggressive |
| `compressorVocal` | -18dB | 3:1 | Vocals |
| `compressorDrums` | -15dB | 6:1 | Drums, punch |
| `compressorMaster` | -8dB | 1.5:1 | Glue compression |

### EQ

Parametric equalizer.

```purescript
type EQBand =
  { frequency :: CutoffFreq
  , gainDb :: Number         -- -15 to +15
  , q :: Resonance           -- Bandwidth
  }

type EQ =
  { bands :: Array EQBand
  , outputGainDb :: Number
  }
```

**Presets:**
- `eq3Band` — Simple low/mid/high
- `eqPresence` — Clarity and air boost
- `eqDrumBus` — Punchy low-end
- `eqMaster` — Gentle final curve
- `eqTelephone` — Lo-fi bandpass

### Distortion

Harmonic saturation and clipping.

**DistortionType Enum:**

| Constructor | Description |
|-------------|-------------|
| `Overdrive` | Soft clipping (tube-like) |
| `Distort` | Hard clipping |
| `Fuzz` | Extreme clipping (transistor) |
| `BitCrush` | Bit depth reduction |
| `WaveShaper` | Custom waveshaping curve |

**Presets:** `distortionSubtle`

### Gate

Noise gate — cuts signal below threshold.

```purescript
type Gate =
  { thresholdDb :: Number    -- -60 to 0
  , attackMs :: Number
  , holdMs :: Number
  , releaseMs :: Number
  , rangeDb :: Number        -- Attenuation when closed
  }
```

**Presets:** `gateDefault`

### Limiter

Prevents signal from exceeding ceiling.

```purescript
type Limiter =
  { thresholdDb :: Number    -- -30 to 0
  , releaseMs :: Number      -- 1-500ms
  , ceilingDb :: Number      -- -6 to 0
  , lookaheadMs :: Number    -- True peak limiting
  }
```

**Presets:** `limiterDefault`, `limiterMaster`

────────────────────────────────────────────────────────────────────────────────
                                                              // spatial // atoms
────────────────────────────────────────────────────────────────────────────────

## Spatial Audio

Stereo and 3D positioning for immersive audio.

### Stereo Positioning

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Pan | Number | -1.0 | 1.0 | clamps | Left (-1) to right (+1) |
| Balance | Number | -100.0 | 100.0 | clamps | Percent-based pan |
| StereoWidth | Number | 0.0 | 2.0 | clamps | 0=mono, 1=stereo, 2=wide |

**Presets:**
- `panLeft` — -0.5 (moderate left)
- `panCenter` — 0.0
- `panRight` — +0.5 (moderate right)
- `panHardLeft` — -1.0
- `panHardRight` — +1.0

**Operations:**
- `invertPan` — Swap left/right
- `blendPan` — Interpolate between positions

### 3D Positioning

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Azimuth | Number | -180.0 | 180.0 | wraps | Horizontal angle (0=front) |
| Elevation | Number | -90.0 | 90.0 | clamps | Vertical angle (0=level) |
| AudioDistance | Number | 0.0 | 100.0 | clamps | Distance in meters |

**Azimuth positions:**
- `azimuthFront` — 0° (in front)
- `azimuthLeft` — -90°
- `azimuthRight` — +90°
- `azimuthBehind` — 180°

**Elevation positions:**
- `elevationLevel` — 0° (ear level)
- `elevationAbove` — +45°
- `elevationBelow` — -45°

────────────────────────────────────────────────────────────────────────────────
                                                            // temporal // atoms
────────────────────────────────────────────────────────────────────────────────

## Musical Time

Tempo, meter, and tick resolution for sequencing.

### Time Signature

| Constructor | Description |
|-------------|-------------|
| `TimeSignature Int Int` | Numerator / denominator |
| `TimeFree` | Rubato, no fixed meter |

**Presets:**

| Name | Value | Use |
|------|-------|-----|
| `time4_4` | 4/4 | Common time |
| `time3_4` | 3/4 | Waltz time |
| `time2_4` | 2/4 | March time |
| `time6_8` | 6/8 | Compound duple |
| `time5_4` | 5/4 | Odd meter |
| `time7_8` | 7/8 | Odd meter |
| `time9_8` | 9/8 | Compound triple |
| `time12_8` | 12/8 | Compound quadruple |
| `timeFree` | Free | Rubato |

### Tempo

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Tempo | Number | 20.0 | 400.0 | clamps | Beats per minute |

**Presets:**

| Name | BPM | Italian |
|------|-----|---------|
| `tempoLargo` | 50 | Very slow |
| `tempoAdagio` | 70 | Slow |
| `tempoAndante` | 90 | Walking pace |
| `tempoModerato` | 110 | Moderate |
| `tempoAllegro` | 140 | Fast |
| `tempoPresto` | 180 | Very fast |

**Conversions:**
- `beatsToMs` — Beats to milliseconds at tempo
- `msToBeats` — Milliseconds to beats at tempo

### Tick Resolution

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| TicksPerBeat | Int | 24 | 960 | clamps | PPQ (Pulses Per Quarter) |

**Presets:**
- `ppq96` — Basic resolution
- `ppq480` — Standard MIDI
- `ppq960` — High resolution

### Musical Position

```purescript
type MusicalPosition =
  { bar :: Int      -- 1-indexed
  , beat :: Int     -- 1-indexed
  , tick :: Int     -- 0-indexed
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                                 // note // types
────────────────────────────────────────────────────────────────────────────────

## Notes and Clips

MIDI note representation for sequencing.

### Note Molecule

```purescript
type Note =
  { pitch :: MidiNote        -- 0-127
  , velocity :: Velocity     -- 1-127
  , start :: TickPosition    -- When it starts
  , duration :: TickDuration -- How long
  , channel :: Channel       -- 1-16
  }
```

**Constructors:**
- `note` — Create note on channel 1
- `noteWithChannel` — Create note with explicit channel

**Operations:**
- `transposeNote` — Shift pitch by semitones
- `moveNote` — Move to new start position
- `stretchNote` — Change duration
- `setNoteVelocity` — Set velocity
- `scaleNoteVelocity` — Scale velocity by factor

**Predicates:**
- `noteOverlaps` — Two notes overlap in time?
- `noteContains` — Position within note?
- `noteAtPosition` — Note starts at position?

### Extended Note Properties

| Name | Type | Min | Max | Notes |
|------|------|-----|-----|-------|
| NoteProbability | Int | 0 | 100 | Chance of playing (generative) |
| VelocityRange | Int | 0 | 64 | ± humanization range |

### Note Collections

- `sortByStart` — Sort notes by start position
- `notesInRange` — Filter notes within tick range

────────────────────────────────────────────────────────────────────────────────
                                                               // source // files
────────────────────────────────────────────────────────────────────────────────

## Source Structure

```
src/Hydrogen/Schema/Audio/
├── Accessibility.purs    # Audio accessibility
├── Analysis.purs         # Audio analysis
├── Arrangement.purs      # Song arrangement
├── Automation.purs       # Parameter automation
├── Buffer.purs           # Audio buffers
├── Clip.purs             # Audio clips
├── Effects.purs          # Reverb, delay, compression, EQ
├── Envelope.purs         # ADSR/AHDSR envelopes
├── Filter.purs           # Filter types and slopes
├── Formant.purs          # Voice formants (leader)
├── Formant/              # Formant submodules
├── Format.purs           # Audio file formats
├── Frequency.purs        # Frequency/pitch (leader)
├── Frequency/            # Frequency submodules
├── Level.purs            # Decibel and linear gain
├── Meter.purs            # Audio metering
├── MIDI.purs             # MIDI protocol atoms
├── Mixer.purs            # Mixing primitives
├── Modulation.purs       # LFO and modulation
├── Note.purs             # MIDI notes
├── Oscillator.purs       # Waveform oscillators
├── Spatial.purs          # Stereo and 3D positioning
├── Speech.purs           # Speech synthesis (leader)
├── Speech/               # Speech submodules
├── Synthesis.purs        # Synthesis parameters
├── Tick.purs             # Tick timing
├── Time.purs             # Audio time
├── TimeSignature.purs    # Tempo and meter
├── Trigger.purs          # Audio triggers
├── Voice.purs            # Voice synthesis
└── VoiceCompounds.purs   # Voice compounds
```

**44 files total.**

────────────────────────────────────────────────────────────────────────────────
                                                        // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Design Philosophy

The Audio pillar provides **deterministic audio primitives** that match
industry standards exactly:

**MIDI 1.0 Compliance:**
Every MIDI atom uses exact protocol bounds — 7-bit values (0-127), 14-bit
pitch bend (-8192 to +8191), channels 1-16. When an agent sends `velocity 100`,
it maps to exactly the same MIDI byte across any implementation.

**Producer-Facing Values:**
Channel numbers are 1-16 (not 0-15 protocol values) because that's what
producers expect. BPM is bounded 20-400 because those are musical tempos.
Attack time caps at 10 seconds because longer is rarely useful.

**Effect Presets as Training Data:**
The preset molecules (`compressorVocal`, `reverbHall`, `eqDrumBus`) encode
25 years of mixing expertise. An AI agent can compose these presets or
learn from their parameter relationships.

**Why This Matters:**
At billion-agent scale, when one agent exports a MIDI sequence and another
imports it, every note, velocity, and timing must be identical. When an
agent describes "warm reverb with long tail," it can compose:
`reverbHall { roomSize: 0.9, damping: 0.4 }` and get deterministic results.

The Audio pillar gives AI a **precise vocabulary for sound** — not "make it
louder" but `linearGain 0.8` or `decibel (-3.0)`.

────────────────────────────────────────────────────────────────────────────────
