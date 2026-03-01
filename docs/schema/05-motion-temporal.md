━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // 05 // motion // temporal
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Motion: Temporal Primitives

Core time measurement and coordination for motion graphics.

────────────────────────────────────────────────────────────────────────────────
                                                                       // atoms
────────────────────────────────────────────────────────────────────────────────

## Timecode.purs (446 lines)

SMPTE timecode representation for professional video/motion graphics.

**Types:**
- `Timecode` — Stores total frame count with frame rate and drop-frame flag
- `TimecodeComponents` — Display components { hours, minutes, seconds, frames }

**Constructors:**
- `timecode` — Create from hour, minute, second, frame components
- `fromFrames` — Create from raw frame count
- `fromSeconds` — Create from seconds
- `zero` — Zero timecode (00:00:00:00)

**Operations:**
- `addFrames`, `subtractFrames` — Frame arithmetic
- `addTimecode`, `subtractTimecode` — Timecode arithmetic
- `parse` — Parse SMPTE string ("HH:MM:SS:FF" or "HH:MM:SS;FF" for drop-frame)
- `format`, `formatCompact` — Format for display
- `toFrames`, `toSeconds`, `toComponents` — Conversion

**Queries:**
- `isDropFrame` — Uses drop-frame format?
- `frameRate` — Get frame rate
- `totalFrames` — Get total frames
- `isValid`, `normalize` — Validation

**Drop-Frame:**
NTSC runs at 29.97fps. Drop-frame skips frames 0,1 at minute start (except 10th minute)
to sync timecode with wall-clock time. Uses semicolon separator: `01:02:03;04`

## TimeRange.purs (372 lines)

Time range (in/out points) for motion graphics.

**Types:**
- `TimeRange` — { inPoint :: Frames, outPoint :: Frames }

**Invariants:** inPoint <= outPoint, both >= 0 (enforced by constructors)

**Constructors:**
- `timeRange` — From in/out points (auto-ordered)
- `fromDuration` — From start point and duration
- `empty` — Zero-length at frame 0
- `infinite` — Large bounded range (avoids actual infinity)

**Accessors:**
- `inPoint`, `outPoint`, `duration`

**Predicates:**
- `contains` — Frame within range?
- `containsRange` — Range fully contains another?
- `overlaps` — Two ranges overlap?
- `isEmpty` — Zero duration?

**Operations:**
- `setInPoint`, `setOutPoint` — Modify points (with clamping)
- `shift` — Move entire range by offset
- `scale` — Scale duration from in point
- `trim` — Clamp to bounds
- `expand` — Add to both ends
- `intersect` — Get overlap (Maybe)
- `union` — Smallest containing range

────────────────────────────────────────────────────────────────────────────────
                                                                   // molecules
───────────────────────────��────────────────────────────────────────────────────

## Timeline.purs (663 lines)

Frame-based animation timing and layer coordination.

**Types:**
- `Timeline` — { frameRate, totalFrames, layers, looping, pingPong }
- `TimelineLayer` — { name, startFrame, endFrame, inPoint, outPoint, timeRemap, enabled }
- `FrameRate` — Number (fps)

**Frame Rate Presets:**
- `fps24` (film), `fps25` (PAL), `fps30` (NTSC)
- `fps48` (HFR film), `fps60` (games), `fps120` (high refresh)
- `customFps` — Custom rate (clamped 1-240)

**Construction:**
- `timeline` — Create with fps and frame count
- `emptyTimeline` — Default empty
- `fromDuration` — From fps and seconds

**Layer Management:**
- `addLayer`, `removeLayer`, `getLayer`
- `setLayerTiming`, `setLayerTimeRemap`
- `getLayerByIndex`, `layerCount`, `hasLayer`

**Frame Calculation:**
- `globalToLocal` — Global frame to layer-local frame (accounts for offset + time remap)
- `localToGlobal` — Inverse transformation
- `layerTimeAtFrame`, `frameAtLayerTime` — Named access
- `isLayerActiveAtFrame` — Layer visible at frame?

**Time Conversion:**
- `frameToSeconds`, `secondsToFrame`
- `progressAtFrame`, `frameAtProgress` — 0-1 progress

**Playback Modes:**
- `clampFrame` — Clamp to timeline bounds
- `wrapFrame` — Loop playback
- `pingPongFrame` — Forward-backward playback

**Batch Operations:**
- `activeLayersAtFrame` — All active layers
- `layerTimesAtFrame` — Local times for all active layers
- `evaluateFrame` — Complete render state { frame, time, progress, layers }

**Advanced:**
- `reverseTimeline` — Reverse playback direction
- `clearTimeRemap`, `isLayerRemapped`
- `isFramePlayable`, `seekToLayerFrame`

## TimeRemap/ (6 files, ~1,059 lines)

Variable speed, time remapping, and ramps for animation.
Leader module re-exports from submodules.

**TimeRemap/Types.purs (99 lines):**

- `RemapMode` — Enumeration:
  - `LinearRemap` — Constant speed factor
  - `CurveRemap Easing` — Speed follows easing curve
  - `KeyframeRemap` — Speed defined by keyframes
  - `FreezeRemap Number` — Frozen at specific time
  - `PingPongRemap` — Forward then backward
  - `LoopRemap Number` — Loop every n frames

- `SpeedKeyframe` — { frame, speed, easing }
  - speed = 1.0 normal, 0.5 half speed, 2.0 double, 0.0 freeze

- `TimeRemap` — { mode, speedFactor, startSpeed, endSpeed, originalDuration, keyframes }

**TimeRemap/Construction.purs (174 lines):**

- `identity` — No change (1x speed)
- `uniformSpeed` — Constant speed change (0.5 = slow-mo, 2.0 = fast-forward)
- `reverse` — Backward playback (-1x)
- `freezeAt` — Hold specific frame
- `timeStretch` — Uniform speed to achieve target duration
- `speedRamp` — Custom easing from start to end speed
- `speedRampIn` — Slow start (ease-in)
- `speedRampOut` — Slow end (ease-out)
- `speedRampInOut` — Slow start and end
- `fromSpeedKeyframes` — Build from keyframe array
- `addSpeedKeyframe`, `removeSpeedKeyframe`

**TimeRemap/Evaluation.purs (257 lines):**

- `apply` — Remap input frame to output frame
- `applyInverse` — Inverse: find input from output (Newton-Raphson for curves)
- `applyToProgress` — Remap normalized 0-1 progress
- `speedAt` — Speed at specific frame
- `derivativeAt` — Rate of time change (alias for speedAt)
- `remappedDuration`, `originalDuration`, `setOriginalDuration`

**TimeRemap/Composition.purs (260 lines):**

Composition:
- `compose` — Apply first, then second (multiply speeds)
- `chain` — Sequential (first plays, then second)
- `blend` — Weighted blend (0.0 = first, 1.0 = second)

Presets:
- `slowMotion` — 50% speed
- `fastForward` — 2x speed
- `pingPong` — Forward then reverse
- `loop` — Loop every n frames
- `hold` — Freeze at end
- `bounce` — Ease in-out with brief hold

Analysis:
- `averageSpeed`, `minSpeed`, `maxSpeed`
- `isConstantSpeed`
- `sampleRemap`, `sampleSpeed` — Sample at n evenly-spaced points

**TimeRemap/Utilities.purs (186 lines):**

- `defaultSpeed` — 1.0 (normal)
- `isValidRemap` — Duration positive, speeds reasonable
- `normalizeRemap` — Scale to average speed 1.0
- `speedKeyframe` — Create keyframe with linear easing
- `combineRemaps` — Average multiple remaps
- `speedMagnitude` — 2D speed vector magnitude
- `hasSpeedChange` — Not identity?

**TimeRemap/Internal.purs (243 lines):**

Internal helpers (not re-exported):
- Numeric: `clamp01`, `clampNumber`, `floorNum`, `floorInt`, `mod`, `epsilon`, `infinity`
- Array: `buildArray`, `buildIntArray`
- Integration: `integrateSpeed`, `integrateKeyframes` (trapezoidal approximation)
- Keyframes: `speedAtKeyframes`, `findSurroundingKeyframes`, `sortKeyframes`

────────────────────────────────────────────────────────────────────────────────
                                                                // source files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Motion/
├── Timecode.purs
├── Timeline.purs
├── TimeRange.purs
└── TimeRemap/
    ├── Types.purs
    ├── Construction.purs
    ├── Evaluation.purs
    ├── Composition.purs
    ├── Utilities.purs
    └── Internal.purs
```

~2,959 lines total.

────────────────────────────────────────────────────────────────────────────────
