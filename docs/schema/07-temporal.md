━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                // 07 // temporal
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Temporal Pillar

Easing functions, spring physics, keyframes, and time representation.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Temporal/`
- **Files**: 39 modules
- **Key features**: Easing (30+ curves), spring physics, keyframes, duration,
  timecodes, calendar types

## Purpose

Temporal provides bounded, deterministic primitives for:
- Time units (nanoseconds to hours, frames at any FPS)
- Easing functions (cubic bezier, steps, procedural)
- Spring physics (damped harmonic oscillator)
- Animation structures (transitions, keyframes, sequences)
- Calendar and wall-clock time

────────────────────────────────────────────────────────────────────────────────
                                                             // time // atoms
────────────────────────────────────────────────────────────────────────────────

## Time Atoms

Core primitives for representing time spans.

### Duration

| Name | Type | Storage | Behavior | Notes |
|------|------|---------|----------|-------|
| Duration | Molecule | Milliseconds (Number) | clamps ≥ 0 | Unit-agnostic time span |

**Constructors:**
- `fromNanoseconds` / `ns` — Create from nanoseconds
- `fromMicroseconds` / `us` — Create from microseconds
- `fromMilliseconds` / `ms` — Create from milliseconds
- `fromSeconds` / `sec` — Create from seconds
- `fromMinutes` / `min` — Create from minutes
- `fromHours` / `hrs` — Create from hours
- `fromFrames` — Create from frame count at given FPS

**Operations:**
- `add`, `subtract` — Duration arithmetic (subtract clamps to zero)
- `scale` — Multiply duration by factor
- `toMilliseconds`, `toSeconds`, etc. — Unit conversion

**Presets:**
- `zero` / `instant` — 0ms
- `veryFast` — 100ms (micro-interactions)
- `fast` — 200ms (button feedback)
- `normal` — 300ms (standard transitions)
- `slow` — 500ms (emphasis)
- `verySlow` — 1000ms (dramatic reveals)

### Time Unit Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Nanosecond | Int | 0 | 999 | clamps | Within microsecond |
| Microsecond | Int | 0 | 999 | clamps | Within millisecond |
| Millisecond | Int | 0 | 999 | clamps | Within second |
| Second | Int | 0 | 59 | clamps | Within minute |
| Minute | Int | 0 | 59 | clamps | Within hour |
| Hour | Int | 0 | 23 | clamps | Within day |

### Frame-Based Time

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| FPS | Number | 1.0 | 240.0 | clamps | Frames per second |
| Frames | Int | 0 | 2147483647 | clamps | Frame count |

**FPS Presets:**
- `fps24` — 24 (cinema)
- `fps25` — 25 (PAL)
- `fps30` — 30 (NTSC)
- `fps60` — 60 (games, smooth UI)
- `fps120` — 120 (high refresh)

### Progress

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Progress | Number | 0.0 | 1.0 | clamps | Normalized animation progress |

**Presets:**
- `start` — 0.0
- `quarter` — 0.25
- `half` — 0.5
- `threeQuarters` — 0.75
- `complete` — 1.0

### Delay

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Delay | Duration | ≥ 0 | — | clamps | Time before animation starts |

**Presets:**
- `noDelay` — 0ms
- `shortDelay` — 100ms
- `normalDelay` — 300ms
- `longDelay` — 500ms

────────────────────────────────────────────────────────────────────────────────
                                                          // easing // overview
────────────────────────────────────────────────────────────────────────────────

## Easing

An easing function maps normalized time [0,1] to normalized progress [0,1].

### Easing Sum Type

| Constructor | Description |
|-------------|-------------|
| `Linear` | Constant velocity |
| `CubicBezier CubicBezierEasing` | CSS-compatible bezier curve |
| `Steps Steps StepPosition` | Discrete jumps |
| `Spring SpringConfig` | Physics-based (no CSS equivalent) |
| `Procedural ProceduralEasing` | Elastic/Bounce (no CSS equivalent) |

### BezierParam Atoms

Control points for cubic bezier curves.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| CubicX1 | Number | 0.0 | 1.0 | clamps | First control point X |
| CubicY1 | Number | -1.0 | 2.0 | clamps | First control point Y (can overshoot) |
| CubicX2 | Number | 0.0 | 1.0 | clamps | Second control point X |
| CubicY2 | Number | -1.0 | 2.0 | clamps | Second control point Y (can overshoot) |

**Note:** X values must be [0,1] for monotonic time. Y values can exceed [0,1] for overshoot effects.

### CubicBezierEasing

```purescript
type CubicBezierEasing =
  { x1 :: CubicX1
  , y1 :: CubicY1
  , x2 :: CubicX2
  , y2 :: CubicY2
  }
```

**CSS Standard Presets:**

| Name | Values (x1, y1, x2, y2) | Description |
|------|-------------------------|-------------|
| `linear` | (0, 0, 1, 1) | Constant velocity |
| `ease` | (0.25, 0.1, 0.25, 1.0) | Gentle acceleration/deceleration |
| `easeIn` | (0.42, 0, 1, 1) | Slow start |
| `easeOut` | (0, 0, 0.58, 1) | Slow end |
| `easeInOut` | (0.42, 0, 0.58, 1) | Slow start and end |

**Extended Power Presets:**

| Name | Curve Type | Description |
|------|------------|-------------|
| `easeInQuad` | t² | Gentle acceleration |
| `easeOutQuad` | 1-(1-t)² | Gentle deceleration |
| `easeInOutQuad` | Symmetric | Balanced |
| `easeInCubic` | t³ | Moderate acceleration |
| `easeOutCubic` | 1-(1-t)³ | Moderate deceleration |
| `easeInOutCubic` | Symmetric | Standard feel |
| `easeInQuart` | t⁴ | Strong acceleration |
| `easeOutQuart` | 1-(1-t)⁴ | Strong deceleration |
| `easeInOutQuart` | Symmetric | Dramatic |
| `easeInQuint` | t⁵ | Very strong acceleration |
| `easeOutQuint` | 1-(1-t)⁵ | Very strong deceleration |
| `easeInOutQuint` | Symmetric | Very dramatic |

**Exponential/Circular Presets:**

| Name | Description |
|------|-------------|
| `easeInExpo` | Exponential acceleration |
| `easeOutExpo` | Exponential deceleration |
| `easeInOutExpo` | Symmetric exponential |
| `easeInCirc` | Circular arc start |
| `easeOutCirc` | Circular arc end |
| `easeInOutCirc` | Symmetric circular |

**Overshoot Presets (easeInBack, easeOutBack, easeInOutBack):**
- Overshoot target then settle
- Y values exceed [0,1] range

**Sinusoidal Presets:**
- `easeInSine`, `easeOutSine`, `easeInOutSine` — Smooth sine-wave motion

### StepEasing

Discrete jumps for sprite animation, typewriter effects, etc.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Steps | Int | 1 | 100 | clamps | Number of discrete steps |

**StepPosition Enum:**

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `JumpStart` | `"jump-start"` | Jump at start of each step |
| `JumpEnd` | `"jump-end"` | Jump at end of each step |
| `JumpNone` | `"jump-none"` | No jump at start or end |
| `JumpBoth` | `"jump-both"` | Jump at both ends |

### ProceduralEasing

Easing functions that cannot be represented as cubic beziers.

**Why separate?** Cubic beziers are monotonic in time — they can't oscillate backwards. Elastic and bounce require procedural runtime evaluation.

**ElasticConfig:**

```purescript
type ElasticConfig =
  { amplitude :: Number  -- Peak overshoot (≥ 1.0)
  , period :: Number     -- Oscillation period (> 0, default 0.3)
  }
```

**BounceConfig:**

```purescript
type BounceConfig =
  { restitution :: Number  -- Energy retention per bounce (0-1)
  }
```

**ProceduralDirection Enum:**

| Constructor | Description |
|-------------|-------------|
| `In` | Effect at animation start |
| `Out` | Effect at animation end |
| `InOut` | Effect at both ends |

**Presets:**
- `easeInElastic`, `easeOutElastic`, `easeInOutElastic`
- `easeInBounce`, `easeOutBounce`, `easeInOutBounce`

**Physical Models:**

*Elastic* — Damped harmonic oscillator: `ẍ + 2ζω₀ẋ + ω₀²x = 0`
- ω₀ = natural frequency
- ζ = damping ratio (< 1 for oscillation)

*Bounce* — Inelastic collisions with coefficient of restitution < 1

────────────────────────────────────────────────────────────────────────────────
                                                          // spring // physics
────────────────────────────────────────────────────────────────────────────────

## Spring Physics

Physics-based animation using the damped harmonic oscillator model.

**The Spring Model:**
```
F = -kx - cv + ma
```

Where:
- **k** = spring stiffness (how "tight" the spring is)
- **c** = damping coefficient (how quickly oscillation fades)
- **m** = mass (affects acceleration response)
- **v** = velocity (current speed)
- **x** = displacement (distance from target)

### Spring Atoms

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Mass | Number | 0.01 | 1000.0 | clamps | Object inertia (typical: 0.1-10) |
| Stiffness | Number | 0.01 | 10000.0 | clamps | Spring constant k (typical: 100-500) |
| Damping | Number | 0.0 | 1000.0 | clamps | Friction coefficient c (typical: 10-50) |
| Velocity | Number | -10000.0 | 10000.0 | clamps | Initial velocity |
| RestDelta | Number | 0.0001 | 100.0 | clamps | Displacement threshold for "at rest" |
| RestSpeed | Number | 0.0001 | 100.0 | clamps | Velocity threshold for "at rest" |

### Damping Behavior

| Condition | Name | Behavior |
|-----------|------|----------|
| c = 0 | Undamped | Oscillates forever |
| c < critical | Underdamped | Overshoot with decay |
| c = critical | Critically damped | Fastest settle, no overshoot |
| c > critical | Overdamped | Slow settle, no overshoot |

**Critical Damping Formula:** `c_critical = 2 × √(mass × stiffness)`

### SpringConfig

```purescript
type SpringConfig =
  { mass :: Mass
  , stiffness :: Stiffness
  , damping :: Damping
  , velocity :: Velocity
  , restDelta :: RestDelta
  , restSpeed :: RestSpeed
  }
```

**Derived Properties:**
- `dampingRatio` — ζ = c / (2 × √(m × k))
- `naturalFrequency` — ω₀ = √(k / m)
- `isUnderdamped`, `isOverdamped`, `isCriticallyDamped` — Predicates

**Presets:**

| Name | Stiffness | Damping | Feel |
|------|-----------|---------|------|
| `gentle` | 120 | 14 | Slow, smooth, no bounce |
| `wobbly` | 180 | 12 | Fast, bouncy, playful |
| `stiff` | 210 | 20 | Snappy, responsive |
| `slow` | 280 | 60 | Dramatic, lazy |
| `molasses` | 280 | 120 | Very slow, syrupy |
| `noWobble` | 170 | 26 | Quick settle, minimal bounce |

────────────────────────────────────────────────────────────────────────────────
                                                        // animation // types
────────────────────────────────────────────────────────────────────────────────

## Animation Types

High-level structures for different animation techniques.

### Animation Sum Type

```purescript
data Animation a
  = Transition { target, duration, easing, delay }
  | KeyframeAnim { keyframes, duration, easing, delay, iteration, direction, persistence, playState }
  | SpringAnim { target, config, delay }
  | PhysicsAnim { velocity, friction, bounds }
```

| Constructor | Duration | Use Case |
|-------------|----------|----------|
| `Transition` | Fixed | Simple A → B with easing |
| `KeyframeAnim` | Fixed | Multi-step interpolation |
| `SpringAnim` | Dynamic | Natural, responsive motion |
| `PhysicsAnim` | Dynamic | Velocity-based (momentum, friction) |

### Keyframe

A value anchored at a specific progress point.

```purescript
data Keyframe a = Keyframe Progress a
```

**Constructors:**
- `keyframe :: Progress -> a -> Keyframe a`
- `at :: a -> Progress -> Keyframe a` — Reads naturally: `value \`at\` progress`

**Example:**
```purescript
[ 0.0 `at` 0.0      -- Start at 0
, 100.0 `at` 0.5    -- Peak at 50%
, 50.0 `at` 1.0     -- End at 50
]
```

### Sequence

Ordered list of animations that play in sequence.

```purescript
type Sequence a = Array (Animation a)
```

### AnimationComposition

How multiple animations combine.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Replace` | `"replace"` | New animation replaces current |
| `Add` | `"add"` | Values are summed |
| `Accumulate` | `"accumulate"` | Build on previous iterations |

### AnimationPhase

Current phase of animation lifecycle.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Idle` | `"idle"` | Not started |
| `Running` | `"running"` | Currently animating |
| `Paused` | `"paused"` | Temporarily stopped |
| `Finished` | `"finished"` | Completed |

### ScrollAnimation

Animation driven by scroll position.

```purescript
type ScrollAnimation =
  { startOffset :: Number   -- Scroll position to start (px)
  , endOffset :: Number     -- Scroll position to end (px)
  , easing :: Easing
  }
```

### Presence

Mount/unmount animation states for components.

| Constructor | Description |
|-------------|-------------|
| `Present` | Fully visible |
| `Entering` | Animating in |
| `Exiting` | Animating out |
| `Absent` | Unmounted |

### Debounce

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Debounce | Duration | ≥ 0 | — | clamps | Wait time before firing |

**Presets:**
- `instantDebounce` — 0ms
- `shortDebounce` — 150ms
- `normalDebounce` — 300ms
- `longDebounce` — 500ms

────────────────────────────────────────────────────────────────────────────────
                                                          // playback // control
────────────────────────────────────────────────────────────────────────────────

## Playback Control

Parameters controlling animation playback behavior.

### PlayState

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Playing` | `"running"` | Animation is active |
| `Paused` | `"paused"` | Animation is frozen |

### Direction

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Normal` | `"normal"` | Forward (0 → 1) |
| `Reverse` | `"reverse"` | Backward (1 → 0) |
| `Alternate` | `"alternate"` | Forward, then backward |
| `AlternateReverse` | `"alternate-reverse"` | Backward, then forward |

### Iteration

How many times to repeat.

| Constructor | Description |
|-------------|-------------|
| `Count Int` | Specific number (≥ 1) |
| `Infinite` | Loop forever |

**Presets:**
- `once` — Count 1
- `twice` — Count 2
- `infinite` — Loop forever

### Persistence

What happens when animation completes.

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `None` | `"none"` | Revert to initial state |
| `Forwards` | `"forwards"` | Stay at final value |
| `Backwards` | `"backwards"` | Apply initial value during delay |
| `Both` | `"both"` | Forwards + Backwards |

────────────────────────────────────────────────────────────────────────────────
                                                            // calendar // time
────────────────────────────────────────────────────────────────────────────────

## Calendar Time

Wall-clock and calendar representations for scheduling, events, and timestamps.

### DayOfWeek

Bounded enumeration of seven days.

| Constructor | ISO 8601 | US Index | Description |
|-------------|----------|----------|-------------|
| `Monday` | 1 | 1 | First weekday |
| `Tuesday` | 2 | 2 | Second weekday |
| `Wednesday` | 3 | 3 | Third weekday |
| `Thursday` | 4 | 4 | Fourth weekday |
| `Friday` | 5 | 5 | Fifth weekday |
| `Saturday` | 6 | 6 | Weekend |
| `Sunday` | 7 | 0 | Weekend (US first day) |

**Name Formats:**
- `name` — Full: "Monday", "Tuesday", ...
- `nameShort` — Abbreviated: "Mon", "Tue", ...
- `nameLetter` — Single: "M", "T", "W", ...

**Predicates:** `isWeekday`, `isWeekend`

**Navigation:** `next`, `prev`, `addDays`

**Collections:** `allDays`, `weekdays`, `weekend`, `allDaysFromMonday`, `allDaysFromSunday`

### Hour / Minute / Second

| Name | Type | Min | Max | Behavior |
|------|------|-----|-----|----------|
| Hour | Int | 0 | 23 | clamps |
| Minute | Int | 0 | 59 | clamps |
| Second | Int | 0 | 59 | clamps |

### TimeOfDay

```purescript
type TimeOfDay =
  { hour :: Hour
  , minute :: Minute
  , second :: Second
  }
```

### Date

```purescript
type Date =
  { year :: Int
  , month :: Int     -- 1-12
  , day :: Int       -- 1-31
  }
```

### DateTime

```purescript
type DateTime =
  { date :: Date
  , time :: TimeOfDay
  , timezone :: Timezone
  }
```

### Timezone

Timezone representation (IANA names or UTC offsets).

### TimeRange

A span between two points in time.

```purescript
type TimeRange =
  { start :: DateTime
  , end :: DateTime
  }
```

### Timecode (SMPTE)

Video/animation timecode format: `HH:MM:SS:FF`

| Field | Range | Description |
|-------|-------|-------------|
| HH | 00-99 | Hours |
| MM | 00-59 | Minutes |
| SS | 00-59 | Seconds |
| FF | 00-FPS | Frames |

**Presets:**
- `emptyTimecode` — "00:00:00:00"

### CalendarDuration

Human-scale duration for scheduling.

```purescript
type CalendarDuration =
  { years :: Int
  , months :: Int
  , days :: Int
  , hours :: Int
  , minutes :: Int
  , seconds :: Int
  }
```

**Note:** Unlike `Duration`, CalendarDuration handles variable-length units (months vary in days, leap years, etc.).

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

## Source Files

```
src/Hydrogen/Schema/Temporal/
├── Animation.purs
├── AnimationComposition.purs
├── AnimationPhase.purs
├── BezierParam.purs
├── CalendarDuration.purs
├── CubicBezierEasing.purs
├── Date.purs
├── DateTime.purs
├── DayOfWeek.purs
├── Debounce.purs
├── Delay.purs
├── Direction.purs
├── Duration.purs
├── Easing.purs
├── FPS.purs
├── Frames.purs
├── Hour.purs
├── Iteration.purs
├── Keyframe.purs
├── Microsecond.purs
├── Millisecond.purs
├── Minute.purs
├── Nanosecond.purs
├── Persistence.purs
├── PlayState.purs
├── Presence.purs
├── ProceduralEasing.purs
├── Progress.purs
├── ScrollAnimation.purs
├── Second.purs
├── Sequence.purs
├── Spring.purs
├── SpringConfig.purs
├── StepEasing.purs
├── Timecode.purs
├── Timeline.purs
├── TimeOfDay.purs
├── TimeRange.purs
└── Timezone.purs
```

39 files.

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Temporal Matters

Time is the axis along which all UI change occurs.

**Every interaction involves time:**
- Button press → feedback animation (200ms ease-out)
- Page load → content fade-in (300ms with stagger)
- Scroll → parallax motion (spring physics)
- Drag → momentum with friction decay

**The problem with CSS animations:**
- Limited to cubic bezier (no elastic, no bounce)
- No spring physics (dynamic duration)
- Fixed duration (can't respond to user input)
- No coordination between elements

**What Temporal provides:**

1. **Unified Easing** — One type covers cubic bezier, steps, springs, and procedural.
   An agent specifies `easeOutElastic` without knowing it requires runtime evaluation.

2. **Physics-Based Motion** — Springs have no fixed duration. They settle when
   the physics says so. This creates natural, responsive feel that beziers can't match.

3. **Deterministic Keyframes** — Same keyframe sequence = same animation.
   Agents can compose multi-step animations algebraically.

4. **Frame-Accurate Time** — Duration converts to frames at any FPS.
   24fps cinema, 60fps UI, 120fps VR — same primitives, correct frames.

**At billion-agent scale:**

When an agent says "animate this button with a bouncy spring feel," the Temporal
primitives give them:
- `springConfig: wobbly` — Known stiffness/damping values
- Deterministic settling behavior
- No ambiguity about what "bouncy" means

When another agent needs to synchronize a sound effect with that bounce, they
query the spring's settling time. Same parameters = same timing = perfect sync.

**Time is not optional.** Every UI framework needs temporal primitives.
Hydrogen makes them bounded, deterministic, and composable.

────────────────────────────────────────────────────────────────────────────────
