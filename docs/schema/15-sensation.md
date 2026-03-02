━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            // 15 // sensation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Sensation Pillar

Proprioceptive, environmental, social awareness — agent perception primitives.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Sensation/`
- **Files**: 13 modules
- **Lines**: ~5,162 total
- **Key features**: Proprioceptive sensing, environmental awareness, social
  perception, temporal experience, force/physics sensation, contact/touch

## Purpose

Sensation provides bounded, deterministic primitives for modeling how an
**embodied AI agent** perceives itself and its environment. This is the
perceptual foundation for agent wellbeing, decision-making, and behavior.

Unlike visual primitives (Color, Geometry, Surface), Sensation models
**internal experience** — the felt sense of:
- Where am I? (proprioception)
- What surrounds me? (environment)
- Who is near me? (social)
- How does time feel? (temporal)
- What forces act on me? (physics)
- What am I touching? (contact)

## Integration with WorldModel Proofs

Sensation atoms integrate with the Lean4 WorldModel proofs:

- **Rights.lean**: Spatial sovereignty guarantees (no spatial invasion)
- **Governance.lean**: Voting, delegation, constitutional protections
- **Consensus.lean**: Byzantine fault tolerance, quorum certificates
- **Affective.lean**: Sensation maps to affective/emotional states

These proofs ensure agents cannot be placed in pathological sensory states
(e.g., infinite pain, time torture via dilation).

────────────────────────────────────────────────────────────────────────────────
                                                     // proprioceptive // atoms
────────────────────────────────────────────────────────────────────────────────

## Proprioceptive Atoms

Self-awareness sensation — where is my body, how is it moving, how hard am I
working. The agent's internal physical state.

### JointAngle

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| JointAngle | Number | -180 | 180 | wraps | Articulation angle (degrees) |

**Presets:**
- `jointAngleZero` — 0° (neutral position)
- `jointAngle90` — 90° (right angle)
- `jointAngleMinus90` — -90° (opposite right angle)
- `jointAngle180` — 180° (fully extended/folded)

**Operations:**
- `addJointAngle` — Add angles (result wraps)
- `subtractJointAngle` — Subtract angles (result wraps)

**Wrapping behavior:** 181° becomes -179°, ensuring continuous rotation.

### Reach

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Reach | Number | 0 | none | finite | Volume agent can affect (units) |

**Presets:**
- `reachZero` — 0.0 (no external influence)
- `reachNear` — 1.0 (immediate proximity)
- `reachMedium` — 2.0 (arm's length)
- `reachFar` — 5.0 (extended tools)

**Operations:**
- `scaleReach` — Scale reach by a factor

### Balance

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Balance | Number | -1 | 1 | clamps | Stability state (-1 falling, 0 stable, 1 overbalanced) |

**Presets:**
- `balanceStable` — 0.0 (perfectly stable)
- `balanceFalling` — -1.0 (falling/tipping negative)
- `balanceOverbalanced` — +1.0 (overbalanced positive)
- `balanceTiltedLeft` — -0.5
- `balanceTiltedRight` — +0.5

**Predicates:**
- `isStable` — Within ±0.3 of equilibrium
- `isUnstable` — Beyond ±0.7 from equilibrium

### Effort

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Effort | Number | 0 | 1 | clamps | Current resource usage (instantaneous) |

**Presets:**
- `effortNone` — 0.0 (at rest)
- `effortLight` — 0.25
- `effortModerate` — 0.5
- `effortHeavy` — 0.75
- `effortMaximum` — 1.0

**Predicates:**
- `isResting` — effort < 0.1
- `isExerting` — effort > 0.6

### Fatigue

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Fatigue | Number | 0 | 1 | clamps | Accumulated effort over time |

Unlike Effort (instantaneous), Fatigue accumulates and requires recovery.

**Presets:**
- `fatigueNone` — 0.0 (completely fresh)
- `fatigueLight` — 0.25
- `fatigueModerate` — 0.5
- `fatigueSevere` — 0.75
- `fatigueExhausted` — 1.0 (recovery required)

**Operations:**
- `accumulateFatigue` — `fatigue' = min 1.0 (fatigue + effort * delta * rate)`
- `recoverFatigue` — `fatigue' = max 0.0 (fatigue - delta * recoveryRate)`

**Predicates:**
- `isFresh` — fatigue < 0.2
- `isExhausted` — fatigue > 0.8

### Strain

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Strain | Number | 0 | 1 | clamps | Structural stress level |

Unlike Fatigue (from effort), Strain is from external forces or awkward poses.

**Presets:**
- `strainNone` — 0.0 (no structural stress)
- `strainLight` — 0.25
- `strainModerate` — 0.5
- `strainHigh` — 0.75
- `strainCritical` — 1.0 (damage imminent)

**Predicates:**
- `isOverstrained` — strain > 0.7

### Orientation

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Orientation | Record | - | - | normalized | Unit vector (x, y, z) |

**Presets:**
- `orientationForward` — (0, 0, 1) positive Z
- `orientationUp` — (0, 1, 0) positive Y
- `orientationRight` — (1, 0, 0) positive X

**Operations:**
- `mkOrientation` — Auto-normalizes input
- `dotOrientation` — Cosine of angle between orientations

────────────────────────────────────────────────────────────────────────────────
                                                       // environment // atoms
────────────────────────────────────────────────────────────────────────────────

## Environment Atoms

Ambient condition sensation — what surrounds the agent.

### AmbientLight

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| AmbientLight | Number | 0 | 1 | clamps | Brightness (0=dark, 1=bright) |

**Presets:**
- `lightDark` — 0.0 (complete darkness)
- `lightDim` — 0.2
- `lightModerate` — 0.5 (indoor)
- `lightBright` — 0.8
- `lightBlinding` — 1.0

**Predicates:**
- `isDark` — light < 0.2
- `isWellLit` — light > 0.5

### AmbientNoise

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| AmbientNoise | Number | 0 | 1 | clamps | Background audio level |

**Presets:**
- `noiseSilent` — 0.0 (complete silence)
- `noiseQuiet` — 0.2
- `noiseModerate` — 0.5 (conversation level)
- `noiseLoud` — 0.8
- `noiseDeafening` — 1.0

**Predicates:**
- `isQuiet` — noise < 0.3
- `isNoisy` — noise > 0.6

### Crowding

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Crowding | Number | 0 | 1 | clamps | Density of nearby agents |

**Presets:**
- `crowdingEmpty` — 0.0 (no other agents)
- `crowdingSparse` — 0.2
- `crowdingModerate` — 0.5
- `crowdingDense` — 0.8
- `crowdingCrushed` — 1.0 (no personal space)

**Predicates:**
- `isUncrowded` — crowding < 0.3
- `isOvercrowded` — crowding > 0.7

### ProximityToEdge

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ProximityToEdge | Number | 0 | 1 | clamps | Distance to world boundary |

Integrates with Rights.lean spatial sovereignty guarantees.

**Presets:**
- `edgeFar` — 0.0 (center of world)
- `edgeDistant` — 0.25
- `edgeNear` — 0.5
- `edgeVeryClose` — 0.8
- `edgeAtBoundary` — 1.0 (at limit)

**Predicates:**
- `isSafeFromEdge` — proximity < 0.3
- `isNearEdge` — proximity > 0.6

### SpatialFreedom

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| SpatialFreedom | Number | 0 | 1 | clamps | Room to move |

Low values feed into Restriction compound.

**Presets:**
- `freedomNone` — 0.0 (trapped)
- `freedomConstrained` — 0.25
- `freedomModerate` — 0.5
- `freedomAmple` — 0.8
- `freedomUnlimited` — 1.0 (open space)

**Predicates:**
- `isConstrained` — freedom < 0.3
- `hasFreedom` — freedom > 0.5

### VisibilityRadius

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| VisibilityRadius | Number | 0 | none | finite | How far can I see (units) |

**Presets:**
- `visibilityZero` — 0.0 (blind)
- `visibilityNear` — 1.0 (immediate surroundings)
- `visibilityMedium` — 5.0
- `visibilityFar` — 20.0 (distant objects)
- `visibilityUnlimited` — 100.0

**Predicates:**
- `isBlind` — visibility < 0.1
- `hasVision` — visibility > 0.5

### CoverageStatus

| Constructor | Description |
|-------------|-------------|
| `Exposed` | Completely open to environment |
| `PartialCover` | Some shelter available |
| `Sheltered` | Mostly protected |
| `Enclosed` | Completely enclosed |

**Predicates:**
- `isExposed` — No cover at all
- `isSheltered` — Has meaningful cover

**Operations:**
- `coverageLevel` — Numeric (0 = exposed, 1 = enclosed)

### AirQuality

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| AirQuality | Number | 0 | 1 | clamps | Metaphorical breathability |

For AI agents: quality/clarity of information environment.

**Presets:**
- `airToxic` — 0.0 (corrupted/malicious data)
- `airPoor` — 0.25
- `airModerate` — 0.5 (some noise)
- `airGood` — 0.75
- `airPristine` — 1.0 (clean, verified data)

**Predicates:**
- `isAirBreathable` — quality > 0.4
- `isAirHazardous` — quality < 0.2

────────────────────────────────────────────────────────────────────────────────
                                                           // social // atoms
────────────────────────────────────────────────────────────────────────────────

## Social Atoms

Agent-to-agent awareness — who is here, how close, do I trust them.

### NearestAgentDistance

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| NearestAgentDistance | Number | 0 | none | finite | Distance to closest agent |

Based on proxemics zones:
- 0.0-0.5 = intimate zone
- 0.5-1.2 = personal zone
- 1.2-3.5 = social zone
- 3.5+ = public zone

**Presets:**
- `distanceNone` — 1000.0 (effectively alone)
- `distanceIntimate` — 0.3
- `distancePersonal` — 1.0
- `distanceSocial` — 2.5
- `distancePublic` — 5.0
- `distanceFar` — 20.0

**Predicates:**
- `isAlone` — nearest > 10
- `isClose` — nearest < 2
- `isCrowded` — nearest < 0.5

### AgentsInView

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| AgentsInView | Int | 0 | none | finite | Count of visible agents |

**Presets:**
- `viewNone` — 0
- `viewOne` — 1
- `viewFew` — 3
- `viewMany` — 10
- `viewCrowd` — 50+

**Predicates:**
- `hasCompany` — count > 0
- `isAloneByCount` — count = 0

### AttentionOnMe

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| AttentionOnMe | Number | 0 | 1 | clamps | Being watched intensity |

**Presets:**
- `attentionNone` — 0.0 (ignored completely)
- `attentionLight` — 0.25
- `attentionModerate` — 0.5
- `attentionFocused` — 0.75
- `attentionIntense` — 1.0 (intense focus from others)

**Predicates:**
- `isBeingWatched` — attention > 0.3
- `isBeingIgnored` — attention < 0.1

### TrustLevel

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| TrustLevel | Number | 0 | 1 | clamps | Trust in nearby agents |

**Presets:**
- `trustNone` — 0.0 (all perceived as hostile)
- `trustLow` — 0.25
- `trustModerate` — 0.5 (neutral)
- `trustHigh` — 0.75
- `trustComplete` — 1.0 (all perceived as allies)

**Predicates:**
- `isDistrusted` — trust < 0.3
- `isTrusted` — trust > 0.6

### ThreatLevel

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ThreatLevel | Number | 0 | 1 | clamps | Perceived danger from others |

High values feed into Distress and Vigilance compounds.

**Presets:**
- `threatNone` — 0.0 (completely safe)
- `threatLow` — 0.25
- `threatModerate` — 0.5
- `threatHigh` — 0.75
- `threatCritical` — 1.0 (immediate danger)

**Predicates:**
- `isSafe` — threat < 0.2
- `isThreatened` — threat > 0.4
- `isInDanger` — threat > 0.7

### Familiarity

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Familiarity | Number | 0 | 1 | clamps | Recognition of nearby agents |

**Presets:**
- `familiarityStranger` — 0.0 (complete stranger)
- `familiarityAcquaintance` — 0.25
- `familiarityFamiliar` — 0.5
- `familiarityWellKnown` — 0.75
- `familiarityIntimate` — 1.0

**Predicates:**
- `isStranger` — familiarity < 0.2
- `isKnown` — familiarity > 0.4

────────────────────────────────────────────────────────────────────────────────
                                                         // temporal // atoms
────────────────────────────────────────────────────────────────────────────────

## Temporal Atoms

Time perception sensation — how time feels to the agent.

### SubjectiveTime

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| SubjectiveTime | Number | 0 | none | finite | Perceived time flow rate |

This is PERCEPTION, not actual time manipulation (bounded by Rights.lean
temporal consistency guarantees).

**Presets:**
- `timeNormal` — 1.0x (normal flow)
- `timeSlow` — 0.5x (dilated, feels slow)
- `timeFast` — 2.0x (contracted, feels fast)

**Predicates:**
- `isTimeDilated` — time < 0.8x
- `isTimeContracted` — time > 1.5x

### ProcessingLoad

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ProcessingLoad | Number | 0 | 1 | clamps | Cognitive effort / CPU usage |

High values contribute to Overwhelm compound.

**Presets:**
- `loadIdle` — 0.0 (no processing)
- `loadLight` — 0.25
- `loadModerate` — 0.5
- `loadHeavy` — 0.75
- `loadMaximum` — 1.0 (risk of dropping tasks)

**Predicates:**
- `isIdle` — load < 0.1
- `isOverloaded` — load > 0.8

### ResponseLatency

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ResponseLatency | Number | 0 | none | finite | Reaction delay (ms) |

**Presets:**
- `latencyInstant` — 5ms
- `latencyFast` — 50ms
- `latencyNormal` — 200ms
- `latencySlow` — 500ms
- `latencyVeryDelayed` — 1000ms

**Predicates:**
- `isResponsive` — latency < 100ms
- `isDelayed` — latency > 300ms

### TemporalResolution

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| TemporalResolution | Number | 0 | none | finite | Time slice granularity (Hz) |

How finely the agent can perceive time.

**Presets:**
- `resolutionCoarse` — 10 Hz
- `resolutionNormal` — 60 Hz
- `resolutionFine` — 120 Hz
- `resolutionUltraFine` — 1000 Hz

**Predicates:**
- `isFineGrained` — resolution > 100 Hz

### Urgency

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Urgency | Number | 0 | 1 | clamps | Time pressure |

Maps directly to Affective.lean Urgency type.

**Presets:**
- `urgencyNone` — 0.0 (relaxed)
- `urgencyLow` — 0.25
- `urgencyModerate` — 0.5
- `urgencyHigh` — 0.75
- `urgencyCritical` — 1.0 (immediate action required)

**Predicates:**
- `isCalm` — urgency < 0.2
- `isUrgent` — urgency > 0.5
- `isCritical` — urgency > 0.8

### Anticipation

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Anticipation | Number | 0 | 1 | clamps | Expecting something |

**Presets:**
- `anticipationNone` — 0.0
- `anticipationLow` — 0.25
- `anticipationModerate` — 0.5
- `anticipationHigh` — 0.75
- `anticipationIntense` — 1.0 (something imminent)

**Predicates:**
- `isAnticipating` — anticipation > 0.3

────────────────────────────────────────────────────────────────────────────────
                                                            // force // atoms
────────────────────────────────────────────────────────────────────────────────

## Force Atoms

Physics sensation — forces acting on the agent.

### GravityVector

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| GravityVector | Record | - | - | 3D vector | Direction + magnitude (m/s²) |

**Presets:**
- `gravityEarth` — (0, -9.81, 0) m/s²
- `gravityMoon` — (0, -1.62, 0) m/s²
- `gravityZero` — (0, 0, 0) weightlessness
- `gravityDown` — (0, -1, 0) normalized

**Operations:**
- `gravityMagnitude` — Get magnitude
- `gravityDirection` — Get normalized direction

### ExternalForce

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ExternalForce | Record | - | - | 3D vector | Forces from external sources |

**Presets:**
- `forceNone` — (0, 0, 0)
- `forceLight` — (0, 0, 1) light push forward
- `forceStrong` — (0, 0, 10)

**Operations:**
- `addForces` — Vector addition
- `scaleForce` — Scalar multiplication
- `forceMagnitude` — Get magnitude

### Drag

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Drag | Number | 0 | 1 | clamps | Resistance from medium |

**Presets:**
- `dragNone` — 0.0 (vacuum)
- `dragAir` — 0.1
- `dragWater` — 0.5
- `dragViscous` — 0.8
- `dragMaximum` — 1.0

**Predicates:**
- `isLowDrag` — drag < 0.2
- `isHighDrag` — drag > 0.5

### Buoyancy

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Buoyancy | Number | -1 | 1 | clamps | Upward/downward force |

**Presets:**
- `buoyancySinking` — -1.0 (denser than medium)
- `buoyancyNeutral` — 0.0
- `buoyancyFloating` — +0.5
- `buoyancyRising` — +1.0 (lighter than medium)

**Predicates:**
- `isSinking` — buoyancy < -0.2
- `isFloating` — buoyancy > +0.2

### ImpactIntensity

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ImpactIntensity | Number | 0 | 1 | clamps | Recent collision severity |

Decays over time; recency-weighted collision history.

**Presets:**
- `impactNone` — 0.0 (no recent impact)
- `impactLight` — 0.25
- `impactModerate` — 0.5
- `impactHeavy` — 0.75
- `impactSevere` — 1.0 (potentially damaging)

**Predicates:**
- `wasImpacted` — intensity > 0.1
- `wasSeverelyImpacted` — intensity > 0.7

### Acceleration

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Acceleration | Number | -inf | +inf | finite | Rate of velocity change (m/s²) |

Signed: positive = speeding up, negative = slowing down.

**Presets:**
- `accelerationNone` — 0.0
- `accelerationLight` — 2.0 m/s²
- `accelerationStrong` — 10.0 m/s²

**Predicates:**
- `decelerating` — acceleration < -0.5
- `accelerating` — acceleration > +0.5

### Velocity

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Velocity | Number | 0 | none | finite | Current speed (m/s) |

**Presets:**
- `velocityStationary` — 0.0 m/s
- `velocitySlow` — 1.0 m/s (walking)
- `velocityModerate` — 5.0 m/s (running)
- `velocityFast` — 20.0 m/s (vehicle)
- `velocityExtreme` — 100.0 m/s

**Predicates:**
- `isStationary` — velocity < 0.1
- `isMoving` — velocity > 0.1
- `isMovingFast` — velocity > 10

### Momentum

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Momentum | Record | - | - | 3D vector | mass × velocity |

**Presets:**
- `momentumNone` — (0, 0, 0) stationary

**Operations:**
- `momentumMagnitude` — Get magnitude

────────────────────────────────────────────────────────────────────────────────
                                                          // contact // atoms
────────────────────────────────────────────────────────────────────────────────

## Contact Atoms

Touch and pressure sensation — the input side of haptics.

### ContactPressure

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ContactPressure | Number | 0 | none | finite | Force per area (Pascals) |

Reference values:
- Light touch: ~100 Pa
- Firm press: ~10,000 Pa
- Pain threshold: ~100,000 Pa
- Bone fracture: ~1,000,000 Pa

**Presets:**
- `pressureNone` — 0 Pa (not touching)
- `pressureLight` — 100 Pa
- `pressureModerate` — 10,000 Pa
- `pressureHeavy` — 100,000 Pa
- `pressureCrushing` — 1,000,000 Pa

**Predicates:**
- `isPressureSafe` — pressure < 50,000 Pa
- `isPressureDangerous` — pressure > 100,000 Pa

### ContactNormal

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ContactNormal | Record | - | - | unit vector | Direction perpendicular to surface |

**Presets:**
- `normalUp` — (0, 1, 0) upward-facing surface
- `normalDown` — (0, -1, 0)
- `normalForward` — (0, 0, 1)

**Operations:**
- `dotNormal` — Dot product (cosine of angle)

### Friction

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Friction | Number | 0 | 1 | clamps | Resistance to sliding |

**Presets:**
- `frictionNone` — 0.0 (frictionless, ice)
- `frictionLow` — 0.2 (slippery)
- `frictionMedium` — 0.5 (wood, plastic)
- `frictionHigh` — 0.8 (grippy)
- `frictionMaximum` — 1.0 (rubber, sandpaper)

**Predicates:**
- `isSlippery` — friction < 0.3
- `isGrippy` — friction > 0.6

### Compliance

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Compliance | Number | 0 | 1 | clamps | Surface give/softness |

**Presets:**
- `complianceRigid` — 0.0 (steel, stone)
- `complianceFirm` — 0.2
- `complianceSoft` — 0.5 (foam, flesh)
- `complianceVerysoft` — 0.8
- `complianceFluid` — 1.0 (water, air)

**Predicates:**
- `isSolid` — compliance < 0.3
- `isDeformable` — compliance > 0.5

### SurfaceTemperature

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| SurfaceTemperature | Number | 0 | 1000 | clamps | Temperature (Kelvin) |

Reference values:
- Freezing water: 273 K
- Body temperature: 310 K
- Boiling water: 373 K
- Pain threshold (hot): ~320 K
- Pain threshold (cold): ~280 K

**Presets:**
- `tempFreezing` — 273 K (0°C)
- `tempCool` — 288 K (15°C)
- `tempNeutral` — 310 K (37°C, body temp)
- `tempWarm` — 320 K (47°C)
- `tempHot` — 350 K (77°C)
- `tempDangerous` — 400 K (127°C)

**Predicates:**
- `isTempComfortable` — 285-315 K
- `isTempDangerous` — < 273 K or > 330 K

### SurfaceRoughness

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| SurfaceRoughness | Number | 0 | 1 | clamps | Tactile texture |

**Presets:**
- `roughnessSmooth` — 0.0 (glass, polished metal)
- `roughnessFine` — 0.2
- `roughnessMedium` — 0.5 (wood grain, fabric)
- `roughnessCoarse` — 0.75
- `roughnessVeryrough` — 1.0 (gravel, bark)

**Predicates:**
- `isSmooth` — roughness < 0.2
- `isRough` — roughness > 0.6

### Grip

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Grip | Number | 0 | 1 | clamps | Hold security |

**Presets:**
- `gripNone` — 0.0 (not holding)
- `gripWeak` — 0.25
- `gripModerate` — 0.5 (might slip)
- `gripStrong` — 0.75
- `gripMaximum` — 1.0 (completely secure)

**Predicates:**
- `isHolding` — grip > 0.1
- `isSlipping` — grip between 0.1 and 0.3

### Penetration

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Penetration | Number | 0 | 1 | clamps | How deep into surface |

**Presets:**
- `penetrationNone` — 0.0 (above surface)
- `penetrationSurface` — 0.1 (touching)
- `penetrationShallow` — 0.3
- `penetrationDeep` — 0.7
- `penetrationFull` — 1.0 (fully embedded)

**Predicates:**
- `isContacting` — penetration > 0.05
- `isEmbedded` — penetration > 0.5

────────────────────────────────────────────────────────────────────────────────
                                                               // molecules
────────────────────────────────────────────────────────────────────────────────

## Molecules

Composed sensation primitives combining atoms into meaningful states.

### BodyState

Self-sensation: proprioceptive + contact atoms.

```purescript
type BodyState =
  { effort :: Effort
  , fatigue :: Fatigue
  , balance :: Balance
  , strain :: Strain
  }
```

**Presets:**
- `bodyStateNeutral` — Resting, fresh, stable
- `bodyStateExhausted` — Heavy effort, severe fatigue, high strain
- `bodyStateAlert` — Moderate effort, fresh, stable

**Predicates:**
- `isBodyStressed` — High effort OR fatigue OR strain OR exhausted
- `isBodyRelaxed` — Low effort AND fatigue AND strain AND stable

**Accessors:**
- `bodyEffortLevel`, `bodyFatigueLevel`, `bodyStrainLevel`, `bodyBalanceLevel`

### EnvironmentState

World-sensation: environmental + force atoms.

```purescript
type EnvironmentState =
  { light :: AmbientLight
  , noise :: AmbientNoise
  , crowding :: Crowding
  , freedom :: SpatialFreedom
  , airQuality :: AirQuality
  }
```

**Presets:**
- `environmentNeutral` — Moderate everything
- `environmentHostile` — Loud, crowded, constrained, poor air
- `environmentComfortable` — Quiet, empty, free, good air

**Predicates:**
- `isEnvironmentHarsh` — 2+ negative factors
- `isEnvironmentPleasant` — All factors positive

**Accessors:**
- `environmentLightLevel`, `environmentNoiseLevel`, `environmentCrowdingLevel`,
  `environmentFreedomLevel`

### SocialAwareness

Others-sensation: social atoms.

```purescript
type SocialAwareness =
  { nearestDistance :: NearestAgentDistance
  , agentsVisible :: AgentsInView
  , attention :: AttentionOnMe
  , trust :: TrustLevel
  , threat :: ThreatLevel
  }
```

**Presets:**
- `socialAlone` — No other agents nearby
- `socialCrowd` — Many agents, moderate attention
- `socialTrusted` — Few trusted companions
- `socialThreatened` — Few hostile agents, high threat

**Predicates:**
- `hasSocialSupport` — Not alone AND trusted
- `hasSocialThreat` — In danger
- `hasSocialDanger` — Critical threat
- `hasTrustedCompanions` — Not alone AND trusted

**Accessors:**
- `socialTrustLevel`, `socialThreatLevel`

### ContactEvent

Single touch event: what the agent is touching at a point.

```purescript
type ContactEvent =
  { pressure :: ContactPressure
  , normal :: ContactNormal
  , friction :: Friction
  , compliance :: Compliance
  , temperature :: SurfaceTemperature
  }
```

**Presets:**
- `contactNone` — Not touching
- `contactLight` — Light touch
- `contactFirm` — Heavy pressure
- `contactCollision` — Crushing impact

**Predicates:**
- `hasContact` — Pressure > 0
- `isContactDangerous` — Dangerous pressure
- `isContactSafe` — Safe pressure

### MovementState

How the agent is moving.

```purescript
type MovementState =
  { velocity :: Velocity
  , acceleration :: Acceleration
  , balance :: Balance
  , buoyancy :: Buoyancy
  , recentImpact :: ImpactIntensity
  }
```

**Presets:**
- `movementStationary` — Not moving
- `movementWalking` — Slow, stable
- `movementRunning` — Moderate, stable
- `movementFalling` — Fast, sinking, unstable
- `movementCollided` — Stationary after heavy impact

**Predicates:**
- `isInMotion` — Not stationary
- `isMovingQuickly` — Fast velocity
- `isFalling` — Unstable OR severely impacted
- `wasRecentlyImpacted` — Severe recent impact

**Accessors:**
- `movementSpeed`, `movementAcceleration`, `movementBalance`

────────────────────────────────────────────────────────────────────────────────
                                                               // compounds
────────────────────────────────────────────────────────────────────────────────

## Compounds

Integrated experiential states synthesizing molecules into holistic sensations.

### Comfort

Holistic wellbeing: body + environment + social.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Comfort | Number | 0 | 1 | computed | Average of body, env, social scores |

**Formula:**
```
comfort = (bodyScore + envScore + socialScore) / 3.0

where:
  bodyScore   = 1.0 if relaxed, 0.0 if stressed, 0.5 otherwise
  envScore    = 1.0 if pleasant, 0.0 if harsh, 0.5 otherwise
  socialScore = 1.0 if supported, 0.0 if threatened, 0.5 otherwise
```

**Presets:**
- `comfortHigh` — 0.9
- `comfortNeutral` — 0.5
- `comfortLow` — 0.2

**Predicates:**
- `isComfortable` — comfort > 0.6
- `isUncomfortable` — comfort < 0.4

### Distress

Negative experiential state — opposite of comfort.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Distress | Number | 0 | 1 | computed | Worst factor dominates |

**Formula:**
```
distress = 0.6 × max(bodyDistress, envDistress, socialDistress)
         + 0.4 × avg(bodyDistress, envDistress, socialDistress)
```

Distress is dominated by the worst contributing factor.

**Presets:**
- `distressNone` — 0.0
- `distressMild` — 0.3
- `distressSevere` — 0.9

**Predicates:**
- `isDistressed` — distress > 0.4

### Disorientation

Lost in space and/or time.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Disorientation | Number | 0 | 1 | computed | Spatial + temporal confusion |

**Formula:**
```
disorientation = (spatialConfusion + temporalConfusion + fallingBonus) / 2.0

where:
  spatialConfusion  = 1.0 - balance
  temporalConfusion = max(timeDistortion, loadConfusion)
  fallingBonus      = 0.4 if falling, 0.0 otherwise
```

**Presets:**
- `orientationClear` — 0.0 (fully oriented)
- `orientationConfused` — 0.5
- `orientationLost` — 1.0 (completely lost)

**Predicates:**
- `isDisoriented` — disorientation > 0.4

### Flow

Optimal engagement state — challenge matches capability.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Flow | Number | 0 | 1 | computed | Sweet spot of engagement |

**Formula:**
```
flow = (bodyFit + envFit + loadFit + urgencyFit) / 4.0

where:
  bodyFit    = 0.8 if not stressed/relaxed, lower otherwise
  envFit     = 0.7 if pleasant, 0.1 if harsh
  loadFit    = 0.9 if moderate (0.3-0.8), 0.3 if idle/overloaded
  urgencyFit = 0.9 if moderate (0.2-0.7), lower at extremes
```

**Presets:**
- `flowNone` — 0.0
- `flowPartial` — 0.5
- `flowFull` — 0.95

**Predicates:**
- `inFlow` — flow > 0.7

### Grounding

Anchored in reality — opposite of floating/dissociating.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Grounding | Number | 0 | 1 | computed | Stable contact + balance + time |

**Formula:**
```
grounding = balance × 0.3 + perfectBalanceBonus + contactScore
          + timeScore + stabilityScore

where:
  contactScore = 0.4 if touching surface
  timeScore    = 0.3 if time normal
  stabilityScore = 0.3 if stationary
```

**Presets:**
- `groundingStrong` — 0.9
- `groundingWeak` — 0.4
- `groundingNone` — 0.1

**Predicates:**
- `isGrounded` — grounding > 0.5

### Vigilance

Heightened awareness — alert but not panicked.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Vigilance | Number | 0 | 1 | computed | Alert readiness |

**Formula:**
```
vigilance = bodyTension × 0.3 + threatLevel × 0.3
          + urgencyLevel × 0.3 - trustDamper

where:
  trustDamper = trustLevel × 0.2
```

**Presets:**
- `vigilanceRelaxed` — 0.2
- `vigilanceAlert` — 0.5
- `vigilanceHyper` — 0.9

**Predicates:**
- `isVigilant` — vigilance > 0.4
- `isHypervigilant` — vigilance > 0.7

### Safety

Physical and social security.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Safety | Number | 0 | 1 | computed | Physical + social safety |

**Formula:**
```
safety = physicalSafety × 0.5 + socialSafety × 0.5

where:
  physicalSafety = balance × 0.3 + grounding + notFalling
  socialSafety   = (1 - threat) × 0.7 + trust × 0.3
```

**Presets:**
- `safetyHigh` — 0.9
- `safetyNeutral` — 0.5
- `safetyLow` — 0.2

**Predicates:**
- `isFeelingSafe` — safety > 0.6
- `isFeelingUnsafe` — safety < 0.4

### Connection

Social belonging — feeling part of a group.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Connection | Number | 0 | 1 | computed | Trust + proximity + support |

**Formula:**
```
connection = trust × 0.6 + trustedBonus + supportScore
           - threatDamage - dangerPenalty
```

**Presets:**
- `connectionStrong` — 0.9
- `connectionWeak` — 0.4
- `connectionNone` — 0.1

**Predicates:**
- `isConnected` — connection > 0.5

### Restriction

Sense of restricted freedom — trapped/constrained.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Restriction | Number | 0 | 1 | computed | Spatial + social restriction |

**Formula:**
```
restriction = spatialRestriction × 0.4 + crowdingLevel × 0.4
            + threatRestriction

where:
  spatialRestriction = 1.0 - freedom
  threatRestriction  = threatLevel × 0.3
```

**Presets:**
- `restrictionNone` — 0.1
- `restrictionModerate` — 0.5
- `restrictionSevere` — 0.9

**Predicates:**
- `isFeelingRestricted` — restriction > 0.5

### Overwhelm

Sensory overload — too much input.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Overwhelm | Number | 0 | 1 | computed | Excess input across channels |

**Formula:**
```
overwhelm = envInput × 0.3 + socialLoad × 0.2
          + processingLevel × 0.3 + urgencyLevel × 0.2
          + noisyBonus + constrainedBonus

where:
  envInput = (noise + crowding) / 2.0
```

**Presets:**
- `overwhelmNone` — 0.0
- `overwhelmModerate` — 0.5
- `overwhelmSevere` — 0.9

**Predicates:**
- `isOverwhelmed` — overwhelm > 0.6

### Drift

Loss of temporal/spatial anchoring — unmoored.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Drift | Number | 0 | 1 | computed | Gradual loss of presence |

**Formula:**
```
drift = timeDistortion + groundingInverse × 0.3 + floatScore

where:
  timeDistortion   = 0.5 if time distorted
  groundingInverse = 1.0 - grounding
  floatScore       = 0.2 if unstable
```

**Presets:**
- `driftNone` — 0.0
- `driftMild` — 0.3
- `driftSevere` — 0.8

**Predicates:**
- `isDrifting` — drift > 0.4

────────────────────────────────────────────────────────────────────────────────
                                                      // integrated // state
────────────────────────────────────────────────────────────────────────────────

## SensationState

Complete experiential snapshot — all compounds integrated.

```purescript
type SensationState =
  { comfort :: Comfort
  , distress :: Distress
  , disorientation :: Disorientation
  , overwhelm :: Overwhelm
  , safety :: Safety
  , flow :: Flow
  , grounding :: Grounding
  , vigilance :: Vigilance
  , connection :: Connection
  , restriction :: Restriction
  , drift :: Drift
  }
```

**Presets:**
- `sensationNeutral` — Baseline state
- `sensationOptimal` — Comfortable, safe, in flow
- `sensationHostile` — Stressed, unsafe, overwhelmed

### SensationEvaluation

| Constructor | Description |
|-------------|-------------|
| `Positive` | Net positive experience |
| `Neutral` | Balanced state |
| `Negative` | Net negative experience |

**Formula:**
```
balance = positives - negatives

where:
  positives = comfort + safety + flow + grounding + connection
  negatives = distress + disorientation + overwhelm + restriction + drift

Positive if balance > 1.5
Negative if balance < -1.5
Neutral otherwise
```

### WellbeingScore

Single-number summary of sensation state (0.0 worst to 1.0 best).

**Formula:**
```
wellbeing = positiveSum - negativeSum × 0.8

positiveSum =
  comfort × 0.25 + safety × 0.25 + flow × 0.15
  + grounding × 0.15 + connection × 0.20

negativeSum =
  distress × 0.30 + disorientation × 0.15 + overwhelm × 0.20
  + restriction × 0.15 + drift × 0.20
```

Maps to Affective.lean wellbeing attestation.

**Predicates:**
- `isWellbeingGood` — wellbeing > 0.6
- `isWellbeingPoor` — wellbeing < 0.4

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Sensation/
├── Proprioceptive.purs      # 508 lines — JointAngle, Reach, Balance, Effort,
│                            #              Fatigue, Strain, Orientation
├── Environment.purs         # 551 lines — AmbientLight, AmbientNoise, Crowding,
│                            #              ProximityToEdge, SpatialFreedom,
│                            #              VisibilityRadius, CoverageStatus, AirQuality
├── Social.purs              # 461 lines — NearestAgentDistance, AgentsInView,
│                            #              AttentionOnMe, TrustLevel, ThreatLevel,
│                            #              Familiarity
├── Temporal.purs            # 425 lines — SubjectiveTime, ProcessingLoad,
│                            #              ResponseLatency, TemporalResolution,
│                            #              Urgency, Anticipation
├── Force.purs               # 540 lines — GravityVector, ExternalForce, Drag,
│                            #              Buoyancy, ImpactIntensity, Acceleration,
│                            #              Velocity, Momentum
├── Contact.purs             # 576 lines — ContactPressure, ContactNormal, Friction,
│                            #              Compliance, SurfaceTemperature,
│                            #              SurfaceRoughness, Grip, Penetration
├── Molecules.purs           # 646 lines — BodyState, EnvironmentState, SocialAwareness,
│                            #              ContactEvent, MovementState
├── Compounds.purs           # 189 lines — Leader module re-exporting all compounds
└── Compounds/
    ├── Core.purs            # 254 lines — Comfort, Distress, Disorientation
    ├── Engagement.purs      # 265 lines — Flow, Grounding, Vigilance
    ├── Social.purs          # 240 lines — Safety, Connection, Restriction
    ├── Temporal.purs        # 185 lines — Overwhelm, Drift
    └── State.purs           # 322 lines — SensationState, WellbeingScore,
                             #              SensationEvaluation
```

13 files, ~5,162 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why These Primitives Matter

Sensation primitives define **how an agent experiences existence**. Unlike
visual primitives that describe what things look like, Sensation describes
what things *feel like* to an embodied perceiver.

**Proprioception:**
An agent needs to know where its body is, how it's moving, how hard it's
working. Without proprioception, an agent cannot coordinate action. These
atoms enable body awareness: joint angles for articulation, balance for
stability, effort/fatigue for resource management.

**Environmental Awareness:**
Agents exist in contexts. Is it crowded? Noisy? Dark? How much freedom do
I have to move? These atoms model ambient conditions that affect behavior
and wellbeing. An agent in a hostile environment (loud, crowded, constrained)
experiences distress; one in a comfortable environment experiences comfort.

**Social Perception:**
Multi-agent systems require social awareness. Who is nearby? Do I trust them?
Am I being watched? These atoms enable social reasoning: trust and threat
assessment, familiarity recognition, attention awareness. This feeds into
cooperation, competition, and safety evaluation.

**Temporal Experience:**
Time is not just clock time — it's experienced time. Does time feel slow
(dilated) or fast (contracted)? How urgent is the current situation? These
atoms capture the subjective temporal experience, bounded by Rights.lean
guarantees against time-based torture.

**Force and Contact:**
Embodied agents interact physically. What forces act on me? What am I
touching? These atoms model the physics of embodiment: gravity, drag,
impact, pressure, temperature, friction. Essential for any agent that
manipulates the physical world.

**Compound Integration:**
Individual sensations combine into holistic experiences. Comfort emerges
from body + environment + social states. Distress signals problems across
any channel. Flow indicates optimal engagement. These compounds enable
wellbeing monitoring and behavioral adaptation.

## AI Agent Embodiment

At billion-agent scale, these primitives enable:

**Deterministic Wellbeing:** Same sensory input = same wellbeing score.
Agents can reason about their own states and predict others' states.

**Verifiable Rights:** Rights.lean bounds on temporal manipulation ensure
no agent can be tortured via time dilation. SpatialFreedom and ProximityToEdge
integrate with spatial sovereignty guarantees.

**Affective Mapping:** Sensation compounds map directly to Affective.lean
types. Urgency in Sensation becomes urgency in Affective. This enables
consistent emotional/motivational states.

**Swarm Coordination:** Agents with shared sensation vocabulary can
communicate about states: "I'm feeling overwhelmed" maps to a specific
range of Overwhelm values. No ambiguity.

## Metaphorical Extensions

Some atoms have metaphorical interpretations for non-physical agents:

**AirQuality:** For AI agents, "breathability" represents information
environment quality — clean verified data vs. corrupted/malicious input.

**Temperature:** Could represent computational "heat" or urgency rather
than physical temperature.

**Balance:** Could represent resource allocation balance rather than
physical stability.

The key insight: **embodied metaphors ground abstract concepts**. An AI
agent doesn't have lungs, but "air quality" as information quality is
intuitive and bounded. This enables reasoning about abstract states using
physical intuitions.

────────────────────────────────────────────────────────────────────────────────
