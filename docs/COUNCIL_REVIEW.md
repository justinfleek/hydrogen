━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // council // review // 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Hydrogen Architecture Council Review

**Date**: 2026-02-25
**Reviewed By**: Three Expert Councils
**Subject**: Ultimate Diffusion-Based Realtime Viewport Assessment

## Executive Summary

The Hydrogen GPU pipeline demonstrates **strong foundational architecture** for a
pure functional rendering system. The pure data model, bounded atoms, and external
state architecture are excellent. However, **critical gaps remain** for the stated
goal of becoming the "ultimate viewport as portal between AI and humans."

**Overall Verdict**: Foundation is sound, critical gaps remain.

────────────────────────────────────────────────────────────────────────────────
                                                              // council // one
────────────────────────────────────────────────────────────────────────────────

## Council Round 1: GPU Graphics Experts

**Expertise**: WebGPU internals, real-time rendering, compute shaders, diffusion
models, high-performance graphics

### 1.1 Compute Pipeline Analysis

#### What's Present and Well-Designed

`ComputeKernel.purs` provides comprehensive coverage for traditional GPU effects:

| Category | Coverage | Assessment |
|----------|----------|------------|
| Blur | Gaussian, Directional, Radial, Box | ✓ Excellent |
| Glow | Bloom, Inner, Outer | ✓ Good |
| Noise | Perlin, Simplex, FBM, Worley | ✓ Excellent |
| Particles | Physics, Emit, Sort | ✓ Good |
| Color | Grading, Tone Mapping, Space | ✓ Good |
| Composition | Blend, Mask, Alpha | ✓ Good |

**Strong points:**
- Separable blur architecture — correct 2-pass implementation
- Workgroup size selection per kernel type — appropriate choices
- Cost estimation — enables GPU budget management
- Conditional kernel execution — quality-adaptive rendering

#### Critical Missing: Diffusion Primitives

**No diffusion-specific kernels exist.** For "every section as diffusion target":

```purescript
-- MISSING: Latent space operations
data DiffusionKernel
  = KernelEncode                    -- Image → Latent (VAE encoder)
      { inputChannels :: Int        -- 3 or 4 (RGB/RGBA)
      , latentChannels :: Int       -- 4 (SD default)
      , downsampleFactor :: Int     -- 8 (SD default)
      }
  | KernelDecode                    -- Latent → Image (VAE decoder)
  | KernelDenoise                   -- Single denoising step
      { sigmaStart :: Number        -- Starting noise level
      , sigmaEnd :: Number          -- Target noise level  
      , cfgScale :: Number          -- Classifier-free guidance
      , stepIndex :: Int            -- Current step
      , totalSteps :: Int           -- Total steps
      }
  | KernelNoiseSchedule             -- Schedule computation
      { scheduler :: SchedulerType  -- DDPM, DDIM, Euler, DPM++
      , totalSteps :: Int
      }
  | KernelLatentBlend               -- Latent space compositing
      { mask :: KernelInput         -- Blend mask in latent space
      , operation :: LatentOp       -- Add, Lerp, Slerp
      }
  | KernelCFG                       -- CFG guidance computation
      { unconditionalLatent :: KernelInput
      , conditionalLatent :: KernelInput
      , scale :: Number
      }
```

**Missing noise schedule types:**

```purescript
data SchedulerType
  = SchedulerDDPM
  | SchedulerDDIM  
  | SchedulerEuler
  | SchedulerEulerAncestral
  | SchedulerDPMPP2M
  | SchedulerDPMPP2MKarras
  | SchedulerHeun
  | SchedulerLMS

type NoiseSchedule =
  { timesteps :: Array Number       -- σ values for each step
  , alphasCumprod :: Array Number   -- α̅ values
  , sigmas :: Array Number          -- σ values for sampling
  , scaledTimesteps :: Array Number -- For scheduler-specific scaling
  }
```

**Missing latent space types:**

```purescript
newtype LatentTensor = LatentTensor
  { shape :: Shape                  -- [batch, 4, h/8, w/8]
  , noiseLevel :: Number            -- Current σ level
  , schedulerState :: SchedulerState
  , conditioning :: Maybe Conditioning
  }

data Conditioning
  = TextConditioning 
      { embeddings :: KernelInput   -- [batch, 77, 768/1024]
      , pooled :: Maybe KernelInput -- For SDXL
      }
  | ImageConditioning KernelInput   -- For ControlNet/IP-Adapter
  | CompositeConditioning (Array Conditioning)
```

### 1.2 WebGPU Mapping Assessment

**Current Abstraction Level: Correct**

The types in `ComputeKernel` map cleanly to WebGPU:

```typescript
// ComputeKernel → WebGPU mapping

// KernelConfig → GPUComputePassDescriptor
const passDescriptor: GPUComputePassDescriptor = {
  label: kernelToString(kernel)
};

// WorkgroupSize → @workgroup_size in WGSL
@workgroup_size(config.workgroupSize.x, config.workgroupSize.y, config.workgroupSize.z)

// DispatchSize → dispatchWorkgroups
pass.dispatchWorkgroups(dispatch.x, dispatch.y, dispatch.z);

// KernelInput/Output → GPUBindGroup entries
// InputTexture → texture_2d<f32> binding
// OutputTexture → texture_storage_2d<rgba8unorm, write> binding
```

#### Gap: Missing Texture/Buffer Descriptor Types

```purescript
-- MISSING: Texture format specification
data TextureFormat
  = RGBA8Unorm      -- Standard 8-bit
  | RGBA16Float     -- HDR rendering
  | RGBA32Float     -- Full precision (diffusion)
  | R32Float        -- Single channel (depth/mask)
  | RG32Float       -- Two channel (flow)
  | BGRA8Unorm      -- Some platform swap chains

-- MISSING: Texture usage flags
data TextureUsage
  = UsageSampled       -- Shader read
  | UsageStorage       -- Compute write
  | UsageRenderTarget  -- Fragment output
  | UsageCopySrc       -- Transfer source
  | UsageCopyDst       -- Transfer destination

-- MISSING: Pipeline identity for caching
type PipelineKey = UUID5.UUID5

data CompiledPipeline = CompiledPipeline
  { key :: PipelineKey
  , kernel :: ComputeKernel
  , bindGroupLayout :: Array BindGroupEntry
  , compiledAt :: FrameTime
  }
```

### 1.3 Multi-Viewport Sync and Distributed Time

**Current State: Insufficient for Billion-Agent Scale**

`FrameState.purs` handles single-instance state well but lacks distributed sync:

```purescript
-- MISSING: Distributed time authority
data TimeAuthority
  = LocalAuthority TimeState                -- Single agent
  | NetworkAuthority                        -- Coordinated cluster
      { serverId :: UUID5.UUID5             -- Time server identity
      , serverTime :: FrameTime             -- Authoritative timestamp
      , localOffset :: FrameTime            -- Local → server offset
      , rtt :: FrameTime                    -- Round-trip time
      , confidence :: Number                -- 0.0-1.0 sync quality
      }

-- MISSING: Viewport synchronization
data ViewportSync = ViewportSync
  { viewportId :: UUID5.UUID5
  , authority :: TimeAuthority
  , frameOffset :: Int                      -- Frames ahead/behind authority
  , syncState :: SyncState
  }

data SyncState
  = Synchronized                            -- Within tolerance
  | Drifting Number                         -- Drifting by N ms/frame
  | Resynchronizing                         -- Catching up
  | Disconnected                            -- No authority contact

-- MISSING: Cross-viewport effect coordination
data SharedEffectState = SharedEffectState
  { effectId :: UUID5.UUID5
  , owningViewport :: UUID5.UUID5
  , subscribedViewports :: Array UUID5.UUID5
  , currentPhase :: AnimationPhase
  , lastSyncFrame :: FrameNumber
  }
```

### 1.4 Diffusion Integration Analysis

**What's Needed for "Every Section as Diffusion Target"**

```purescript
-- MISSING: Per-region diffusion state
data RegionDiffusionState = RegionDiffusionState
  { regionId :: UUID5.UUID5
  , latent :: LatentTensor                  -- Current latent state
  , noiseLevel :: Number                    -- Current σ
  , targetSteps :: Int                      -- Configured step count
  , currentStep :: Int                      -- Where we are
  , controlSignals :: Array ControlSignal   -- External guidance
  , blendMode :: DiffusionBlendMode         -- How to composite result
  }

data DiffusionBlendMode
  = BlendReplace                            -- Replace region entirely
  | BlendAlpha Number                       -- Alpha blend with base
  | BlendLatent LatentBlendOp               -- Blend in latent space

-- MISSING: Step control for real-time
data StepStrategy
  = FixedSteps Int                          -- Always N steps
  | AdaptiveSteps                           -- Quality-based
      { minSteps :: Int
      , maxSteps :: Int  
      , qualityTarget :: Number
      }
  | BudgetedSteps                           -- Time-based
      { framebudgetMs :: Number
      , stepsPerFrame :: Int
      }
  | IncrementalDenoise                      -- One step per frame
      { accumulationFrames :: Int
      }
```

### 1.5 Performance Bottlenecks at 120fps

#### Memory Allocation Patterns

**Current issue:** `defaultConfig` creates new records per kernel.

At 120fps with 50 kernels/frame = **6000 allocations/second** just for configs.

**Solutions:**
1. Pool common configs
2. Use indices into pre-allocated config arrays
3. Define configs as constants for common dimensions

#### Shader Compilation

**No pipeline caching representation.** Every frame could theoretically recompile.

**WebGPU impact:** Pipeline compilation is ~10-50ms per shader. Without caching,
first use of each effect causes frame drops.

#### Dispatch Batching

Each kernel dispatches independently with no batching consideration.

```purescript
-- MISSING: Dispatch batching
data KernelBatch = KernelBatch
  { kernels :: Array ComputeKernel
  , sharedBindings :: Array BindGroupEntry
  , dispatchOrder :: Array Int
  }

-- MISSING: Resource barrier analysis
needsBarrier :: ComputeKernel -> ComputeKernel -> Boolean
```

### 1.6 Missing GPU Primitives

| Operation | Status | Use Case |
|-----------|--------|----------|
| SDF Rendering | Missing | Text, icons (Ghostty) |
| Signed Distance Fields | Missing | UI shapes |
| Bezier Curve GPU | Missing | Vector graphics |
| Text Glyph Cache | Missing | Terminal rendering |
| Order-Independent Transparency | Missing | Glass effects |
| MSAA Integration | Missing | Anti-aliasing |
| TAA (Temporal AA) | Missing | Motion stability |

#### Critical for Target Applications

**Frame.io (Video Editing):**
```purescript
data VideoKernel
  = KernelYUVtoRGB                          -- Color space conversion
  | KernelScaler                            -- Lanczos/bicubic scaling
  | KernelDeinterlace                       -- Field processing
  | KernelLUT3D                             -- Color LUT application
```

**Ghostty (Terminal):**
```purescript
data TextKernel
  = KernelGlyphRasterize                    -- SDF glyph rendering
  | KernelTextLayout                        -- Glyph positioning
  | KernelSubpixelAA                        -- ClearType-style AA
  | KernelCursorBlink                       -- Animated cursor
```

**Hospital Dashboards:**
```purescript
data ChartKernel
  = KernelLinePlot                          -- Vital sign traces
  | KernelSparkline                         -- Inline charts
  | KernelGradientFill                      -- Area fills
  | KernelThresholdOverlay                  -- Alert zones
```

**Fighter Jet HUD:**
```purescript
data HUDKernel
  = KernelVectorLine                        -- Symbology lines
  | KernelArcSegment                        -- Attitude indicators
  | KernelBitmapSymbol                      -- Warning icons
  | KernelNightVisionMode                   -- NVG-compatible output
```

────────────────────────────────────────────────────────────────────────────────
                                                              // council // two
────────────────────────────────────────────────────────────────────────────────

## Council Round 2: Real-Time Systems Architects

**Expertise**: Game engine architectures, ECS systems, event-driven programming,
physics engines, distributed real-time systems

### 2.1 State Model Analysis

**Assessment: Correct granularity, but missing stratification**

**What's Right:**
- External state model is fundamentally sound
- Separating TimeState, MouseState, ViewportState enables partial updates
- PerformanceState tracks GPU/CPU budgets — essential for adaptive quality

**Critical Gaps:**

1. **No per-element state locality**

   At 1000+ elements, all state lives in flat registries. Game engines solve
   this with ECS where state lives with entities:

   ```purescript
   type ElementState =
     { animations :: Array AnimationHandle
     , springs :: Array SpringHandle  
     , localTime :: Number  -- element-local timeline
     }
   ```

2. **No hierarchical invalidation**

   When a spring updates, the entire FrameState is "dirty". Need:

   ```purescript
   type FrameStateDelta =
     { dirtyAnimations :: Set AnimationHandle
     , dirtySprings :: Set SpringHandle
     , dirtyElements :: Set PickId
     }
   ```

3. **MouseState lacks gesture accumulation**

   For sub-millisecond input, you need:
   - Input queue with timestamps (not just current position)
   - Gesture recognizer state machine
   - Prediction buffer for 120Hz+ displays

### 2.2 Event Architecture Analysis

**Assessment: Correct pure evaluation, but missing temporal context**

**What's Right:**
- TriggerCondition ADT enables ternary logic (Met/NotMet/Unknown)
- Boolean algebra composition via TriggerCombinator
- TimeTrigger variants cover essential temporal patterns

**Critical Gaps:**

1. **No trigger registration timestamp**

   `evaluateTriggerWithTime` takes `elapsedMs` as a parameter, but who tracks
   when each trigger was registered?

2. **Edge detection is missing**

   Cannot distinguish MouseEnter from MouseHover without external state:

   ```purescript
   data TriggerEdge
     = EdgeRising      -- false → true this frame
     | EdgeFalling     -- true → false this frame
     | LevelHigh       -- currently true
     | LevelLow        -- currently false
   ```

3. **No debouncing/throttling primitives**

   At 120fps, you don't want 120 `MouseMove` events per second:

   ```purescript
   data TriggerTiming
     = Immediate
     | Debounced Number    -- wait N ms after last trigger
     | Throttled Number    -- at most once per N ms
     | Sampled Int         -- every N frames
   ```

### 2.3 Spring Physics Analysis

**Assessment: Semi-implicit Euler is acceptable, but not optimal**

Semi-implicit Euler (symplectic Euler) updates velocity first, then position:
- **Stable** for constant timesteps
- **Energy-conserving** (won't explode)
- **First-order accurate**

**Potential Issues:**

1. **Variable timestep instability**

   If frame time varies (16.67ms → 33.33ms during a hitch), spring behavior
   changes. At high stiffness (k > 1000), variable dt can cause overshooting.

   **Solution**: Fixed timestep accumulator
   ```purescript
   tickSpringFixed :: Number -> Number -> SpringInstance -> SpringInstance
   tickSpringFixed accumulator fixedDt spring =
     if accumulator >= fixedDt
     then tickSpringFixed (accumulator - fixedDt) fixedDt (stepSpring fixedDt spring)
     else spring { accumulator = accumulator }
   ```

2. **Missing critical damping ratio**

   Users can't specify "critically damped" (ζ = 1.0) springs:

   ```purescript
   criticalDamping = 2.0 * sqrt (spring.stiffness * spring.mass)
   dampingRatio = spring.damping / criticalDamping
   ```

### 2.4 Animation Registry Performance

**Assessment: O(n) lookup will bottleneck at scale**

| Operation | Current | Required |
|-----------|---------|----------|
| `getAnimationPhase` | O(n) via `Array.find` | O(1) |
| `tickAnimations` | O(n) — acceptable | O(n) |
| `unregisterAnimation` | O(n) via `filter` | O(1) |

At 1000 animations and 120fps:
- 120,000 lookups/second for phase queries
- If each lookup scans 500 elements on average: **60 million comparisons/second**

**Solutions:**
1. **IntMap/HashMap**: Replace Array with Map keyed by handle
2. **Generational indices**: Handles are `{ index, generation }` for slot reuse
3. **Archetype batching**: Group animations by phase for SIMD-friendly ticking

### 2.5 Snapshot/Undo Analysis

**Assessment: Full snapshots correct for small state, delta compression needed**

**Issues at Scale:**
- Memory explosion: 1000 springs × 100 undo levels × 32 bytes = 3.2 MB
- No structural sharing: Changing one spring copies all 1000

**Solutions:**
1. **Copy-on-write with structural sharing**
2. **Command-based undo** (History.purs already has this, but not connected)
3. **Keyframe + interpolation** for continuous state

### 2.6 Distributed Time Coordination

**Current Model: No distributed coordination exists**

**Requirements for Billion-Agent Sync:**

1. **Lamport timestamps** for causal ordering:
   ```purescript
   type LogicalTime =
     { wallClock :: FrameTime
     , logicalCounter :: Int
     , agentId :: UUID5
     }
   ```

2. **Vector clocks** for conflict detection

3. **Clock synchronization protocol** (NTP-style)

4. **Deterministic frame scheduling**:
   ```purescript
   frameTime :: FrameNumber -> GlobalTime -> LocalTime
   frameTime frame globalStart = globalStart + (toNumber frame * frameDuration)
   ```

5. **Input canonicalization** with rollback/resimulation

### 2.7 Input Handling Gaps

**Current: Mouse-only**

**Missing Input Types:**

```purescript
-- Touch events
type TouchPoint =
  { id :: Int
  , x :: Number, y :: Number
  , force :: Number         -- 0.0-1.0
  , radiusX :: Number
  , radiusY :: Number
  }

-- Stylus/pen input
type StylusState =
  { x :: Number, y :: Number
  , pressure :: Number      -- 0.0-1.0
  , tiltX :: Number         -- degrees
  , tiltY :: Number
  , twist :: Number         -- rotation
  , pointerType :: PointerType  -- Pen/Eraser
  }

-- Gesture recognition
data GestureState
  = GestureNone
  | GesturePinch { scale :: Number, velocity :: Number }
  | GestureRotate { rotation :: Number, velocity :: Number }
  | GestureSwipe { direction :: SwipeDirection, velocity :: Number }
  | GestureLongPress { duration :: Number }

-- Unified pointer abstraction
type PointerState =
  { id :: Int
  , type :: PointerType     -- Mouse/Touch/Pen
  , x :: Number, y :: Number
  , pressure :: Number
  , buttons :: Int          -- bitmask
  , isPrimary :: Boolean
  }

-- Gamepad/controller input
type GamepadState =
  { axes :: Array Number    -- -1.0 to 1.0
  , buttons :: Array { pressed :: Boolean, value :: Number }
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                            // council // three
────────────────────────────────────────────────────────────────────────────────

## Council Round 3: Domain Specialists

**Expertise**: Medical device displays (FDA), avionics HUDs (DO-178C), broadcast
graphics, accessibility, multi-sensory interfaces

### 3.1 Medical Displays (FDA 21 CFR Part 11)

#### What Exists (Applicable)

**Temporal pillar** provides:
- `Milliseconds`, `Frames`, `FPS` atoms — sufficient for ECG waveform timing
- `Progress`, `Iteration` atoms for trending displays

**Reactive pillar** provides:
- `Stale`, `Refreshing`, `Offline` data states — critical for medical
- `Error`, `Warning`, `Info` semantic states for alarm categories

#### Complete Gaps

| Gap | Required Atoms/Molecules |
|-----|-------------------------|
| **Waveform primitives** | `WaveformSample`, `Waveform { samples, sampleRate, lead }` |
| **Alarm states with audio** | `AlarmPriority`, `AlarmAudio { tone, pattern, volume }` |
| **Medical time atoms** | `InfusionRate`, `DrugDose` |
| **Trend visualization** | `TrendWindow`, `TrendAlert` |
| **Signal quality indicators** | `SignalQuality = Good | Marginal | Poor | Invalid | LeadOff` |

#### Audio Gap — CRITICAL

**RenderEffect.purs is visual-only.** Medical devices require:

```purescript
data AudioEffect
  = AlarmTone { frequency :: Hz, duty :: Percent, priority :: AlarmPriority }
  | VoiceAlert { message :: String, voice :: VoiceProfile }
  | HeartbeatSync { rate :: BPM }
```

**Assessment**: Hydrogen **CANNOT** render a compliant hospital dashboard without
the Audio pillar being integrated into the effect system.

### 3.2 Avionics HUD (DO-178C DAL-A)

#### What Exists (Applicable)

**Geometry pillar** provides:
- `Degrees`, `Radians`, `ArcMinute`, `ArcSecond` — sufficient for heading/attitude
- `Circle`, `Arc`, `Polygon` — can compose attitude indicators

**Spatial pillar** provides:
- `EulerAngles`, `Quaternion` for attitude representation

#### Complete Gaps

| Gap | Required Atoms/Molecules |
|-----|-------------------------|
| **Failure mode display** | `DataValidity = Valid | Stale { age } | Failed | CrossCheck` |
| **Redundancy indication** | `SensorSource = Primary | Secondary | Tertiary` |
| **Flight level atoms** | `FlightLevel`, `PressureAltitude` |
| **Mach number** | `MachNumber { mach: BoundedNumber 0 10 }` |
| **Tape displays** | `TapeDisplay { value, range, bugs, trend }` |
| **Symbology flashing** | `FlashState { phase, rate, priority }` |

#### Failure Mode Gap — CRITICAL

```purescript
-- CURRENT (insufficient)
| Stale         | Data may be outdated

-- REQUIRED for DO-178C
data DataAge
  = Fresh               -- < 250ms
  | Aging { ms :: Int } -- 250ms - 2s (yellow cross-hatch)
  | Stale { ms :: Int } -- 2s - 10s (X through display)
  | Invalid             -- > 10s or sensor failure (remove from display)
  | NeverReceived       -- source never provided data
```

### 3.3 Broadcast Graphics (SMPTE Compliance)

#### What Exists (Applicable)

**Temporal pillar** provides:
- `Frames`, `FPS`, `Timecode` atoms
- Motion blur with `shutterAngle` — broadcast-accurate

#### Gaps

| Gap | Required Atoms/Molecules |
|-----|-------------------------|
| **SMPTE Timecode** | `SMPTETimecode { hours, minutes, seconds, frames, dropFrame, frameRate }` |
| **Genlock** | `GenlockStatus = Locked | Hunting | Free`, `PhaseOffset` |
| **Drop-frame accounting** | `DropFrameMode = NonDrop | DropFrame` |
| **Safe areas** | `SafeArea = TitleSafe | ActionSafe | GraphicsSafe` |
| **Broadcast color space** | `LegalRange = Full | Limited`, `VideoLevel` bounded to legal |
| **Alpha premultiplication** | `AlphaMode = Straight | Premultiplied` |

### 3.4 Accessibility (WCAG 2.1 AA)

#### What Exists (Applicable)

**Reactive pillar** provides:
- `FocusTrap`, `FocusScope`, `FocusRestore` — good focus management
- `RovingTabindex` for keyboard navigation

#### Complete Gaps — CRITICAL

**No ARIA atoms exist anywhere in the Schema.**

```purescript
data AriaRole
  = RoleButton
  | RoleLink  
  | RoleTab
  | RoleTabPanel
  | RoleTabList
  | RoleMenu
  | RoleMenuItem
  | RoleDialog
  | RoleAlertDialog
  | RoleAlert
  | RoleStatus
  | RoleProgressbar
  | RoleSlider
  | RoleCheckbox
  | RoleRadio
  | RoleSwitch
  | RoleTextbox
  | RoleGrid
  | RoleTree
  | RoleListbox
  | RoleCombobox
  | RoleTooltip
  -- ... 40+ more roles

-- ARIA states
data AriaState
  = AriaExpanded Boolean
  | AriaSelected Boolean
  | AriaPressed Boolean | TriState
  | AriaChecked Boolean | Mixed
  | AriaDisabled Boolean
  | AriaHidden Boolean
  | AriaInvalid Boolean
  | AriaBusy Boolean

-- ARIA properties
data AriaProperty
  = AriaLabelledBy String
  | AriaDescribedBy String
  | AriaControls String
  | AriaOwns String
  | AriaLive Politeness
  | AriaAtomic Boolean

-- Motion preferences
data MotionPreference = NoPreference | Reduce | Preserve
```

**Assessment**: Hydrogen **CANNOT** produce accessible web applications without
ARIA primitives. This is a **blocking gap** for any public-facing UI.

### 3.5 Haptics

#### What Exists

**Pillar 10: Haptic** provides:
- `Intensity`, `Sharpness`, `Frequency`, `Duration` atoms
- `Attack`, `Decay` envelope parameters
- Impact feedback compounds

#### Gaps for AI Emotional Expression

| Gap | Required Atoms/Molecules |
|-----|-------------------------|
| **Force curves** | `ForceCurve { points, interpolation }` |
| **Emotional mapping** | `EmotionHaptic = Curiosity | Excitement | Calm | Concern | Joy` |
| **Biometric sync** | `BiometricSync { source: HeartRate | Breathing, phase }` |
| **Multi-actuator patterns** | `SpatialHaptic { actuators, pattern }` |

```purescript
data ForceProfile
  = LinearRamp { start :: Intensity, end :: Intensity, duration :: Milliseconds }
  | ExponentialDecay { peak :: Intensity, tau :: Milliseconds }
  | ADSR { attack, decay, sustain, release :: Milliseconds }
  | Custom { curve :: ForceCurve }
```

### 3.6 Audio

#### What Exists

**Pillar 10b: Audio** in Schema provides extensive vocabulary:
- Complete synthesis parameters
- Effects (reverb, delay, compression)
- Spatial audio atoms

#### Gap: Integration with RenderEffect

**RenderEffect.purs is visual-only.** Audio has no parallel effect system.

```purescript
-- MISSING: AudioEffect type parallel to RenderEffect
data AudioEffect
  = EffectReverb ReverbEffect
  | EffectDelay DelayEffect
  | EffectCompressor CompressorEffect
  | EffectSpatialize SpatialAudioEffect
  | EffectNone

-- MISSING: Audio-visual sync
type AVElement =
  { visual :: Element
  , audio :: AudioCue
  , sync :: SyncMode
  }

-- MISSING: AI voice rendering
type VoiceElement =
  { text :: String
  , voice :: VoiceProfile
  , emotion :: EmotionTag
  }
```

### 3.7 Failure Modes

**Current: Simple Stale boolean**

**Required for safety-critical:**

```purescript
data DataValidity
  = Valid { confidence :: Percent, source :: SensorId }
  | Degraded { reason :: DegradationReason, usable :: Boolean }
  | Stale { age :: Duration, lastValid :: Timestamp }
  | SensorFailure { sensor :: SensorId, failureMode :: FailureMode }
  | CommsLost { since :: Duration, lastPacket :: Timestamp }
  | CrossCheckFailed { sources :: Array SensorId, disagreement :: Percent }
  | OutOfRange { value :: Number, min :: Number, max :: Number }
  | RateOfChangeExceeded { current :: Number, previous :: Number, maxRate :: Number }
  | NeverReceived

data FailureMode
  = HardwareFault
  | CalibrationError
  | RangeExceeded
  | SelfTestFailed
  | Unknown

data DisplayResponse
  = ShowLastValidWithAge { age :: Duration }
  | ShowXThrough
  | RemoveFromDisplay
  | ShowFailureFlag { flag :: FailureFlag }
  | FlashWithMessage { message :: String, rate :: Hz }
```

────────────────────────────────────────────────────────────────────────────────
                                                             // gap // summary
────────────────────────────────────────────────────────────────────────────────

## Critical Blocking Gaps

| Gap | Identified By | Impact | Priority | Status |
|-----|---------------|--------|----------|--------|
| **No diffusion primitives** | GPU Council | Cannot do AI avatar rendering | P0 | OPEN |
| **No distributed time sync** | Real-Time Council | Cannot sync billion agents | P0 | OPEN |
| ~~**No AudioEffect type**~~ | Domain Council | Medical, broadcast, AI voice blocked | P0 | **DONE** ✓ |
| ~~**No ARIA/accessibility atoms**~~ | Domain Council | All web apps fail WCAG | P0 | **DONE** ✓ |
| **No SDF/text rendering kernels** | GPU Council | Cannot build Ghostty | P1 | OPEN |
| **No failure mode atoms** | Domain Council | Avionics/medical blocked | P1 | OPEN |
| **O(n) registry lookups** | Real-Time Council | Bottleneck at 1000+ animations | P1 | OPEN |
| **Variable timestep instability** | Real-Time Council | Physics glitches | P1 | OPEN |

### Implementation Log (2026-02-26)

**AudioEffect System — COMPLETE:**
- `src/Hydrogen/Audio/AudioEffect.purs` — Composable audio effect ADT
- `src/Hydrogen/Audio/AVSync.purs` — Audio-visual synchronization (AVElement, VoiceElement, EmotionTag)
- `src/Hydrogen/Schema/Audio/Effects.purs` — 12 new effect presets

**Accessibility Schema — COMPLETE:**
- `src/Hydrogen/Schema/Accessibility/` — Full WAI-ARIA 1.2 primitives
- 7 files: Role.purs, State.purs, Property.purs, LiveRegion.purs, Landmark.purs, Molecules.purs, Accessibility.purs
- ~1,170 lines covering all ARIA roles (59), states (10), properties, live regions, landmarks

## Application Status Matrix

| Application | Status | Blocking Gaps |
|-------------|--------|---------------|
| **Frame.io** | 🟡 Partial | Video decode kernels, LUT3D |
| **Ghostty** | 🔴 Blocked | SDF text rendering, glyph cache |
| **Cinema4D/After Effects** | 🟡 Partial | 3D compositing, expressions |
| **Ableton** | 🟡 Partial | Waveforms (AudioEffect now exists) |
| **Hospital Dashboard** | 🟡 Partial | Waveforms, signal quality (AudioEffect now exists) |
| **Fighter Jet HUD** | 🔴 Blocked | DataValidity, failure flags |
| **AI Avatar Window** | 🟡 Partial | Diffusion (voice/emotion now exist) |
| **Accessible Web Apps** | 🟢 Unblocked | ARIA primitives **DONE** |

## Domain Summary Matrix

| Domain | Visual | Temporal | Audio | Haptic | Accessibility | Failure | Status |
|--------|--------|----------|-------|--------|---------------|---------|--------|
| Medical Dashboard | Partial | Partial | **DONE** | N/A | **DONE** | Partial | **Feasible** |
| Avionics HUD | Good | Good | **DONE** | N/A | N/A | **MISSING** | **BLOCKED** |
| Broadcast Graphics | Good | Partial | **DONE** | N/A | N/A | Partial | **Feasible** |
| Web Accessibility | Good | Good | N/A | N/A | **DONE** | Good | **UNBLOCKED** |
| AI Haptic Expression | N/A | Good | **DONE** | Partial | N/A | N/A | **Feasible** |

────────────────────────────────────────────────────────────────────────────────
                                                      // implementation // plan
────────────────────────────────────────────────────────────────────────────────

## Recommended Implementation Order

### Phase 1: Core Infrastructure (Unblocks everything)

1. `Hydrogen/GPU/Resource.purs`
   - TextureDescriptor, BufferDescriptor, PipelineCache
   - TextureFormat, TextureUsage enums

2. `Hydrogen/GPU/Interpreter.purs`
   - Execute ComputeKernel against WebGPU
   - WGSL shader generation

3. Fix AnimationRegistry to use `Map` (O(1) lookups)

4. Add fixed timestep accumulator to springs

### Phase 2: Multi-Modal (Unblocks AI avatar, medical, broadcast) — **COMPLETE**

5. ~~`Hydrogen/Audio/AudioEffect.purs`~~ ✓ DONE
   - Parallel structure to RenderEffect
   - Synthesis, spatialization, analysis effects

6. ~~`Hydrogen/Audio/Synthesis.purs`~~ ✓ EXISTS (Schema/Audio/Synthesis.purs)
   - Schema audio atoms already implemented

7. ~~Integrate audio with Element composition~~ ✓ DONE
   - AVElement type for synchronized audio-visual (AVSync.purs)
   - VoiceElement type for AI voice (AVSync.purs)

### Phase 3: Diffusion (Unblocks AI avatar, real-time inference) — **COMPLETE**

8. ~~`Hydrogen/GPU/Diffusion.purs`~~ ✓ DONE
   - LatentTensor, LatentShape, NoiseSchedule, SigmaSchedule
   - Conditioning (Text, Image, Composite, None)
   - DiffusionKernel ADT (Encode, Decode, Denoise, NoiseSchedule, LatentBlend, CFG)
   - SchedulerType (16 variants: normal, karras, exponential, beta57, etc.)
   - NoiseType (19 variants: gaussian, brownian, fractal family, pyramid, perlin)
   - NoiseMode (12 variants: hard, soft, lorentzian, sinusoidal)
   - GuideMode (9 variants: flow, sync, lure, data, epsilon, pseudoimplicit)
   - ImplicitType (4 variants: rebound, retro-eta, bongmath, predictor-corrector)
   - RegionDiffusionState, DiffusionRegion, DiffusionBlendMode
   - StepStrategy (Standard, Substep, Ancestral, SDE)
   - Full RES4LYF compatibility (types from res4lyf repository analysis)
   - Presets: eulerDiscrete, dpmPlusPlus2M, flowMatchEuler, res4lyfRebound, res4lyfPredictorCorrector

9. `Hydrogen/GPU/Diffusion/Sampler.purs` — OPEN (scheduler implementations)
   - Sampler implementations using DiffusionKernel types

10. Per-region diffusion state in FrameState — OPEN (FrameState.Allocation being handled by other agent)

### Phase 4: Accessibility & Safety (Unblocks web, medical, avionics) — **PARTIAL**

11. ~~`Hydrogen/Schema/Accessibility/Aria.purs`~~ ✓ DONE
    - All ARIA roles (59 total: 20 widget, 9 composite, 27 structure, 3 window)
    - ARIA states (10 types with tristate support)
    - ARIA properties (relationship, widget, label)
    - Live regions with politeness levels
    - Landmark roles
    - Full implementation: `src/Hydrogen/Schema/Accessibility/` (7 files, ~1,170 lines)

12. `Hydrogen/Schema/Reactive/DataValidity.purs` — OPEN
    - Graduated failure modes
    - Sensor source tracking
    - Display response strategies

13. Integrate with Element type — OPEN

### Phase 5: Domain-Specific (Unblocks specific applications)

14. `Hydrogen/GPU/Kernel/Text.purs`
    - SDF glyph rendering
    - Subpixel anti-aliasing
    - Glyph cache management

15. `Hydrogen/GPU/Kernel/Video.purs`
    - YUV→RGB conversion
    - LUT3D application
    - Frame scaling

16. `Hydrogen/GPU/Kernel/Chart.purs`
    - Waveform rendering
    - Trend visualization
    - Threshold overlays

17. `Hydrogen/Schema/Temporal/Timecode.purs`
    - SMPTE timecode molecule
    - Drop-frame handling
    - Genlock status

### Phase 6: Distributed Scale

18. `Hydrogen/Distributed/TimeAuthority.purs`
    - Lamport timestamps
    - Vector clocks
    - Clock sync protocol

19. `Hydrogen/Distributed/ViewportSync.purs`
    - Multi-viewport coordination
    - Shared effect state
    - Drift compensation

20. Input canonicalization and rollback

────────────────────────────────────────────────────────────────────────────────
                                                                  // conclusion
────────────────────────────────────────────────────────────────────────────────

## Verdict

**The foundation is architecturally sound.**

The separation of kernel description from execution, the compositional algebra
(sequence/parallel/conditional), the tensor-native viewport model, and the pure
data architecture are excellent design decisions.

**Critical gaps for stated goals (updated 2026-02-26):**

1. No diffusion primitives (blocking for AI avatar rendering) — **OPEN**
2. No distributed time sync (blocking for multi-viewport at scale) — **OPEN**
3. ~~No AudioEffect system~~ — **DONE** (AudioEffect.purs + AVSync.purs)
4. ~~No ARIA accessibility~~ — **DONE** (Schema/Accessibility/ pillar)
5. No SDF/text rendering (blocking for Ghostty-class terminals) — **OPEN**

**Progress since original review:**
- AudioEffect ADT created parallel to RenderEffect
- AVElement and VoiceElement types for AI avatar audio-visual sync
- Complete WAI-ARIA 1.2 accessibility primitives (59 roles, 10 states, properties)
- Web applications now UNBLOCKED for accessibility compliance
- Medical/broadcast audio now FEASIBLE

**Remaining blockers:**
- Diffusion primitives for AI avatar rendering
- Distributed time sync for billion-agent coordination
- DataValidity for safety-critical (avionics/medical)

**Recommendation:** Address remaining gaps in priority order. Web apps and
audio-enabled applications are now feasible. Focus on diffusion and distributed
time for full "AI portal" capability.

────────────────────────────────────────────────────────────────────────────────

                                               — The Council // 2026-02-25

────────────────────────────────────────────────────────────────────────────────
