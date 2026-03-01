# Pillar 10: Haptic

Tactile and sensory feedback.

## Implementation

- **Location**: `src/Hydrogen/Schema/Haptic/`
- **Files**: 5 modules
- **Key features**: Vibration control, audio feedback, haptic events, iOS system patterns

## Atoms

### Vibration

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Intensity | Number | 0.0 | 1.0 | clamps | Vibration strength |
| Sharpness | Number | 0.0 | 1.0 | clamps | Haptic sharpness (iOS) |
| HapticFrequency | Number | 0 | 500 | clamps | Vibration frequency (Hz) |
| HapticDuration | Number | 0 | 10000 | clamps | Haptic duration (ms) |
| Attack | Number | 0 | none | finite | Ramp up time (ms) |
| Decay | Number | 0 | none | finite | Ramp down time (ms) |

### Audio

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Volume | Number | 0.0 | 1.0 | clamps | Sound volume |
| Pitch | Number | 0.1 | 4.0 | clamps | Pitch multiplier |
| Pan | Number | -1.0 | 1.0 | clamps | Stereo pan |
| SoundId | String | - | - | - | Sound asset identifier |

## Molecules

| Name | Composition | Notes |
|------|-------------|-------|
| HapticEvent | Intensity + Sharpness + Duration + Attack + Decay | Full envelope haptic event |
| VibrationStep | Intensity + Duration | Simple vibration primitive |
| AudioCue | SoundId + Volume + Pitch + Pan | Audio feedback event |
| HapticPattern | Array HapticEvent + loop flag | Sequence of haptic events |

## Compounds

### Impact Feedback

| Name | Description |
|------|-------------|
| ImpactLight | Subtle tap (light intensity, sharp sharpness) |
| ImpactMedium | Standard tap (medium intensity) |
| ImpactHeavy | Strong tap (heavy intensity, sharp) |
| ImpactSoft | Muted, soft tap (low intensity, soft sharpness) |
| ImpactRigid | Sharp, rigid tap (high intensity, very sharp) |

### Notification Feedback

| Name | Description |
|------|-------------|
| NotifySuccess | Positive acknowledgment (two ascending pulses) |
| NotifyWarning | Attention needed (three medium pulses) |
| NotifyError | Something went wrong (two heavy pulses) |

### Selection Feedback

| Name | Description |
|------|-------------|
| SelectionTick | Single selection change (light, quick tick) |
| SelectionStart | Begin selection (slightly stronger) |
| SelectionEnd | End selection (confirmation feel) |

### Continuous Feedback

| Name | Description |
|------|-------------|
| TextureType | Textured surface feel (oscillating intensity) |
| SliderType | Position-dependent intensity |
| RampType | Increasing/decreasing over time |

### System Patterns (iOS)

| Name | Description |
|------|-------------|
| Peek | Preview content (3D Touch peek) |
| Pop | Confirm selection (3D Touch pop) |
| AlignmentGuide | Snap to guide (design tools) |
| LevelChange | Undo/redo level marker |

### Audio Feedback

| Name | Description |
|------|-------------|
| ClickSound | UI click |
| KeySound | Keyboard key press |
| LockSound | Lock screen |
| PaymentSound | Transaction complete |
| CameraSound | Shutter sound |
| AmbientLoop | Background audio loop |
