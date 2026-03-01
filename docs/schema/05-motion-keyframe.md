━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // 05 // motion // keyframe
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Motion: Keyframe Animation

Core keyframe types and animation composition.

────────────────────────────────────────────────────────────────────────────────
                                                                       // atoms
────────────────────────────────────────────────────────────────────────────────

## Keyframe.purs (396 lines)

Keyframe data for motion graphics animation.

**Types:**
- `KeyframeId` — Unique identifier (deterministically generated)
- `InterpolationType` — { Linear, Bezier, Hold, Auto }
- `Tangent` — { x, y } control point offset for bezier
- `KeyframeValue` — Value sum type:
  - `NumberValue Number`
  - `Vec2Value { x, y }`
  - `Vec3Value { x, y, z }`
  - `ColorValue { r, g, b, a }`
  - `AngleValue Number` (degrees)
  - `PercentValue Number` (0-100)

- `Keyframe` — Complete keyframe:
  - `{ id, frame, value, interpolation, inTangent, outTangent }`

**Constructors:**
- `keyframe` — Basic keyframe with auto-generated ID
- `keyframeWithId` — With explicit ID
- `tangent`, `tangentFlat`, `tangentAuto`

**Builders:**
- `withInterpolation`, `withInTangent`, `withOutTangent`
- `withBezierTangents` — Set both tangents + bezier mode
- `withHold`, `withLinear`, `withAuto`

**Accessors:**
- `frame`, `value`, `interpolationType`, `inTangent`, `outTangent`, `keyframeId`

**Predicates:**
- `isBezier`, `isHold`, `isLinear`, `isAuto`

**Operations:**
- `setFrame`, `setValue`, `shiftFrame`
- `lerpValue` — Linear interpolation between values
- `addValues`, `scaleValue`

## KeyframeAnimation/Types.purs (229 lines)

Core enumerations for keyframe animations.

**AnimationProperty (20 variants):**
- Transform: `PropTranslateX/Y/Z`, `PropRotate/X/Y/Z`, `PropScale/X/Y`, `PropSkewX/Y`
- Visual: `PropOpacity`, `PropBlur`, `PropBrightness`, `PropSaturate`
- Color: `PropBackgroundColor`, `PropBorderColor`, `PropShadowColor`
- Custom: `PropCustom String`

**AnimationDirection:**
- `DirectionNormal`, `DirectionReverse`
- `DirectionAlternate`, `DirectionAlternateReverse`

**AnimationFillMode:**
- `FillNone`, `FillForwards`, `FillBackwards`, `FillBoth`

**AnimationPlayState:**
- `PlayStatePlaying`, `PlayStatePaused`

────────────────────────────────────────────────────────────────────────────────
                                                                   // molecules
────────────────────────────────────────────────────────────────────────────────

## KeyframeAnimation/Keyframe.purs

`PropertyKeyframe` — Keyframe with percent offset (0-100) and value.

Helpers:
- `propertyKeyframe`, `opacityKeyframe`, `translateXKeyframe`
- `translateYKeyframe`, `rotateKeyframe`, `scaleKeyframe`, `colorKeyframe`

## KeyframeAnimation/Core.purs (238 lines)

`KeyframeAnimation` — Complete animation specification:

```purescript
{ id, name, property, keyframes, duration, delay,
  iterations, direction, fillMode, playState, easing }
```

**Constructors:**
- `keyframeAnimation` — Full control (name, property, keyframes, duration)
- `simpleAnimation` — Two-keyframe (start → end)

**Builders:**
- `withDuration`, `withDelay`, `withIterations`, `withInfinite`
- `withDirection`, `withFillMode`, `withEasing`, `withProperty`
- `addKeyframe`

**Accessors:**
- `duration`, `delay`, `iterations`, `direction`, `fillMode`
- `keyframes`, `property`

**Predicates:**
- `isInfinite`, `isPaused`, `hasKeyframes`

────────────────────────────────────────────────────────────────────────────────
                                                                  // compounds
────────────────────────────────────────────────────────────────────────────────

## KeyframeAnimation/Presets/Attention.purs

Attention-grabbing animations:
- `bounce`, `flash`, `pulse`, `rubberBand`, `shake`
- `swing`, `tada`, `wobble`, `jello`, `heartBeat`

## KeyframeAnimation/Presets/Enter.purs

Entry animations:
- `fadeIn`, `fadeInUp/Down/Left/Right`
- `slideInUp/Down/Left/Right`
- `zoomIn`, `bounceIn`

## KeyframeAnimation/Presets/Exit.purs

Exit animations:
- `fadeOut`, `fadeOutUp/Down/Left/Right`
- `slideOutUp/Down/Left/Right`
- `zoomOut`, `bounceOut`

## KeyframeAnimation/Presets/Loading.purs

Loading state animations:
- `spin`, `spinReverse`, `pingPong`, `breathe`

────────────────────────────────────────────────────────────────────────────────
                                                                // source files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Motion/
├── Keyframe.purs
├── KeyframeAnimation.purs (leader)
└── KeyframeAnimation/
    ├── Types.purs
    ├── Keyframe.purs
    ├── Core.purs
    └── Presets/
        ├── Attention.purs
        ├── Enter.purs
        ├── Exit.purs
        └── Loading.purs
```

~1,500 lines total.

────────────────────────────────────────────────────────────────────────────────

