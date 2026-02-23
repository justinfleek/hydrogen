# Hydrogen Session Notes

**Last Updated:** 2026-02-23
**Build Status:** Zero warnings, zero errors

---

## Current Goal

Port remaining Halogen-based components (`Hydrogen.Component.*`) to Schema-native Element-based components (`Hydrogen.Element.Component.*`). All components must use Schema atoms exclusively — no hardcoded CSS strings, no Tailwind classes, no JavaScript FFI except at true system boundaries.

---

## Key Constraints

- **Pure Schema, no Tailwind**: Components must use Schema atoms exclusively
- **No escape hatches**: No `extraAttributes` — everything must be fully deterministic
- **No JS FFI**: FFI only at true system boundaries (Target.DOM runtime), never in components
- **Pure PureScript locale data**: Use lookup tables for locale strings, not JavaScript's Intl API
- **500 line max per file**: Files must be split when exceeding this limit
- **Explicit imports only**: Never use `(..)` imports — they are canaries for incomplete work
- **Fix all warnings**: Zero warnings required — NEVER DELETE CODE TO FIX WARNINGS
- **UUID5 for identifiers**: Deterministic ID generation for contacts, events, etc.

---

## Build Command

```bash
nix develop --command spago build
```

---

## Component Porting Status

### Ported to Element (38 components)

| Component | Element Lines | Status |
|-----------|---------------|--------|
| Alert | 382 | Complete |
| AlertDialog | 440 | Complete |
| AutoComplete | 824 | Complete |
| Avatar | 328 | Complete |
| Badge | 297 | Complete |
| Breadcrumb | 277 | Complete |
| Button | 681 | Complete |
| Calendar | 1,726 | Complete |
| Card | 531 | Complete |
| ChatBubble | 813 | Complete |
| Checkbox | 412 | Complete |
| CodeBlock | 400 | Complete |
| Collapsible | 314 | Complete |
| ColorPicker | 968 | Complete |
| DataGrid | 939 + subs | Complete |
| Input | 713 | Complete |
| LoadingBar | 317 | Complete |
| NumberInput | 522 | Complete |
| Pagination | 558 | Complete |
| PasswordInput | 891 | Complete |
| Progress | 314 | Complete |
| Radio | 549 | Complete |
| Rating | 384 | Complete |
| SearchInput | 816 | Complete |
| Select | 496 | Complete |
| Separator | 297 | Complete |
| Sheet | 369 | Complete |
| Skeleton | 457 | Complete |
| Slider | 428 | Complete |
| StatCard | 446 | Complete |
| Stepper | 562 | Complete |
| Switch | 383 | Complete |
| Table | 155 | Complete |
| TagInput | 734 | Complete |
| Textarea | 836 | Complete |
| Timeline | 361 | Complete |
| Toast | 684 | Complete |
| Toggle | 446 | Complete |

### Not Yet Ported (33 components, ~12,130 lines)

#### High Priority — Date/Time (use new Scheduling schema)

| Component | Halogen Lines | Notes |
|-----------|---------------|-------|
| DatePicker | 667 | Uses Calendar internally |
| DateRangePicker | 675 | Uses Calendar internally |
| TimePicker | 686 | Uses Hour/Minute/TimeOfDay atoms |

#### Medium Priority — Complex Interactive

| Component | Halogen Lines | Notes |
|-----------|---------------|-------|
| Carousel | 631 | Touch/swipe gestures |
| Kanban | 701 | Drag-drop board |
| TreeView | 596 | Hierarchical data |
| Tour | 666 | Onboarding overlay |

#### Medium Priority — Specialized Inputs

| Component | Halogen Lines | Notes |
|-----------|---------------|-------|
| OTPInput | 326 | Multi-digit verification |
| PhoneInput | 547 | International format |
| CreditCard | 802 | Card detection/formatting |
| Signature | 701 | Canvas drawing |

#### Lower Priority — Visual Effects

| Component | Halogen Lines | Notes |
|-----------|---------------|-------|
| Confetti | 398 | Particle system |
| QRCode | 638 | Image generation |
| GradientEditor | 226 | Color stops editor |
| MeshGradientRenderer | 155 | Complex gradient |

#### Motion Subsystem (18 components, 7,741 lines)

**Curve/** (6 components, 2,486 lines)
- BezierCurve, CurveEditor, CurveHandle, CurveKeyframe, EasingPicker, EasingPreview

**Property/** (6 components, 2,499 lines)
- AngleDial, KeyframeToggle, PositionXY, PropertyGroup, PropertyRow, ScrubableNumber

**Timeline/** (6 components, 2,756 lines)
- AnimationTimeline, KeyframeMarker, LayerTrack, Playhead, PropertyTrack, TimeRuler

---

## Schema Pillar Completeness

### Complete (~80%+)

| Pillar | Files | Notes |
|--------|-------|-------|
| Color | 37 | Missing: Value, camera log curves, LUT modules |
| Dimension | 14+ | Missing: SI prefixes, explicit pixel types |
| Typography | 17 | Missing: TabSize, TextDecoration, OpenType features |
| Reactive | 13 | Mostly complete |
| Gestural | 16+ | Missing: Pinch, Rotate multi-touch |

### Partial (15-50%)

| Pillar | Files | Major Gaps |
|--------|-------|------------|
| Temporal | 6 | Missing: Frames, FPS, Spring physics, Progress atoms |
| Elevation | 2 | Missing: Perspective, DoF, semantic elevation compounds |
| Geometry | 1 | Only Radius.purs exists — missing angles, shapes, paths, transforms, beziers |
| Audio | 2 | Only Frequency/Level — missing synthesis, envelopes, filters |

### Missing (0%)

| Pillar | Priority | Description |
|--------|----------|-------------|
| Material | High | Blur, filters, noise, borders, gradients, surfaces |
| Haptic | Medium | Vibration, impact feedback, audio cues |
| Spatial | Medium | 3D transforms, cameras, lights, PBR materials |
| Brand | High | Design tokens, themes, semantic colors, component tokens |

---

## (..) Import Canaries

**111 files with 188 (..) imports need fixing.**

### Highest Priority (5 occurrences)

- `src/Hydrogen/Query.purs`
- `src/Hydrogen/API/Client.purs`

### High Priority (3-4 occurrences)

- `src/Hydrogen/HTML/Renderer.purs` (4)
- `src/Hydrogen/Schema/Dimension/Camera.purs` (3)
- `src/Hydrogen/Realtime/WebSocket.purs` (3)
- `src/Hydrogen/Motion/LayoutAnimation.purs` (3)
- `src/Hydrogen/Error/Boundary.purs` (3)
- `src/Hydrogen/Component/DatePicker.purs` (3)
- `src/Hydrogen/Component/DataGrid.purs` (3)

### Common Patterns to Fix

```purescript
-- BAD (canary)
import Data.Maybe (..)

-- GOOD (explicit)
import Data.Maybe (Maybe(Nothing, Just), isJust, isNothing, fromMaybe)
```

---

## Scheduling System (Completed This Session)

New modules in `src/Hydrogen/Schema/Scheduling/`:

| Module | Lines | Description |
|--------|-------|-------------|
| RSVP.purs | ~100 | Pending, Accepted, Declined, Tentative, Delegated |
| Recurrence.purs | ~400 | RFC 5545 rules (daily, weekly, monthly, yearly) |
| Contact.purs | ~250 | Person, Room, Resource, Group with ContactId |
| Invite.purs | ~280 | AttendeeRole, RSVP tracking, ContactId reference |
| Event.purs | 405 | Core types, constructors, accessors |
| EventQuery.purs | 150 | Boolean predicates, computed properties |
| EventMod.purs | 203 | Modifiers, offset ops, iCal export |

New modules in `src/Hydrogen/Schema/Temporal/`:

| Module | Lines | Description |
|--------|-------|-------------|
| Millisecond.purs | ~90 | Bounded 0-999 |
| TimeOfDay.purs | 300 | Hour + Minute + Second + Millisecond molecule |
| Timezone.purs | ~310 | UtcOffset, TimezoneId, 13 common zones |

---

## Recommended Next Steps (Priority Order)

### 1. Port Date/Time Components (uses new Scheduling schema)

```
DatePicker.purs → Element/Component/DatePicker.purs
DateRangePicker.purs → Element/Component/DateRangePicker.purs  
TimePicker.purs → Element/Component/TimePicker.purs
```

### 2. Create Missing Schema Pillars

**Material Pillar** (highest impact):
- BlurRadius, BlurSigma atoms
- Filter atoms (Brightness, Contrast, Saturation, etc.)
- BorderWidth, BorderStyle atoms
- GradientFill, SolidFill compounds
- BackdropBlur, Frosted effects

**Brand Pillar** (required for theming):
- ColorToken, SpacingToken, SizeToken molecules
- SemanticColors compound
- ThemeLight, ThemeDark compounds

**Geometry Pillar** (required for many components):
- Angle atoms (Degrees, Radians, Turns)
- Point2D, Point3D molecules
- Circle, Rectangle, Path compounds
- Transform molecules (Translate, Rotate, Scale)

### 3. Fix (..) Imports in Core Modules

Start with highest-impact:
- `Hydrogen/Query.purs`
- `Hydrogen/API/Client.purs`
- `Hydrogen/HTML/Renderer.purs`

### 4. Port Complex Interactive Components

```
Carousel.purs → Uses Gestural/Swipe
Kanban.purs → Uses DragDrop
TreeView.purs → Recursive rendering
```

### 5. Port Motion Subsystem

This is a large undertaking (7,741 lines). Consider:
- Start with core timeline components
- Bezier/easing can reuse Schema/Motion/Easing

---

## File Locations

### Documentation
- `docs/SCHEMA.md` — Full 12 pillar enumeration
- `docs/design-ontology.md` — Implementation details
- `docs/COMPONENT_ARCHITECTURE.md` — Component porting spec
- `CLAUDE.md` — Project rules and attestation

### Halogen Components (to port FROM)
- `src/Hydrogen/Component/*.purs`
- `src/Hydrogen/Component/Motion/**/*.purs`

### Element Components (to port TO)
- `src/Hydrogen/Element/Component/*.purs`

### Schema Atoms
- `src/Hydrogen/Schema/Color/`
- `src/Hydrogen/Schema/Dimension/`
- `src/Hydrogen/Schema/Geometry/`
- `src/Hydrogen/Schema/Typography/`
- `src/Hydrogen/Schema/Elevation/`
- `src/Hydrogen/Schema/Temporal/`
- `src/Hydrogen/Schema/Reactive/`
- `src/Hydrogen/Schema/Gestural/`
- `src/Hydrogen/Schema/Audio/`
- `src/Hydrogen/Schema/Motion/`
- `src/Hydrogen/Schema/Scheduling/` (NEW)

### Missing Schema Directories (to create)
- `src/Hydrogen/Schema/Material/`
- `src/Hydrogen/Schema/Haptic/`
- `src/Hydrogen/Schema/Spatial/`
- `src/Hydrogen/Schema/Brand/`

---

## Session Summary (2026-02-23)

### Created

- `Millisecond.purs` — Bounded millisecond atom
- `TimeOfDay.purs` — Time molecule
- `Timezone.purs` — UTC offset and IANA zones
- `RSVP.purs` — Attendee response status
- `Recurrence.purs` — RFC 5545 recurrence rules
- `Contact.purs` — Person/Room/Resource/Group
- `Invite.purs` — Event invitation with roles
- `Event.purs` — Core event types (split into 3 modules)
- `EventQuery.purs` — Query functions
- `EventMod.purs` — Modifiers and display

### Fixed

- `Hour.purs` — Added missing Show class import
- `Minute.purs` — Added missing Show class import
- `Second.purs` — Added missing Show class import
- Removed monolithic `Time.purs` (replaced by individual modules)

### Verified

- Full build: 0 warnings, 0 errors
- All new modules under 500 line limit
- All imports explicit (no `(..)`)
