━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // 05 // motion // text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Text Animation Subsystem

Per-character text animation and text-on-path primitives.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

The Text Animation subsystem provides per-character animation and text-on-path 
primitives for motion graphics. This includes:

- **12 text enumerations** — Font style, alignment, case, selector modes, preset types
- **3 selector types** — Range, wiggly, and expression-based character selection
- **18 animatable properties** — Position, scale, rotation, fill, stroke, tracking, blur
- **Per-character 3D** — Independent X/Y/Z transforms per character
- **Text-on-path** — Flow text along arbitrary bezier paths with margins and alignment

All values are bounded to ensure deterministic behavior at billion-agent scale.
Same animator configuration = same rendered output, guaranteed.

## File Map

```
src/Hydrogen/Schema/Motion/
├── TextAnimator.purs             # Leader module (132 lines)
├── TextAnimator/
│   ├── Enumerations.purs         # 12 enumerations (492 lines)
│   ├── Selectors.purs            # Range/Wiggly/Expression selectors (197 lines)
│   ├── Animator.purs             # 2D text animator (146 lines)
│   └── Animator3D.purs           # Per-character 3D (318 lines)
└── TextPath.purs                 # Text-on-path options (321 lines)
```

**Total: 6 files, ~1,606 lines**

**Note:** `TextAnimator.purs` is the leader module that re-exports all submodules
for convenient imports.

────────────────────────────────────────────────────────────────────────────────
                                                                // enumerations
────────────────────────────────────────────────────────────────────────────────

## TextAnimator/Enumerations.purs (492 lines)

12 enumeration types for text animation with serialization functions.

### FontStyle

```purescript
data FontStyle = FSNormal | FSItalic

fontStyleToString   :: FontStyle -> String    -- "normal" | "italic"
fontStyleFromString :: String -> Maybe FontStyle
```

### TextAlign

```purescript
data TextAlign = TALeft | TACenter | TARight

textAlignToString   :: TextAlign -> String
textAlignFromString :: String -> Maybe TextAlign
```

### AnchorPointGrouping

Grouping for per-character anchor point calculations:

```purescript
data AnchorPointGrouping
  = APGCharacter  -- Per character
  | APGWord       -- Per word
  | APGLine       -- Per line
  | APGAll        -- All text as one
```

### FillAndStroke

Render order for fill and stroke:

```purescript
data FillAndStroke
  = FASOFillOverStroke  -- Fill drawn over stroke
  | FASOStrokeOverFill  -- Stroke drawn over fill
```

### InterCharacterBlending

Blend mode between overlapping characters:

```purescript
data InterCharacterBlending
  = ICBNormal | ICBMultiply | ICBScreen | ICBOverlay
```

### TextCase

```purescript
data TextCase
  = TCNormal     -- No transformation
  | TCUppercase  -- All uppercase
  | TCLowercase  -- All lowercase
  | TCSmallCaps  -- Small capitals
```

### VerticalAlign

```purescript
data VerticalAlign
  = VANormal      -- Normal baseline
  | VASuperscript -- Superscript position
  | VASubscript   -- Subscript position
```

### RangeSelectorMode

```purescript
data RangeSelectorMode
  = RSMPercent  -- Percentage-based (0-100)
  | RSMIndex    -- Character index-based
```

### SelectionBasedOn

```purescript
data SelectionBasedOn
  = SBOCharacters                 -- All characters
  | SBOCharactersExcludingSpaces  -- Characters excluding spaces
  | SBOWords                      -- Words
  | SBOLines                      -- Lines
```

### SelectionShape (6 variants)

Falloff shape for selection:

```purescript
data SelectionShape
  = SSSquare    -- Flat selection
  | SSRampUp    -- Ramp 0 to 1
  | SSRampDown  -- Ramp 1 to 0
  | SSTriangle  -- Triangle peak
  | SSRound     -- Circular
  | SSSmooth    -- Smooth easing
```

### SelectorMode (6 variants)

How multiple selectors combine:

```purescript
data SelectorMode
  = SMAdd | SMSubtract | SMIntersect | SMMin | SMMax | SMDifference
```

### TextAnimatorPresetType (11 variants)

Preset animation types:

```purescript
data TextAnimatorPresetType
  = TAPTypewriter        -- Typewriter reveal
  | TAPFadeInByCharacter -- Fade in character by character
  | TAPFadeInByWord      -- Fade in word by word
  | TAPBounceIn          -- Bouncy entrance
  | TAPWave              -- Wave motion
  | TAPScaleIn           -- Scale up entrance
  | TAPRotateIn          -- Rotation entrance
  | TAPSlideInLeft       -- Slide from left
  | TAPSlideInRight      -- Slide from right
  | TAPBlurIn            -- Blur to clear
  | TAPRandomFade        -- Random character fade
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // selectors
────────────────────────────────────────────────────────────────────────────────

## TextAnimator/Selectors.purs (197 lines)

Selector types that determine which characters are affected by animation.

### Supporting Types

```purescript
type CharacterBlur = { x :: Number, y :: Number }
mkCharacterBlur :: Number -> Number -> CharacterBlur

type GroupingAlignment = { x :: Number, y :: Number }  -- 0-100%
mkGroupingAlignment :: Number -> Number -> GroupingAlignment

type EaseSettings = { high :: Number, low :: Number }  -- 0-100%
mkEaseSettings      :: Number -> Number -> EaseSettings
defaultEaseSettings :: EaseSettings  -- No easing
```

### TextRangeSelector

Start/end/offset based selection:

```purescript
type TextRangeSelector =
  { mode            :: RangeSelectorMode
  , startPropertyId :: AnimatablePropertyId
  , endPropertyId   :: AnimatablePropertyId
  , offsetPropertyId :: AnimatablePropertyId
  , basedOn         :: SelectionBasedOn
  , shape           :: SelectionShape
  , selectorMode    :: Maybe SelectorMode
  , amount          :: Number           -- 0-100%
  , smoothness      :: Number           -- 0-100%
  , randomizeOrder  :: Boolean
  , randomSeed      :: Int
  , ease            :: EaseSettings
  }

defaultTextRangeSelector 
  :: AnimatablePropertyId -> AnimatablePropertyId -> AnimatablePropertyId 
  -> TextRangeSelector
```

### TextWigglySelector

Organic procedural character movement:

```purescript
type TextWigglySelector =
  { enabled          :: Boolean
  , mode             :: SelectorMode
  , maxAmount        :: Number         -- Maximum %
  , minAmount        :: Number         -- Minimum %
  , wigglesPerSecond :: Number         -- Frequency
  , correlation      :: Number         -- 0-100% (adjacent correlation)
  , lockDimensions   :: Boolean
  , basedOn          :: SelectionBasedOn
  , randomSeed       :: Int
  }

defaultTextWigglySelector :: TextWigglySelector  -- Disabled
```

### TextExpressionSelector

Code-driven procedural selection:

```purescript
type TextExpressionSelector =
  { enabled          :: Boolean
  , mode             :: SelectorMode
  , amountExpression :: String         -- Expression code
  , basedOn          :: SelectionBasedOn
  }

defaultTextExpressionSelector :: TextExpressionSelector  -- Disabled, "100"
```

────────────────────────────────────────────────────────────────────────────────
                                                                    // animator
────────────────────────────────────────────────────────────────────────────────

## TextAnimator/Animator.purs (146 lines)

Core 2D text animator with animatable properties.

### TextAnimatorId

```purescript
newtype TextAnimatorId = TextAnimatorId String

mkTextAnimatorId :: String -> Maybe TextAnimatorId  -- Nothing if empty
```

### TextAnimatorProperties

18 animatable property slots:

```purescript
type TextAnimatorProperties =
  { positionPropertyId        :: Maybe AnimatablePropertyId
  , anchorPointPropertyId     :: Maybe AnimatablePropertyId
  , scalePropertyId           :: Maybe AnimatablePropertyId
  , rotationPropertyId        :: Maybe AnimatablePropertyId
  , skewPropertyId            :: Maybe AnimatablePropertyId
  , skewAxisPropertyId        :: Maybe AnimatablePropertyId
  , opacityPropertyId         :: Maybe AnimatablePropertyId
  , fillColorPropertyId       :: Maybe AnimatablePropertyId
  , fillBrightnessPropertyId  :: Maybe AnimatablePropertyId
  , fillSaturationPropertyId  :: Maybe AnimatablePropertyId
  , fillHuePropertyId         :: Maybe AnimatablePropertyId
  , strokeColorPropertyId     :: Maybe AnimatablePropertyId
  , strokeWidthPropertyId     :: Maybe AnimatablePropertyId
  , trackingPropertyId        :: Maybe AnimatablePropertyId
  , lineAnchorPropertyId      :: Maybe AnimatablePropertyId
  , lineSpacingPropertyId     :: Maybe AnimatablePropertyId
  , characterOffsetPropertyId :: Maybe AnimatablePropertyId
  , blurPropertyId            :: Maybe AnimatablePropertyId
  }

defaultTextAnimatorProperties :: TextAnimatorProperties  -- All Nothing
```

### TextAnimator

```purescript
type TextAnimator =
  { id                 :: TextAnimatorId
  , name               :: String
  , enabled            :: Boolean
  , rangeSelector      :: TextRangeSelector
  , wigglySelector     :: Maybe TextWigglySelector
  , expressionSelector :: Maybe TextExpressionSelector
  , properties         :: TextAnimatorProperties
  }

defaultTextAnimator 
  :: TextAnimatorId -> String -> TextRangeSelector -> TextAnimator
```

────────────────────────────────────────────────────────────────────────────────
                                                                 // animator-3d
────────────────────────────────────────────────────────────────────────────────

## TextAnimator/Animator3D.purs (318 lines)

Per-character 3D animation for independent X/Y/Z transforms per character.

### CharacterOrientation

Auto-orient behavior for 3D characters:

```purescript
data CharacterOrientation
  = COOff                 -- No auto-orientation
  | COOrientAlongPath     -- Orient along text path/baseline
  | COOrientTowardsCamera -- Always face camera (billboard)
  | COOrientToPoint       -- Orient towards specific point

characterOrientationToString   :: CharacterOrientation -> String
characterOrientationFromString :: String -> Maybe CharacterOrientation
```

### PerCharacter3DProperties

Independent 3D transforms per character:

```purescript
type PerCharacter3DProperties =
  { positionX         :: Maybe AnimatablePropertyId  -- X position offset
  , positionY         :: Maybe AnimatablePropertyId  -- Y position offset
  , positionZ         :: Maybe AnimatablePropertyId  -- Z position (depth)
  , anchorPointX      :: Maybe AnimatablePropertyId
  , anchorPointY      :: Maybe AnimatablePropertyId
  , anchorPointZ      :: Maybe AnimatablePropertyId
  , scaleX            :: Maybe AnimatablePropertyId  -- 0-1000%
  , scaleY            :: Maybe AnimatablePropertyId
  , scaleZ            :: Maybe AnimatablePropertyId
  , rotationX         :: Maybe AnimatablePropertyId  -- Degrees
  , rotationY         :: Maybe AnimatablePropertyId
  , rotationZ         :: Maybe AnimatablePropertyId
  , orientation       :: CharacterOrientation
  , orientTowardsPoint :: Maybe AnimatablePropertyId
  }

defaultPerCharacter3DProperties :: PerCharacter3DProperties  -- All Nothing, COOff
```

### TextAnimator3DProperties

Combined 2D + 3D properties:

```purescript
type TextAnimator3DProperties =
  { -- Standard 2D
    position2D     :: Maybe AnimatablePropertyId
  , anchorPoint2D  :: Maybe AnimatablePropertyId
  , scale2D        :: Maybe AnimatablePropertyId
  , rotation2D     :: Maybe AnimatablePropertyId
  , opacity        :: Maybe AnimatablePropertyId
  , skew           :: Maybe AnimatablePropertyId
  , skewAxis       :: Maybe AnimatablePropertyId
  
    -- 3D position/transforms
  , position3D     :: PerCharacter3DProperties
  
    -- Fill/stroke
  , fillColor      :: Maybe AnimatablePropertyId
  , fillHue        :: Maybe AnimatablePropertyId
  , fillSaturation :: Maybe AnimatablePropertyId
  , fillBrightness :: Maybe AnimatablePropertyId
  , strokeColor    :: Maybe AnimatablePropertyId
  , strokeWidth    :: Maybe AnimatablePropertyId
  
    -- Spacing
  , tracking       :: Maybe AnimatablePropertyId
  , lineAnchor     :: Maybe AnimatablePropertyId
  , lineSpacing    :: Maybe AnimatablePropertyId
  , characterOffset :: Maybe AnimatablePropertyId
  , characterBlur  :: Maybe AnimatablePropertyId
  }

defaultTextAnimator3DProperties :: TextAnimator3DProperties
```

### TextAnimator3D

Full 3D-capable text animator:

```purescript
type TextAnimator3D =
  { id                    :: TextAnimatorId
  , name                  :: String
  , enabled               :: Boolean
  , perCharacter3DEnabled :: Boolean              -- Master 3D toggle
  , rangeSelector         :: TextRangeSelector
  , wigglySelector        :: Maybe TextWigglySelector
  , expressionSelector    :: Maybe TextExpressionSelector
  , properties            :: TextAnimator3DProperties
  }

defaultTextAnimator3D
  :: TextAnimatorId -> String -> TextRangeSelector -> TextAnimator3D
```

### 3D Queries

```purescript
hasAny3DProperties   :: PerCharacter3DProperties -> Boolean
count3DProperties    :: PerCharacter3DProperties -> Int
describe3DOrientation :: PerCharacter3DProperties -> String
```

────────────────────────────────────────────────────────────────────────────────
                                                                  // text-path
────────────────────────────────────────────────────────────────────────────────

## TextPath.purs (321 lines)

Text-on-path options for flowing text along arbitrary bezier paths.

### TextPathSource

Source of the path for text to follow:

```purescript
data TextPathSource
  = TPSNone              -- No path (standard layout)
  | TPSMask Int          -- Mask on layer by index (1-based)
  | TPSMaskNamed String  -- Mask on layer by name
  | TPSShapeLayer String -- Path from shape layer (by name)
  | TPSCustomPath        -- Custom inline path definition

textPathSourceToString   :: TextPathSource -> String
textPathSourceFromString :: String -> Maybe TextPathSource
```

### PathAlignment

```purescript
data PathAlignment
  = PALeft    -- Text starts at path beginning
  | PACenter  -- Text centers on path
  | PARight   -- Text ends at path end
  | PAJustify -- Text stretches to fill path

pathAlignmentToString   :: PathAlignment -> String
pathAlignmentFromString :: String -> Maybe PathAlignment
```

### BaselineShiftMode

```purescript
data BaselineShiftMode
  = BSMNone      -- No baseline adjustment
  | BSMAutomatic -- Automatic based on font metrics
  | BSMManual    -- Manual offset value

baselineShiftModeToString   :: BaselineShiftMode -> String
baselineShiftModeFromString :: String -> Maybe BaselineShiftMode
```

### PathMargin

Margin offset along path (percentage, -100% to 100%):

```purescript
newtype PathMargin = PathMargin Number

pathMargin       :: Number -> PathMargin  -- Clamped to bounds
unwrapPathMargin :: PathMargin -> Number
```

### TextPathOptions

Complete path options:

```purescript
type TextPathOptions =
  { source              :: TextPathSource
  , reversePath         :: Boolean        -- Flow in reverse direction
  , perpendicularToPath :: Boolean        -- Characters rotate to tangent
  , forceAlignment      :: Boolean        -- Justify to path length
  , firstMargin         :: PathMargin     -- Offset from path start
  , lastMargin          :: PathMargin     -- Offset from path end
  , alignment           :: PathAlignment
  , baselineShiftMode   :: BaselineShiftMode
  , baselineShift       :: Number         -- Manual offset (pixels)
  }

defaultTextPathOptions :: TextPathOptions  -- No path, perpendicular enabled
textPathOptions        :: TextPathSource -> TextPathOptions
```

### Operations

```purescript
setFirstMargin         :: Number -> TextPathOptions -> TextPathOptions
setLastMargin          :: Number -> TextPathOptions -> TextPathOptions
setReversePath         :: Boolean -> TextPathOptions -> TextPathOptions
setPerpendicularToPath :: Boolean -> TextPathOptions -> TextPathOptions
setForceAlignment      :: Boolean -> TextPathOptions -> TextPathOptions
```

### Queries

```purescript
hasPathOptions        :: TextPathOptions -> Boolean
isPathReversed        :: TextPathOptions -> Boolean
isPerpendicularToPath :: TextPathOptions -> Boolean
isForceAligned        :: TextPathOptions -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                              // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

**From Schema:**
- `Hydrogen.Schema.Bounded` — `clampNumber` for PathMargin bounds

**Within Motion:**
- `Hydrogen.Schema.Motion.Property` — `AnimatablePropertyId` for all property refs
- Layer system uses text animators via `LTText` layer type
- Keyframe system animates all property IDs

## Usage Example

Creating a typewriter reveal with per-character rotation:

```purescript
import Hydrogen.Schema.Motion.TextAnimator.Animator
import Hydrogen.Schema.Motion.TextAnimator.Animator3D
import Hydrogen.Schema.Motion.TextAnimator.Selectors
import Hydrogen.Schema.Motion.TextPath
import Data.Maybe (fromJust)

-- Create range selector for typewriter effect
rangeSelector = defaultTextRangeSelector startId endId offsetId
  # _ { shape = SSRampUp, amount = 100.0 }

-- Basic 2D animator
basicAnimator = defaultTextAnimator
  (fromJust (mkTextAnimatorId "reveal"))
  "Typewriter Reveal"
  rangeSelector

-- 3D animator with per-character rotation
animator3D = defaultTextAnimator3D
  (fromJust (mkTextAnimatorId "rotate-in"))
  "3D Rotate In"
  rangeSelector
  # _ { perCharacter3DEnabled = true
      , properties = defaultTextAnimator3DProperties
          { position3D = defaultPerCharacter3DProperties
              { rotationY = Just rotYPropertyId
              , orientation = COOrientAlongPath
              }
          }
      }

-- Text on a circular path
pathOptions = textPathOptions (TPSMask 1)
  # setFirstMargin 10.0
  # setLastMargin 10.0
```

────────────────────────────────────────────────────────────────────────────────
