━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                // 12 // brand
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Brand Pillar

The complete vocabulary for brand identity, design tokens, themes, and visual
systems. 37 source files defining the atoms, molecules, and compounds that
compose a brand's complete design language.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

Brand provides bounded, deterministic primitives for:
- Brand identity (name, domain, UUID5)
- Color palettes with semantic roles (OKLCH-based)
- Typography systems (families, weights, scales)
- Spacing systems (grid, geometric scales)
- Brand voice and personality (tone, traits, IS/NOT constraints)
- Logo systems (lockups, variants, rules, errors)
- Content-addressed provenance (SHA256, timestamps)
- Design tokens (named values with semantic meaning)
- Theme composition (light, dark, contrast modes)
- Component compounds (UI styling via token references)

## At Billion-Agent Scale

When agents compose UI, they reference tokens by semantic name (`color.primary.500`,
`spacing.md`) rather than raw values. The brand system resolves these references
deterministically. Two agents referencing the same token get identical output.

Brands are content-addressed: same content → same hash → same identity.
This enables distributed caching, version tracking, and deterministic builds.

────────────────────────────────────────────────────────────────────────────────
                                                             // core // identity
────────────────────────────────────────────────────────────────────────────────

## Identity.purs (188 lines)

Brand identity atoms and the complete identity molecule.

**Atoms:**

### Domain
A validated domain string — non-empty, lowercase, contains at least one dot.

```purescript
newtype Domain = Domain String

domain :: String -> Maybe Domain        -- Smart constructor
unDomain :: Domain -> String            -- Unwrap
mkDomainUnsafe :: String -> Domain      -- For trusted sources only
```

Examples: `"jbreenconsulting.com"`, `"nike.com"`, `"apple.com"`

Invariant: `domain_valid` (nonempty ∧ has_dot)

### BrandName
A validated brand name — 1-256 characters, trimmed.

```purescript
newtype BrandName = BrandName String

brandName :: String -> Maybe BrandName  -- Smart constructor
unBrandName :: BrandName -> String      -- Unwrap
```

Examples: `"J. Breen Consulting"`, `"Nike"`, `"Apple Inc."`

Invariant: `brand_name_bounded` (1 <= length <= 256)

### UUID
A 128-bit universally unique identifier in standard format (36 chars with hyphens).

```purescript
newtype UUID = UUID String

mkUUID :: String -> Maybe UUID          -- Format validation
unUUID :: UUID -> String                -- Unwrap
brandNamespace :: UUID                  -- DNS namespace for UUID5
```

Format: `"xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx"`

Invariant: `uuid5_deterministic` (same namespace + name = same uuid)

**Molecule:**

### BrandIdentity
Complete identity composed of name, domain, and UUID.

```purescript
type BrandIdentity =
  { name :: BrandName
  , domain :: Domain
  , uuid :: UUID
  }

mkBrandIdentity :: BrandName -> Domain -> UUID -> BrandIdentity
brandUUID :: BrandIdentity -> UUID
```

The UUID is computed as `uuid5(brandNamespace, domain)` at ingestion time.
Same domain always produces same UUID — deterministic identity.

────────────────────────────────────────────────────────────────────────────────
                                                              // color // system
────────────────────────────────────────────────────────────────────────────────

## Palette.purs (261 lines)

Brand color palette with semantic roles in OKLCH color space.

**Atoms:**

### Lightness
Perceptual lightness from 0 (black) to 1 (white). Clamped.

```purescript
newtype Lightness = Lightness Number
mkLightness :: Number -> Lightness      -- Clamps to [0, 1]
```

### Chroma
Color saturation from 0 (gray) to 0.5 (maximum). Clamped.

```purescript
newtype Chroma = Chroma Number
mkChroma :: Number -> Chroma            -- Clamps to [0, 0.5]
```

### Hue
Color hue from 0 to 360 degrees. Wraps.

```purescript
newtype Hue = Hue Number
mkHue :: Number -> Hue                  -- Wraps at 360
```

Color wheel: 0=red, 120=green, 240=blue

**Molecules:**

### OKLCH
Perceptually uniform color composed of Lightness, Chroma, Hue.

```purescript
type OKLCH = { l :: Lightness, c :: Chroma, h :: Hue }
oklch :: Number -> Number -> Number -> OKLCH
```

### Role
Semantic color roles for design systems:

```purescript
data Role
  = Primary       -- Main brand color
  | Secondary     -- Supporting brand color
  | Accent        -- Call-to-action, highlights
  | Background    -- Page/section backgrounds
  | Surface       -- Card/element backgrounds
  | OnPrimary     -- Text/icons on primary
  | OnSecondary   -- Text/icons on secondary
  | OnBackground  -- Text/icons on background
  | OnSurface     -- Text/icons on surface
  | Success       -- Positive feedback
  | Warning       -- Caution feedback
  | Error         -- Negative feedback
  | Info          -- Informational
```

**Compound:**

### BrandPalette
Complete color palette with validated constraints.

```purescript
type BrandPalette = { entries :: Array PaletteEntry }
mkBrandPalette :: Array PaletteEntry -> Maybe BrandPalette
getPrimary :: BrandPalette -> OKLCH
getByRole :: Role -> BrandPalette -> Maybe OKLCH
```

Invariants:
- `has_primary`: Palette always has primary color
- `unique_roles`: Each role appears at most once

**Contrast Utilities:**

```purescript
lightnessDiff :: OKLCH -> OKLCH -> Number
wcagAALightnessDiff :: Number   -- 0.4 (≈4.5:1 ratio)
wcagAAALightnessDiff :: Number  -- 0.55 (≈7:1 ratio)
```

────────────────────────────────────────────────────────────────────────────────
                                                                      // voice
────────────────────────────────────────────────────────────────────────────────

## Voice.purs (451 lines)

Brand voice and personality — the most valuable part of brand ingestion.

**Atoms:**

### Tone
The primary emotional register of brand communication.

```purescript
data Tone
  = Formal        -- Professional, reserved
  | Casual        -- Friendly, conversational
  | Playful       -- Fun, lighthearted
  | Authoritative -- Expert, commanding
  | Empathetic    -- Understanding, supportive
  | Inspirational -- Motivating, uplifting
  | Technical     -- Precise, detailed
  | Minimalist    -- Brief, essential
```

A brand has exactly one tone — the foundation of voice consistency.

### Trait
Individual personality traits that describe the brand:

```purescript
data Trait
  -- Trust & Reliability
  = Trustworthy | Reliable | Authentic | Transparent
  -- Innovation & Creativity
  | Innovative | Creative | Bold | Visionary
  -- Approachability
  | Friendly | Approachable | Warm | Inclusive
  -- Expertise
  | Expert | Knowledgeable | Sophisticated | Premium
  -- Energy
  | Energetic | Passionate | Dynamic | Driven
```

### Term
A vocabulary term (word or phrase), must be non-empty.

```purescript
newtype Term = Term String
mkTerm :: String -> Maybe Term
```

**Molecules:**

### TraitSet
Non-empty, unique collection of personality traits.

```purescript
type TraitSet = { traits :: Array Trait }
mkTraitSet :: Array Trait -> Maybe TraitSet  -- Returns Nothing if empty
hasTrait :: Trait -> TraitSet -> Boolean
```

### Vocabulary
Preferred and prohibited terms for brand voice.

```purescript
type Vocabulary = { preferred :: Array Term, prohibited :: Array Term }
mkVocabulary :: Array Term -> Array Term -> Maybe Vocabulary
isPreferred :: String -> Vocabulary -> Boolean
isProhibited :: String -> Vocabulary -> Boolean
```

Invariant: `vocabulary_disjoint` (preferred ∩ prohibited = ∅)

### VoiceAttribute (IS/NOT Pattern)
**The most valuable part of any brand voice specification.**

Converts subjective tone guidance into enforceable constraints.

```purescript
type VoiceAttribute =
  { name :: String              -- "Authoritative"
  , is :: Array Term            -- [knowledgeable, trusted, confident]
  , isNot :: Array Term         -- [overbearing, pompous, condescending]
  }

mkVoiceAttribute :: String -> Array Term -> Array Term -> Maybe VoiceAttribute
matchesAttribute :: String -> VoiceAttribute -> Boolean
violatesAttribute :: String -> VoiceAttribute -> Boolean
```

Example from SMART Brand Ingestion Framework:
```
Authoritative:
  IS: knowledgeable, trusted, confident, credible
  IS NOT: overbearing, pompous, condescending
```

### VoiceConstraints
Collection of VoiceAttributes for complete voice guardrails.

```purescript
type VoiceConstraints = { attributes :: Array VoiceAttribute }
checkConstraints :: String -> VoiceConstraints -> Array String
findViolations :: Array String -> VoiceConstraints -> Array (Tuple String (Array String))
```

**Compound:**

### BrandVoice
Complete voice configuration for a brand.

```purescript
type BrandVoice =
  { tone :: Tone
  , traits :: TraitSet
  , vocabulary :: Vocabulary
  , constraints :: VoiceConstraints
  }

mkBrandVoice :: Tone -> TraitSet -> Vocabulary -> BrandVoice
mkBrandVoiceWithConstraints :: Tone -> TraitSet -> Vocabulary -> VoiceConstraints -> BrandVoice
defaultVoice :: BrandVoice  -- Casual, friendly/approachable
```

────────────────────────────────────────────────────────────────────────────────
                                                              // logo // system
────────────────────────────────────────────────────────────────────────────────

## Logo/ Directory (9 files)

Complete logo specification from SMART Brand Ingestion Framework §9-14.

### Components.purs (114 lines)

Logo component types and descriptions.

```purescript
data LogoComponent = Icon | Wordmark

type IconDescription = -- Description of icon/mark
type WordmarkDescription = -- Description of wordmark
type LogoSymbolism = -- Meaning/symbolism explanation
```

### Orientation.purs (54 lines)

```purescript
data Orientation = Horizontal | Vertical | Square
```

### Variants.purs (102 lines)

Color variants for logo usage.

```purescript
data ColorVariant
  = FullColor    -- Primary full-color version
  | BlackWhite   -- Pure black/white
  | Reversed     -- For dark backgrounds
  | SingleColor  -- Single brand color

type VariantSet = { variants :: Array ColorVariant }
mkVariantSet :: Array ColorVariant -> Maybe VariantSet  -- Must have >= 1
```

### ClearSpace.purs (89 lines)

Minimum clearance around logos.

```purescript
type ClearSpaceMultiplier  -- e.g., 1.5x height
type ClearSpaceReference   -- What measurement to multiply
type ClearSpaceRule = { multiplier, reference }
```

### Sizing.purs (87 lines)

Minimum size constraints.

```purescript
type PrintSize     -- Minimum print size (inches/mm)
type DigitalSize   -- Minimum digital size (pixels)
type SizeConstraint = { print :: PrintSize, digital :: DigitalSize }
```

### Lockup.purs (198 lines)

Logo lockups — specific arrangements of logo components.

```purescript
data LockupPriority = Primary | Secondary | Tertiary

data UsageContext
  = Letterhead | BusinessCard | EmailSignature
  | SocialProfile | WebsiteHeader | AppIcon | Favicon
  | Merchandise | PrintAdvertising | DigitalAdvertising
  | Presentation | Video

type LogoLockup =
  { name :: LockupName
  , components :: Array LogoComponent
  , orientation :: Orientation
  , priority :: LockupPriority
  , variants :: VariantSet
  , contexts :: Array UsageContext
  , approvedBackgrounds :: Array BackgroundColor
  , clearSpace :: ClearSpaceRule
  , minSize :: SizeConstraint
  }
```

### Errors.purs (142 lines)

Logo misuse patterns (the "Do Not" list).

```purescript
data ErrorCategory
  = ContrastError     -- Poor contrast with background
  | ColorError        -- Wrong colors used
  | DistortionError   -- Stretched, skewed, rotated
  | LayoutError       -- Incorrect arrangement
  | ClearSpaceError   -- Insufficient clearance

type LogoError = { category :: ErrorCategory, description :: String }
type LogoErrorSet = { errors :: Array LogoError }
```

### Rules.purs (121 lines)

Usage rules for watermarks and social media.

```purescript
type WatermarkOpacity  -- 0.0 to 1.0
type WatermarkRule = { opacity :: WatermarkOpacity, lockupRef :: LockupName }

data SocialPlatform
  = Twitter | LinkedIn | Facebook | Instagram
  | YouTube | TikTok | Discord | Slack

type SocialRule = { platform :: SocialPlatform, lockup :: LockupName }
```

### System.purs (189 lines)

Complete logo system compound.

```purescript
type LogoSystem =
  { primary :: LogoLockup
  , alternates :: Array LogoLockup
  , errors :: LogoErrorSet
  , watermark :: Maybe WatermarkRule
  , socialRules :: Array SocialRule
  , iconDescription :: Maybe IconDescription
  , wordmarkDescription :: Maybe WordmarkDescription
  , symbolism :: Maybe LogoSymbolism
  }

findLockupByName :: LockupName -> LogoSystem -> Maybe LogoLockup
findLockupsForContext :: UsageContext -> LogoSystem -> Array LogoLockup
validateLogoSystem :: LogoSystem -> Array String  -- Validation warnings
```

────────────────────────────────────────────────────────────────────────────────
                                                                     // tokens
────────────────────────────────────────────────────────────────────────────────

## Token.purs (234 lines)

Design token infrastructure — the atomic units of a design system.

**Atoms:**

### TokenName
Semantic identifier in hierarchical dot-notation.

```purescript
newtype TokenName = TokenName String
mkTokenName :: String -> Maybe TokenName
tokenNameFromParts :: Array String -> Maybe TokenName
tokenNameParts :: TokenName -> Array String
```

Examples: `"color.primary.500"`, `"spacing.md"`, `"type.heading.h1"`

Naming rules:
- 2-128 characters
- Lowercase letters, numbers, dots, hyphens only
- No leading/trailing/consecutive dots

### TokenDesc
Human-readable explanation of token purpose.

```purescript
newtype TokenDesc = TokenDesc String
mkTokenDesc :: String -> TokenDesc
```

Good: "Primary brand color for interactive elements"
Bad: "Blue color" (describes value, not purpose)

### TokenCategory
Categories matching design system pillars:

```purescript
data TokenCategory
  = CategoryColor      -- Color values
  | CategorySpacing    -- Padding, margin, gap
  | CategorySize       -- Width, height
  | CategoryRadius     -- Corner radius
  | CategoryShadow     -- Shadow definitions
  | CategoryType       -- Typography
  | CategoryDuration   -- Animation timing
  | CategoryEasing     -- Easing curves
  | CategoryZIndex     -- Stacking order
  | CategoryOpacity    -- Alpha values
  | CategoryBorder     -- Border definitions
  | CategoryMotion     -- Animation definitions
  | CategoryBreakpoint -- Responsive breakpoints
  | CategoryAsset      -- Asset references
```

## Token/ Directory (9 files)

Typed tokens for each category.

### Token/Color.purs (247 lines)

```purescript
data ColorRole
  = RolePrimary | RoleSecondary | RoleTertiary | RoleAccent
  | RoleNeutral | RoleBackground | RoleSurface
  | RoleSuccess | RoleWarning | RoleError | RoleInfo
  | RoleOnPrimary | RoleOnSecondary | RoleOnBackground | RoleOnSurface
  | RoleOutline | RoleScrim

data ColorShade
  = Shade50 | Shade100 | Shade200 | Shade300 | Shade400
  | Shade500 | Shade600 | Shade700 | Shade800 | Shade900 | Shade950

type ColorToken = { meta :: TokenMeta, value :: OKLCH, role :: ColorRole }
```

### Token/Spacing.purs, Token/Size.purs, Token/Radius.purs
```purescript
type SpacingToken = { meta :: TokenMeta, value :: Number }
type SizeToken = { meta :: TokenMeta, value :: Number }
type RadiusToken = { meta :: TokenMeta, value :: Number }
```

### Token/Shadow.purs, Token/Duration.purs, Token/Easing.purs
```purescript
type ShadowToken = { meta :: TokenMeta, value :: Shadow }
type DurationToken = { meta :: TokenMeta, value :: Number }  -- Milliseconds
type EasingToken = { meta :: TokenMeta, value :: EasingFunction }
```

### Token/ZIndex.purs, Token/Ref.purs
```purescript
type ZIndexToken = { meta :: TokenMeta, value :: Int }
type TokenRef = { path :: TokenName, fallback :: Maybe String }
```

────────────────────────────────────────────────────────────────────────────────
                                                                     // themes
────────────────────────────────────────────────────────────────────────────────

## Theme.purs (318 lines)

Theme configuration — organizing tokens into switchable configurations.

**Atoms:**

### ThemeMode
Which token values to use for rendering.

```purescript
data ThemeMode
  = ThemeModeLight        -- Light mode (default)
  | ThemeModeDark         -- Dark mode
  | ThemeModeContrast     -- High contrast (accessibility)
  | ThemeModeAuto         -- System preference
  | ThemeModeCustom String  -- Named custom mode
```

### ThemePreference
User/system preference for theme selection.

```purescript
data ThemePreference
  = PreferLight
  | PreferDark
  | PreferContrast
  | PreferSystem
  | PreferTime { lightStart :: Int, darkStart :: Int }  -- Hours (0-23)

resolveAutoTheme :: ThemePreference -> Boolean -> Int -> ThemeMode
```

**Molecules:**

### ThemeTokens
All tokens for a single theme.

```purescript
type ThemeTokens =
  { colors :: Array ColorToken
  , spacing :: Array SpacingToken
  , typography :: Array TypeToken
  , shadows :: Array ShadowToken
  , radii :: Array RadiusToken
  , durations :: Array DurationToken
  , easings :: Array EasingToken
  , zIndices :: Array ZIndexToken
  }

themeTokenCount :: ThemeTokens -> Int
```

**Compound:**

### ThemeSet
Complete set of themes for an application.

```purescript
type ThemeSet =
  { light :: Theme
  , dark :: Theme
  , contrast :: Theme
  , custom :: Array Theme
  }

mkThemeSet :: Theme -> Theme -> Theme -> ThemeSet
getThemeForMode :: ThemeMode -> ThemeSet -> Maybe Theme
addCustomTheme :: Theme -> ThemeSet -> ThemeSet
themeSetModes :: ThemeSet -> Array ThemeMode
```

────────────────────────────────────────────────────────────────────────────────
                                                                 // provenance
────────────────────────────────────────────────────────────────────────────────

## Provenance.purs (189 lines)

Content-addressed provenance for brand data integrity.

**Atoms:**

### ContentHash
SHA256 hash as 64 hexadecimal characters.

```purescript
newtype ContentHash = ContentHash String
mkContentHash :: String -> Maybe ContentHash  -- Validates 64 hex chars
sha256 :: String -> ContentHash  -- Computed at Haskell boundary
```

This is the primary key for content-addressed storage.

### Timestamp
Unix timestamp (seconds since 1970-01-01 00:00:00 UTC).

```purescript
newtype Timestamp = Timestamp Int
mkTimestamp :: Int -> Timestamp  -- Clamps negative to 0
timestampDiff :: Timestamp -> Timestamp -> Int
```

### SourceURL
Validated URL with scheme, domain, path.

```purescript
data Scheme = HTTP | HTTPS

type SourceURL = { scheme :: Scheme, domain :: String, path :: String }
mkSourceURL :: Scheme -> String -> String -> Maybe SourceURL
sourceURLToString :: SourceURL -> String
```

**Compound:**

### Provenance
Complete provenance record.

```purescript
type Provenance =
  { sourceUrl :: SourceURL
  , ingestedAt :: Timestamp
  , contentHash :: ContentHash
  }

mkProvenance :: SourceURL -> Timestamp -> ContentHash -> Provenance
isStale :: Provenance -> Timestamp -> Int -> Boolean
sameContent :: Provenance -> Provenance -> Boolean
```

### StorageKey
Key for content-addressed storage.

```purescript
type StorageKey = { brandUUID :: String, contentHash :: ContentHash }
toHAMTKey :: StorageKey -> String      -- Content hash only
toDuckDBKey :: StorageKey -> String    -- "uuid:hash" format
```

────────────────────────────────────────────────────────────────────────────────
                                                       // compound // brand type
────────────────────────────────────────────────────────────────────────────────

## Brand.purs (213 lines)

The top-level Brand type — what brand ingestion produces and agents consume.

```purescript
type Brand =
  { identity :: BrandIdentity
  , palette :: BrandPalette
  , typography :: BrandTypography
  , spacing :: BrandSpacing
  , voice :: BrandVoice
  , logo :: Maybe LogoSystem
  , provenance :: Provenance
  }

mkBrand 
  :: BrandIdentity 
  -> BrandPalette 
  -> BrandTypography 
  -> BrandSpacing 
  -> BrandVoice 
  -> Maybe LogoSystem
  -> SourceURL 
  -> Timestamp 
  -> Brand

brandContentHash :: Brand -> ContentHash
brandsEqual :: Brand -> Brand -> Boolean  -- O(1) via content hash
```

**Invariants (proven in Lean4):**
- `identity.uuid` is deterministic from `identity.domain`
- `palette` has exactly one primary color
- `typography` weights are 100-900, multiples of 100
- `spacing` scale ratio > 1 (monotonically increasing)
- `voice` has at least one trait
- `logo` system has exactly one primary lockup (if present)
- `provenance.contentHash` matches serialized content

────────────────────────────────────────────────────────────────────────────────
                                                                 // compounds
────────────────────────────────────────────────────────────────────────────────

## Compound/ Directory (3 files)

Brand compounds bridge tokens to UI components.

### Compound/Types.purs
Component styling via token references.

```purescript
-- Example: Button compound
type ButtonCompound =
  { background :: TokenRef        -- "color.primary.500"
  , text :: TokenRef              -- "color.on-primary"
  , radius :: TokenRef            -- "radius.md"
  , paddingX :: TokenRef          -- "spacing.4"
  , paddingY :: TokenRef          -- "spacing.2"
  , hoverBackground :: TokenRef   -- "color.primary.600"
  , activeBackground :: TokenRef  -- "color.primary.700"
  }
```

Components covered:
- **Interactive**: Button, IconButton, Link, Toggle, Switch, Checkbox, Radio, Select, Slider
- **Containers**: Card, Alert, Modal, Dialog, Sheet, Accordion, Collapsible, Tabs
- **Data Display**: Badge, Avatar, Tag, Chip, Table, DataGrid, List, Tooltip, Popover
- **Form**: Input, Textarea, SearchInput, DatePicker, TimePicker, ColorPicker
- **Feedback**: Toast, Alert, Progress, Skeleton, Spinner, LoadingBar
- **Navigation**: Breadcrumb, Tabs, Menu, Sidebar, Pagination, Stepper

### Compound/PropertyRef.purs
Property references with fallbacks.

### Compound/State.purs
Interactive state tokens (hover, active, focus, disabled).

────────────────────────────────────────────────────────────────────────────────
                                                       // supporting // modules
────────────────────────────────────────────────────────────────────────────────

## Typography.purs (156 lines)

Brand typography configuration.

```purescript
type BrandTypography =
  { headingFamily :: FontFamily
  , bodyFamily :: FontFamily
  , monoFamily :: FontFamily
  , regularWeight :: FontWeight
  , boldWeight :: FontWeight
  , scale :: TypeScale
  }

data FontWeight
  = Thin | ExtraLight | Light | Regular
  | Medium | SemiBold | Bold | ExtraBold | Black

fontWeightToInt :: FontWeight -> Int  -- 100-900
```

## Spacing.purs (124 lines)

Brand spacing system.

```purescript
data SpacingSystem
  = GridSpacing Int          -- 4px or 8px grid
  | GeometricSpacing Number  -- Golden ratio, etc.
  | CustomSpacing (Array Number)

type BrandSpacing =
  { system :: SpacingSystem
  , unit :: SpacingUnit
  , scale :: SpacingScale
  }

grid4 :: BrandSpacing  -- 4px grid: 4, 8, 12, 16, 20, 24...
grid8 :: BrandSpacing  -- 8px grid: 8, 16, 24, 32, 40...
```

## ColorSystem.purs — Extended color system with shades
## Mission.purs — Brand mission and values
## Values.purs — Core brand values
## Tagline.purs — Brand tagline/slogan

────────────────────────────────────────────────────────────────────────────────
                                                             // file // summary
────────────────────────────────────────────────────────────────────────────────

| File | Lines | Purpose |
|------|------:|---------|
| Brand.purs | 213 | Top-level Brand compound |
| Identity.purs | 188 | Domain, BrandName, UUID, BrandIdentity |
| Palette.purs | 261 | OKLCH atoms, roles, BrandPalette |
| Voice.purs | 451 | Tone, Trait, IS/NOT, BrandVoice |
| Typography.purs | 156 | FontFamily, FontWeight, TypeScale |
| Spacing.purs | 124 | SpacingSystem, BrandSpacing |
| ColorSystem.purs | ~100 | Extended color shades |
| Provenance.purs | 189 | ContentHash, Timestamp, SourceURL |
| Token.purs | 234 | TokenName, TokenCategory, TokenMeta |
| Token/*.purs | ~650 | Typed tokens (Color, Spacing, etc.) |
| Theme.purs | 318 | ThemeMode, ThemeTokens, ThemeSet |
| Logo.purs | 87 | Leader module for Logo/* |
| Logo/*.purs | ~1,100 | Complete logo system |
| Compound.purs | 52 | Leader module for Compound/* |
| Compound/*.purs | ~380 | Component compounds |
| Mission/Values/Tagline | ~180 | Brand messaging |

**Total: 37 files, ~4,200 lines**

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Content Addressing

Every Brand has a deterministic content hash:

```purescript
hash1 = brandContentHash brand1
hash2 = brandContentHash brand2

-- Same content → Same hash
-- Same hash → Can be compared in O(1)
-- Hash serves as storage key
```

Storage layers:
- **L1 (HAMT)**: Content hash as key, O(log32 n) lookup
- **L2 (DuckDB)**: content_hash column, indexed
- **L3 (Postgres)**: content_hash column, indexed, immutable rows

## Deterministic Identity

UUID5 derives identity from domain:

```purescript
uuid = uuid5(brandNamespace, "example.com")
-- Always produces the same UUID for "example.com"
-- Different from "other.com"
```

This enables distributed systems to identify brands without coordination.

## The IS/NOT Pattern

From SMART Brand Ingestion Framework:

> "The IS/NOT pattern is the most valuable part of any brand voice 
>  specification. It converts subjective tone guidance into enforceable 
>  constraints. Always prioritize capturing this data."

Instead of vague guidance like "be authoritative but not arrogant", the IS/NOT
pattern gives concrete terms:

```
Authoritative:
  IS: knowledgeable, trusted, confident, credible
  IS NOT: overbearing, pompous, condescending
```

AI content generation can programmatically check: "Does this copy violate any
IS NOT terms?" — enabling automated brand voice enforcement.

## Theme Composition

Themes compose tokens into switchable configurations:

```
Light Theme → { color.primary: OKLCH(0.65, 0.24, 240), ... }
Dark Theme  → { color.primary: OKLCH(0.75, 0.28, 240), ... }
```

Components reference tokens by name. Theme switch changes resolved values.
Same components, different themes, different visual output — deterministically.

────────────────────────────────────────────────────────────────────────────────
                                                                 // invariants
────────────────────────────────────────────────────────────────────────────────

**Proven in Lean4:**

| Invariant | Module | Description |
|-----------|--------|-------------|
| uuid5_deterministic | Identity | Same domain = same UUID |
| uuid5_injective | Identity | Different domains = different UUIDs |
| domain_valid | Identity | Non-empty, contains dot |
| brand_name_bounded | Identity | 1 <= length <= 256 |
| has_primary | Palette | Palette always has primary color |
| unique_roles | Palette | Each role appears at most once |
| in_gamut | Palette | All OKLCH colors within bounds |
| traits_nonempty | Voice | Every brand has >= 1 trait |
| traits_unique | Voice | No duplicate traits |
| tone_exclusive | Voice | Exactly one tone |
| vocabulary_disjoint | Voice | Preferred ∩ Prohibited = ∅ |
| is_not_disjoint | Voice | IS ∩ IS NOT = ∅ per attribute |
| hash_deterministic | Provenance | Same content = same hash |
| hash_injective | Provenance | Different content = different hash |
| timestamp_ordered | Provenance | Timestamps totally ordered |
| lockup_has_variants | Logo | Every lockup has >= 1 variant |
| clear_space_positive | Logo | Clear space multiplier > 0 |
| primary_lockup_exists | Logo | System has exactly one primary |

────────────────────────────────────────────────────────────────────────────────

                                                             — Hydrogen Schema
                                                                    Brand Pillar
                                                                       // 2026

────────────────────────────────────────────────────────────────────────────────
