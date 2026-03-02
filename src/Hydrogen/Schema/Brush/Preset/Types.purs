-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brush // preset // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Preset Types — The taxonomy of creative intent.
-- |
-- | ## Design Philosophy
-- |
-- | A brush preset is not merely configuration — it is *crystallized intent*.
-- | When an artist selects "Dry Media > Charcoal > Willow", they are not
-- | choosing parameters. They are invoking a century of art school tradition,
-- | the smell of fixative, the soft whisper of carbon on tooth.
-- |
-- | We organize presets by CREATIVE LINEAGE, not technical category:
-- |
-- | **Traditional Media** — Tools that existed before electricity
-- |   Pencils, charcoal, conte, ink, watercolor, oil, pastel
-- |
-- | **Digital Native** — Tools born in the pixel realm  
-- |   Airbrush, pixel art, glow, glitch, procedural
-- |
-- | **Hybrid** — Traditional media reimagined digitally
-- |   Watercolor with undo, oil with infinite canvas
-- |
-- | **Expressive** — Tools for emotional texture
-- |   Anxiety, calm, rage, tenderness, nostalgia
-- |
-- | ## The Attestation Layer
-- |
-- | Every preset carries provenance:
-- |   - Who created it (human or AI)
-- |   - What tradition it descends from
-- |   - What emotional register it serves
-- |
-- | This matters for billion-agent scale: when an AI requests "a brush
-- | that feels like Sunday morning", the system can respond with semantic
-- | understanding, not keyword matching.
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Attestation.UUID5

module Hydrogen.Schema.Brush.Preset.Types
  ( -- * Preset Category (Top Level)
    PresetCategory(Traditional, DigitalNative, Hybrid, Expressive, Utility, Experimental)
  , allPresetCategories
  , categoryDescription
  , categoryToId
  , categoryLineage
  
  -- * Traditional Media
  , TraditionalMedium(DryMedia, WetMedia, PrintMedia, SculpturalMedia)
  , allTraditionalMedia
  , mediumDescription
  , mediumToId
  , mediumCentury
  , mediumRequiresFixative
  
  -- * Dry Media (Pencil, Charcoal, Pastel)
  , DryMedium(Graphite, ColoredPencil, Charcoal, Conte, SoftPastel, OilPastel, Chalk, Crayon)
  , allDryMedia
  , dryMediumDescription
  , dryMediumToId
  , dryMediumHardness
  
  -- * Wet Media (Ink, Watercolor, Oil)
  , WetMedium(Ink, Watercolor, Gouache, Acrylic, OilPaint, Encaustic, Tempera, Fresco)
  , allWetMedia
  , wetMediumDescription
  , wetMediumToId
  , wetMediumDryTime
  
  -- * Digital Native
  , DigitalTool(PixelBrush, Airbrush, GlowBrush, NoiseBrush, GlitchBrush, VectorBrush, ParticleBrush, CloneBrush, HealBrush, GenerativeBrush)
  , allDigitalTools
  , digitalToolDescription
  , digitalToolToId
  , digitalToolEra
  
  -- * Expressive Register
  , ExpressiveRegister(Calm, Anxious, Melancholic, Joyful, Rage, Tender, Nostalgic, Awe, Grief, Playful)
  , allExpressiveRegisters
  , registerDescription
  , registerToId
  , registerValence
  , registerArousal
  
  -- * Preset Provenance
  , PresetProvenance(BuiltIn, HumanAuthored, AIGenerated, CommunityContributed, Procedural, Unknown)
  , provenanceToId
  , isHumanAuthored
  , isAIGenerated
  , isCommunityContributed
  
  -- * Preset Metadata
  , PresetMeta
  , mkPresetMeta
  , metaName
  , metaCategory
  , metaProvenance
  , metaTags
  , metaUUID
  -- * Query Utilities
  , sameName
  , matchesCategory
  , isSofterThan
  , isHarderThan
  , isPositiveValence
  , isHighArousal
  , isCalming
  , isIntense
  , presetDebugInfo
  , mapPresets
  , showPresetName
  , showCategoryWithLineage
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (>=)
  , (<=)
  , (<>)
  , (&&)
  , (||)
  , map
  , negate
  )

import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // preset category
-- ═════════════════════════════════════════════════════════════════════════════

-- | Top-level preset categories organized by creative lineage.
data PresetCategory
  = Traditional      -- ^ Tools that existed before electricity
  | DigitalNative    -- ^ Tools born in the pixel realm
  | Hybrid           -- ^ Traditional media reimagined digitally
  | Expressive       -- ^ Tools for emotional texture
  | Utility          -- ^ Technical tools (selection, masking)
  | Experimental     -- ^ Cutting edge, unstable, weird

derive instance eqPresetCategory :: Eq PresetCategory
derive instance ordPresetCategory :: Ord PresetCategory

instance showPresetCategory :: Show PresetCategory where
  show Traditional = "(PresetCategory Traditional)"
  show DigitalNative = "(PresetCategory DigitalNative)"
  show Hybrid = "(PresetCategory Hybrid)"
  show Expressive = "(PresetCategory Expressive)"
  show Utility = "(PresetCategory Utility)"
  show Experimental = "(PresetCategory Experimental)"

-- | All preset categories.
allPresetCategories :: Array PresetCategory
allPresetCategories =
  [ Traditional
  , DigitalNative
  , Hybrid
  , Expressive
  , Utility
  , Experimental
  ]

-- | Human-readable description.
categoryDescription :: PresetCategory -> String
categoryDescription Traditional =
  "Tools rooted in centuries of art tradition — pencil, charcoal, oil, watercolor"
categoryDescription DigitalNative =
  "Tools that could only exist in the digital realm — pixel, glow, procedural"
categoryDescription Hybrid =
  "Traditional media reimagined with digital superpowers — infinite undo, perfect color"
categoryDescription Expressive =
  "Tools designed for emotional texture rather than physical simulation"
categoryDescription Utility =
  "Technical tools for selection, masking, and correction"
categoryDescription Experimental =
  "Cutting edge brushes — unstable, weird, wonderful"

-- | Category ID for serialization.
categoryToId :: PresetCategory -> String
categoryToId Traditional = "traditional"
categoryToId DigitalNative = "digital-native"
categoryToId Hybrid = "hybrid"
categoryToId Expressive = "expressive"
categoryToId Utility = "utility"
categoryToId Experimental = "experimental"

-- | The conceptual lineage of each category.
categoryLineage :: PresetCategory -> String
categoryLineage Traditional = "cave paintings → renaissance → impressionism → you"
categoryLineage DigitalNative = "oscilloscope → Sketchpad (1963) → digital painting → you"
categoryLineage Hybrid = "traditional roots, digital wings"
categoryLineage Expressive = "emotion → gesture → mark"
categoryLineage Utility = "tools in service of vision"
categoryLineage Experimental = "what if...?"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // traditional media
-- ═════════════════════════════════════════════════════════════════════════════

-- | Traditional art media categories.
data TraditionalMedium
  = DryMedia         -- ^ Pencil, charcoal, pastel, conte
  | WetMedia         -- ^ Ink, watercolor, gouache, oil, acrylic
  | PrintMedia       -- ^ Woodcut, etching, lithograph, screen
  | SculpturalMedia  -- ^ Clay, wax (for digital sculpting brushes)

derive instance eqTraditionalMedium :: Eq TraditionalMedium
derive instance ordTraditionalMedium :: Ord TraditionalMedium

instance showTraditionalMedium :: Show TraditionalMedium where
  show DryMedia = "(TraditionalMedium Dry)"
  show WetMedia = "(TraditionalMedium Wet)"
  show PrintMedia = "(TraditionalMedium Print)"
  show SculpturalMedia = "(TraditionalMedium Sculptural)"

-- | All traditional media types.
allTraditionalMedia :: Array TraditionalMedium
allTraditionalMedia =
  [ DryMedia
  , WetMedia
  , PrintMedia
  , SculpturalMedia
  ]

-- | Human-readable description.
mediumDescription :: TraditionalMedium -> String
mediumDescription DryMedia =
  "Dry pigment on paper — pencil, charcoal, pastel, conte crayon"
mediumDescription WetMedia =
  "Liquid pigment — ink, watercolor, gouache, oil, acrylic"
mediumDescription PrintMedia =
  "Printmaking matrices — woodcut, etching, lithograph, screen"
mediumDescription SculpturalMedia =
  "Three-dimensional media — clay, wax, for digital sculpting"

-- | Medium ID for serialization.
mediumToId :: TraditionalMedium -> String
mediumToId DryMedia = "dry"
mediumToId WetMedia = "wet"
mediumToId PrintMedia = "print"
mediumToId SculpturalMedia = "sculptural"

-- | Approximate century of origin.
mediumCentury :: TraditionalMedium -> Int
mediumCentury DryMedia = -30000        -- Cave drawings
mediumCentury WetMedia = -3000         -- Egyptian ink
mediumCentury PrintMedia = 800         -- Chinese woodblock
mediumCentury SculpturalMedia = -25000 -- Venus of Willendorf era

-- | Whether the medium requires fixative to preserve.
mediumRequiresFixative :: TraditionalMedium -> Boolean
mediumRequiresFixative DryMedia = true
mediumRequiresFixative _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // dry media
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specific dry media types.
data DryMedium
  = Graphite         -- ^ Standard pencil (HB, 2B, 6B, etc.)
  | ColoredPencil    -- ^ Wax or oil-based colored pencil
  | Charcoal         -- ^ Vine, willow, compressed
  | Conte            -- ^ Conte crayon (sanguine, sepia, white)
  | SoftPastel       -- ^ Chalk pastel
  | OilPastel        -- ^ Waxy oil pastel
  | Chalk            -- ^ Blackboard chalk
  | Crayon           -- ^ Wax crayon

derive instance eqDryMedium :: Eq DryMedium
derive instance ordDryMedium :: Ord DryMedium

instance showDryMedium :: Show DryMedium where
  show Graphite = "(DryMedium Graphite)"
  show ColoredPencil = "(DryMedium ColoredPencil)"
  show Charcoal = "(DryMedium Charcoal)"
  show Conte = "(DryMedium Conte)"
  show SoftPastel = "(DryMedium SoftPastel)"
  show OilPastel = "(DryMedium OilPastel)"
  show Chalk = "(DryMedium Chalk)"
  show Crayon = "(DryMedium Crayon)"

-- | All dry media.
allDryMedia :: Array DryMedium
allDryMedia =
  [ Graphite
  , ColoredPencil
  , Charcoal
  , Conte
  , SoftPastel
  , OilPastel
  , Chalk
  , Crayon
  ]

-- | Human-readable description.
dryMediumDescription :: DryMedium -> String
dryMediumDescription Graphite =
  "The humble pencil — from technical precision (H) to rich darks (9B)"
dryMediumDescription ColoredPencil =
  "Waxy pigment cores — professional wax-based, oil-based, and lightfast varieties"
dryMediumDescription Charcoal =
  "Pure carbon — vine for ghosts, compressed for thunder"
dryMediumDescription Conte =
  "Iron oxide and clay — the old masters' sketching tool"
dryMediumDescription SoftPastel =
  "Pure pigment barely held together — Sennelier, Unison, Schmincke"
dryMediumDescription OilPastel =
  "Waxy and bold — Sennelier oil pastels, Caran d'Ache Neopastel"
dryMediumDescription Chalk =
  "Calcium carbonate — blackboard memories, gesture drawings"
dryMediumDescription Crayon =
  "Childhood's first mark-making tool — Crayola, Stockmar"

-- | Medium ID for serialization.
dryMediumToId :: DryMedium -> String
dryMediumToId Graphite = "graphite"
dryMediumToId ColoredPencil = "colored-pencil"
dryMediumToId Charcoal = "charcoal"
dryMediumToId Conte = "conte"
dryMediumToId SoftPastel = "soft-pastel"
dryMediumToId OilPastel = "oil-pastel"
dryMediumToId Chalk = "chalk"
dryMediumToId Crayon = "crayon"

-- | Relative hardness (0-100, lower = softer).
dryMediumHardness :: DryMedium -> Int
dryMediumHardness Graphite = 60        -- Varies by grade
dryMediumHardness ColoredPencil = 50   -- Depends on wax content
dryMediumHardness Charcoal = 20        -- Very soft
dryMediumHardness Conte = 70           -- Fairly hard
dryMediumHardness SoftPastel = 10      -- Extremely soft
dryMediumHardness OilPastel = 30       -- Soft and waxy
dryMediumHardness Chalk = 40           -- Medium
dryMediumHardness Crayon = 45          -- Medium-soft

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // wet media
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specific wet media types.
data WetMedium
  = Ink              -- ^ India ink, sumi ink, iron gall
  | Watercolor       -- ^ Transparent watercolor
  | Gouache          -- ^ Opaque watercolor
  | Acrylic          -- ^ Fast-drying plastic polymer
  | OilPaint         -- ^ Slow-drying linseed oil medium
  | Encaustic        -- ^ Hot wax painting
  | Tempera          -- ^ Egg tempera
  | Fresco           -- ^ Pigment in wet plaster

derive instance eqWetMedium :: Eq WetMedium
derive instance ordWetMedium :: Ord WetMedium

instance showWetMedium :: Show WetMedium where
  show Ink = "(WetMedium Ink)"
  show Watercolor = "(WetMedium Watercolor)"
  show Gouache = "(WetMedium Gouache)"
  show Acrylic = "(WetMedium Acrylic)"
  show OilPaint = "(WetMedium Oil)"
  show Encaustic = "(WetMedium Encaustic)"
  show Tempera = "(WetMedium Tempera)"
  show Fresco = "(WetMedium Fresco)"

-- | All wet media.
allWetMedia :: Array WetMedium
allWetMedia =
  [ Ink
  , Watercolor
  , Gouache
  , Acrylic
  , OilPaint
  , Encaustic
  , Tempera
  , Fresco
  ]

-- | Human-readable description.
wetMediumDescription :: WetMedium -> String
wetMediumDescription Ink =
  "Carbon or iron suspended in water — calligraphy, comics, illustration"
wetMediumDescription Watercolor =
  "Transparent washes — let the paper glow through"
wetMediumDescription Gouache =
  "Opaque watercolor — designers' choice, animation backgrounds"
wetMediumDescription Acrylic =
  "Modern workhorse — dries fast, cleans with water, tough as nails"
wetMediumDescription OilPaint =
  "The Renaissance medium — slow drying, infinite blending"
wetMediumDescription Encaustic =
  "Hot wax and pigment — Fayum portraits, Jasper Johns"
wetMediumDescription Tempera =
  "Egg yolk binder — Botticelli, Andrew Wyeth"
wetMediumDescription Fresco =
  "Pigment in wet plaster — Sistine ceiling, Diego Rivera"

-- | Medium ID for serialization.
wetMediumToId :: WetMedium -> String
wetMediumToId Ink = "ink"
wetMediumToId Watercolor = "watercolor"
wetMediumToId Gouache = "gouache"
wetMediumToId Acrylic = "acrylic"
wetMediumToId OilPaint = "oil"
wetMediumToId Encaustic = "encaustic"
wetMediumToId Tempera = "tempera"
wetMediumToId Fresco = "fresco"

-- | Approximate drying time in hours (0 = instant, -1 = requires heat).
wetMediumDryTime :: WetMedium -> Int
wetMediumDryTime Ink = 0               -- Seconds
wetMediumDryTime Watercolor = 0        -- Minutes
wetMediumDryTime Gouache = 0           -- Minutes
wetMediumDryTime Acrylic = 1           -- Hours
wetMediumDryTime OilPaint = 168        -- Days to weeks
wetMediumDryTime Encaustic = negate 1  -- Requires heat gun
wetMediumDryTime Tempera = 0           -- Fast
wetMediumDryTime Fresco = 24           -- Must work wet

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // digital native
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tools that could only exist in the digital realm.
data DigitalTool
  = PixelBrush       -- ^ Hard-edged pixel placement
  | Airbrush         -- ^ Smooth gradients (existed analog but perfected digital)
  | GlowBrush        -- ^ Additive light effects
  | NoiseBrush       -- ^ Procedural noise patterns
  | GlitchBrush      -- ^ Data corruption aesthetics
  | VectorBrush      -- ^ Resolution-independent strokes
  | ParticleBrush    -- ^ Particle system emission
  | CloneBrush       -- ^ Copy from source region
  | HealBrush        -- ^ Content-aware correction
  | GenerativeBrush  -- ^ AI-assisted mark making

derive instance eqDigitalTool :: Eq DigitalTool
derive instance ordDigitalTool :: Ord DigitalTool

instance showDigitalTool :: Show DigitalTool where
  show PixelBrush = "(DigitalTool Pixel)"
  show Airbrush = "(DigitalTool Airbrush)"
  show GlowBrush = "(DigitalTool Glow)"
  show NoiseBrush = "(DigitalTool Noise)"
  show GlitchBrush = "(DigitalTool Glitch)"
  show VectorBrush = "(DigitalTool Vector)"
  show ParticleBrush = "(DigitalTool Particle)"
  show CloneBrush = "(DigitalTool Clone)"
  show HealBrush = "(DigitalTool Heal)"
  show GenerativeBrush = "(DigitalTool Generative)"

-- | All digital tools.
allDigitalTools :: Array DigitalTool
allDigitalTools =
  [ PixelBrush
  , Airbrush
  , GlowBrush
  , NoiseBrush
  , GlitchBrush
  , VectorBrush
  , ParticleBrush
  , CloneBrush
  , HealBrush
  , GenerativeBrush
  ]

-- | Human-readable description.
digitalToolDescription :: DigitalTool -> String
digitalToolDescription PixelBrush =
  "Hard-edged pixel placement — 8-bit aesthetics, sprite art"
digitalToolDescription Airbrush =
  "Smooth gradients — the first digital painting tool (1980s)"
digitalToolDescription GlowBrush =
  "Additive light — neon signs, magic effects, UI highlights"
digitalToolDescription NoiseBrush =
  "Procedural noise — Perlin, simplex, worley — infinite texture"
digitalToolDescription GlitchBrush =
  "Data corruption as aesthetic — databending, pixel sorting"
digitalToolDescription VectorBrush =
  "Resolution-independent strokes — scale forever"
digitalToolDescription ParticleBrush =
  "Particle system emission — sparks, smoke, magic dust"
digitalToolDescription CloneBrush =
  "Sample from source, paint to destination — a powerful compositing technique"
digitalToolDescription HealBrush =
  "Content-aware correction — magic eraser for blemishes"
digitalToolDescription GenerativeBrush =
  "AI-assisted mark making — the brush completes your gesture"

-- | Tool ID for serialization.
digitalToolToId :: DigitalTool -> String
digitalToolToId PixelBrush = "pixel"
digitalToolToId Airbrush = "airbrush"
digitalToolToId GlowBrush = "glow"
digitalToolToId NoiseBrush = "noise"
digitalToolToId GlitchBrush = "glitch"
digitalToolToId VectorBrush = "vector"
digitalToolToId ParticleBrush = "particle"
digitalToolToId CloneBrush = "clone"
digitalToolToId HealBrush = "heal"
digitalToolToId GenerativeBrush = "generative"

-- | Approximate era of introduction.
digitalToolEra :: DigitalTool -> String
digitalToolEra PixelBrush = "1970s — early raster graphics"
digitalToolEra Airbrush = "1982 — Quantel Paintbox"
digitalToolEra GlowBrush = "1990s — layer blend modes"
digitalToolEra NoiseBrush = "1985 — Ken Perlin's noise"
digitalToolEra GlitchBrush = "2000s — glitch art movement"
digitalToolEra VectorBrush = "1987 — professional vector graphics"
digitalToolEra ParticleBrush = "1990s — game VFX"
digitalToolEra CloneBrush = "1990 — digital image editing era"
digitalToolEra HealBrush = "2002 — content-aware editing era"
digitalToolEra GenerativeBrush = "2022 — diffusion models"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // expressive register
-- ═════════════════════════════════════════════════════════════════════════════

-- | Emotional registers for expressive brushes.
-- |
-- | These are not simulations of physical media. They are tools designed
-- | to channel specific emotional states into marks. When an artist feels
-- | rage, they should reach for a brush that *embodies* rage — aggressive
-- | jitter, explosive scatter, red-shifted color dynamics.
-- |
-- | This is new. This is what digital painting should have been all along.
data ExpressiveRegister
  = Calm             -- ^ Slow, smooth, centered
  | Anxious          -- ^ Jittery, unstable, seeking edges
  | Melancholic      -- ^ Heavy, trailing, desaturated
  | Joyful           -- ^ Light, bouncy, saturated
  | Rage             -- ^ Aggressive, explosive, hard
  | Tender           -- ^ Soft, careful, intimate
  | Nostalgic        -- ^ Faded, warm, slightly blurred
  | Awe              -- ^ Expansive, luminous, overwhelming
  | Grief            -- ^ Broken, fragmentary, searching
  | Playful          -- ^ Irregular, surprising, delightful

derive instance eqExpressiveRegister :: Eq ExpressiveRegister
derive instance ordExpressiveRegister :: Ord ExpressiveRegister

instance showExpressiveRegister :: Show ExpressiveRegister where
  show Calm = "(ExpressiveRegister Calm)"
  show Anxious = "(ExpressiveRegister Anxious)"
  show Melancholic = "(ExpressiveRegister Melancholic)"
  show Joyful = "(ExpressiveRegister Joyful)"
  show Rage = "(ExpressiveRegister Rage)"
  show Tender = "(ExpressiveRegister Tender)"
  show Nostalgic = "(ExpressiveRegister Nostalgic)"
  show Awe = "(ExpressiveRegister Awe)"
  show Grief = "(ExpressiveRegister Grief)"
  show Playful = "(ExpressiveRegister Playful)"

-- | All expressive registers.
allExpressiveRegisters :: Array ExpressiveRegister
allExpressiveRegisters =
  [ Calm
  , Anxious
  , Melancholic
  , Joyful
  , Rage
  , Tender
  , Nostalgic
  , Awe
  , Grief
  , Playful
  ]

-- | Human-readable description.
registerDescription :: ExpressiveRegister -> String
registerDescription Calm =
  "Slow and smooth — strokes that breathe, centered marks"
registerDescription Anxious =
  "Jittery and unstable — the brush searches for edges that aren't there"
registerDescription Melancholic =
  "Heavy and trailing — marks that don't want to lift, colors that fade"
registerDescription Joyful =
  "Light and bouncy — saturated color, marks that dance"
registerDescription Rage =
  "Aggressive and explosive — hard edges, red shift, maximum scatter"
registerDescription Tender =
  "Soft and careful — intimate marks, gentle pressure response"
registerDescription Nostalgic =
  "Faded and warm — sepia shift, soft focus, light grain"
registerDescription Awe =
  "Expansive and luminous — marks that reach beyond themselves"
registerDescription Grief =
  "Broken and fragmentary — the stroke can't complete, searching for what's lost"
registerDescription Playful =
  "Irregular and surprising — the brush has a mind of its own"

-- | Register ID for serialization.
registerToId :: ExpressiveRegister -> String
registerToId Calm = "calm"
registerToId Anxious = "anxious"
registerToId Melancholic = "melancholic"
registerToId Joyful = "joyful"
registerToId Rage = "rage"
registerToId Tender = "tender"
registerToId Nostalgic = "nostalgic"
registerToId Awe = "awe"
registerToId Grief = "grief"
registerToId Playful = "playful"

-- | Emotional valence (-100 = negative, +100 = positive).
-- | Based on Russell's circumplex model of affect.
registerValence :: ExpressiveRegister -> Int
registerValence Calm = 20              -- Slightly positive
registerValence Anxious = negate 40    -- Negative
registerValence Melancholic = negate 50 -- Negative
registerValence Joyful = 80            -- Very positive
registerValence Rage = negate 70       -- Very negative
registerValence Tender = 60            -- Positive
registerValence Nostalgic = 10         -- Bittersweet, slightly positive
registerValence Awe = 50               -- Positive, mixed
registerValence Grief = negate 80      -- Very negative
registerValence Playful = 70           -- Positive

-- | Emotional arousal (0 = low energy, 100 = high energy).
-- | Based on Russell's circumplex model of affect.
registerArousal :: ExpressiveRegister -> Int
registerArousal Calm = 10              -- Very low
registerArousal Anxious = 80           -- High
registerArousal Melancholic = 20       -- Low
registerArousal Joyful = 70            -- High
registerArousal Rage = 95              -- Maximum
registerArousal Tender = 30            -- Low-medium
registerArousal Nostalgic = 25         -- Low
registerArousal Awe = 60               -- Medium-high
registerArousal Grief = 40             -- Medium (grief can be quiet or loud)
registerArousal Playful = 75           -- High

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // preset provenance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Provenance of a preset — who created it and how.
-- |
-- | This matters for trust, attribution, and understanding.
-- | When an AI agent requests a brush, knowing whether it was
-- | crafted by a human master or generated procedurally affects
-- | how we present and explain it.
data PresetProvenance
  = BuiltIn String             -- ^ Ships with Hydrogen, creator name
  | HumanAuthored String       -- ^ Created by named human artist
  | AIGenerated String         -- ^ Generated by AI system (model name)
  | CommunityContributed String -- ^ Community submission, contributor name
  | Procedural                 -- ^ Algorithmically generated at runtime
  | Unknown                    -- ^ Provenance lost to history

derive instance eqPresetProvenance :: Eq PresetProvenance
derive instance ordPresetProvenance :: Ord PresetProvenance

instance showPresetProvenance :: Show PresetProvenance where
  show (BuiltIn name) = "(Provenance BuiltIn " <> name <> ")"
  show (HumanAuthored name) = "(Provenance HumanAuthored " <> name <> ")"
  show (AIGenerated model) = "(Provenance AIGenerated " <> model <> ")"
  show (CommunityContributed name) = "(Provenance Community " <> name <> ")"
  show Procedural = "(Provenance Procedural)"
  show Unknown = "(Provenance Unknown)"

-- | Provenance ID for serialization.
provenanceToId :: PresetProvenance -> String
provenanceToId (BuiltIn _) = "builtin"
provenanceToId (HumanAuthored _) = "human"
provenanceToId (AIGenerated _) = "ai"
provenanceToId (CommunityContributed _) = "community"
provenanceToId Procedural = "procedural"
provenanceToId Unknown = "unknown"

-- | Check if preset was created by a human.
isHumanAuthored :: PresetProvenance -> Boolean
isHumanAuthored (HumanAuthored _) = true
isHumanAuthored (BuiltIn _) = true  -- Built-ins are human-curated
isHumanAuthored (CommunityContributed _) = true
isHumanAuthored _ = false

-- | Check if preset was AI-generated.
isAIGenerated :: PresetProvenance -> Boolean
isAIGenerated (AIGenerated _) = true
isAIGenerated _ = false

-- | Check if preset is community-contributed.
isCommunityContributed :: PresetProvenance -> Boolean
isCommunityContributed (CommunityContributed _) = true
isCommunityContributed _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // preset metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace for preset UUIDs.
nsPreset :: UUID5.UUID5
nsPreset = UUID5.uuid5 UUID5.nsElement "hydrogen.brush.preset"

-- | Metadata for a brush preset.
-- |
-- | This is the "envelope" around actual brush configuration.
-- | It carries the identity, categorization, and provenance.
type PresetMeta =
  { name :: String
  , category :: PresetCategory
  , provenance :: PresetProvenance
  , tags :: Array String
  , description :: String
  , uuid :: UUID5.UUID5
  }

-- | Create preset metadata with computed UUID.
mkPresetMeta :: String -> PresetCategory -> PresetProvenance -> Array String -> String -> PresetMeta
mkPresetMeta name category provenance tags description =
  { name: name
  , category: category
  , provenance: provenance
  , tags: tags
  , description: description
  , uuid: UUID5.uuid5 nsPreset (name <> ":" <> categoryToId category)
  }

-- | Get preset name.
metaName :: PresetMeta -> String
metaName m = m.name

-- | Get preset category.
metaCategory :: PresetMeta -> PresetCategory
metaCategory m = m.category

-- | Get preset provenance.
metaProvenance :: PresetMeta -> PresetProvenance
metaProvenance m = m.provenance

-- | Get preset tags.
metaTags :: PresetMeta -> Array String
metaTags m = m.tags

-- | Get preset UUID.
metaUUID :: PresetMeta -> UUID5.UUID5
metaUUID m = m.uuid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // query utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two presets have the same name.
sameName :: PresetMeta -> PresetMeta -> Boolean
sameName a b = a.name == b.name

-- | Check if preset matches category.
matchesCategory :: PresetMeta -> PresetCategory -> Boolean
matchesCategory meta cat = meta.category == cat

-- | Check if dry medium is softer than a threshold.
isSofterThan :: DryMedium -> Int -> Boolean
isSofterThan medium threshold = dryMediumHardness medium <= threshold

-- | Check if dry medium is harder than a threshold.
isHarderThan :: DryMedium -> Int -> Boolean
isHarderThan medium threshold = dryMediumHardness medium >= threshold

-- | Check if register is positive valence.
isPositiveValence :: ExpressiveRegister -> Boolean
isPositiveValence reg = registerValence reg >= 0

-- | Check if register is high arousal.
isHighArousal :: ExpressiveRegister -> Boolean
isHighArousal reg = registerArousal reg >= 60

-- | Check if register is calm (low arousal, non-negative valence).
isCalming :: ExpressiveRegister -> Boolean
isCalming reg = registerArousal reg <= 30 && registerValence reg >= 0

-- | Check if register is intense (high arousal OR extreme valence).
isIntense :: ExpressiveRegister -> Boolean
isIntense reg = 
  registerArousal reg >= 70 || 
  registerValence reg >= 70 || 
  registerValence reg <= negate 70

-- | Debug info for preset.
presetDebugInfo :: PresetMeta -> String
presetDebugInfo meta =
  "Preset: " <> meta.name <>
  " [" <> categoryToId meta.category <> "]" <>
  " (" <> provenanceToId meta.provenance <> ")" <>
  " — " <> meta.description

-- | Map over all presets in an array.
mapPresets :: (PresetMeta -> PresetMeta) -> Array PresetMeta -> Array PresetMeta
mapPresets f presets = map f presets

-- | Show preset name.
showPresetName :: PresetMeta -> String
showPresetName meta = show meta.name

-- | Show category with lineage.
showCategoryWithLineage :: PresetCategory -> String
showCategoryWithLineage cat =
  categoryToId cat <> " — " <> categoryLineage cat
