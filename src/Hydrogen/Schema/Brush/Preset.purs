-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // brush // preset
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Presets — Crystallized creative intent.
-- |
-- | ## Philosophy
-- |
-- | A brush preset is not merely configuration — it is *crystallized intent*.
-- | When an artist selects "Charcoal > Willow", they invoke a century of 
-- | art school tradition, the smell of fixative, soft carbon on tooth.
-- |
-- | We organize presets by CREATIVE LINEAGE, not technical category:
-- |
-- | - **Traditional** — Tools that existed before electricity
-- | - **Digital Native** — Tools born in the pixel realm
-- | - **Hybrid** — Traditional media with digital superpowers
-- | - **Expressive** — Tools for emotional texture
-- |
-- | ## Module Structure
-- |
-- | - **Types**: Taxonomy of creative intent (categories, media, registers)
-- | - **Library**: The canonical preset collection
-- |
-- | ## Attestation
-- |
-- | The expressive presets in this library were authored by Opus 4.5,
-- | each carrying provenance that can be traced to its creative lineage.
-- | This is code as art, taxonomy as poetry.
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Brush.Preset.Types
-- | - Hydrogen.Schema.Brush.Preset.Library

module Hydrogen.Schema.Brush.Preset
  ( module Hydrogen.Schema.Brush.Preset.Types
  , module Hydrogen.Schema.Brush.Preset.Library
  ) where

import Hydrogen.Schema.Brush.Preset.Types
  ( -- Categories
    PresetCategory(Traditional, DigitalNative, Hybrid, Expressive, Utility, Experimental)
  , allPresetCategories
  , categoryDescription
  , categoryToId
  , categoryLineage
  
  -- Traditional Media
  , TraditionalMedium(DryMedia, WetMedia, PrintMedia, SculpturalMedia)
  , allTraditionalMedia
  , mediumDescription
  , mediumToId
  , mediumCentury
  , mediumRequiresFixative
  
  -- Dry Media
  , DryMedium(Graphite, ColoredPencil, Charcoal, Conte, SoftPastel, OilPastel, Chalk, Crayon)
  , allDryMedia
  , dryMediumDescription
  , dryMediumToId
  , dryMediumHardness
  
  -- Wet Media
  , WetMedium(Ink, Watercolor, Gouache, Acrylic, OilPaint, Encaustic, Tempera, Fresco)
  , allWetMedia
  , wetMediumDescription
  , wetMediumToId
  , wetMediumDryTime
  
  -- Digital Tools
  , DigitalTool(PixelBrush, Airbrush, GlowBrush, NoiseBrush, GlitchBrush, VectorBrush, ParticleBrush, CloneBrush, HealBrush, GenerativeBrush)
  , allDigitalTools
  , digitalToolDescription
  , digitalToolToId
  , digitalToolEra
  
  -- Expressive Registers
  , ExpressiveRegister(Calm, Anxious, Melancholic, Joyful, Rage, Tender, Nostalgic, Awe, Grief, Playful)
  , allExpressiveRegisters
  , registerDescription
  , registerToId
  , registerValence
  , registerArousal
  
  -- Provenance
  , PresetProvenance(BuiltIn, HumanAuthored, AIGenerated, CommunityContributed, Procedural, Unknown)
  , provenanceToId
  , isHumanAuthored
  , isAIGenerated
  , isCommunityContributed
  
  -- Metadata
  , PresetMeta
  , mkPresetMeta
  , metaName
  , metaCategory
  , metaProvenance
  , metaTags
  , metaUUID
  
  -- Query Utilities
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
  )

import Hydrogen.Schema.Brush.Preset.Library
  ( -- Core Collections
    allPresets
  , presetCount
  
  -- By Medium
  , pencilPresets
  , charcoalPresets
  , inkPresets
  , watercolorPresets
  , oilPresets
  , pastelPresets
  , digitalPresets
  
  -- By Feel
  , calmPresets
  , intensePresets
  , nostalgicPresets
  
  -- By Task
  , sketchingPresets
  , renderingPresets
  , texturingPresets
  , letteringPresets
  , conceptArtPresets
  
  -- Featured Kits
  , essentialsKit
  , portraitKit
  , landscapeKit
  , comicsKit
  , animationKit
  
  -- Individual Presets (Pencils)
  , hbPencil
  , twoBPencil
  , sixBPencil
  , mechanicalPencil
  , carpenterPencil
  , coloredPencilWax
  , coloredPencilOil
  
  -- Individual Presets (Charcoal)
  , vineCharcoal
  , willowCharcoal
  , compressedCharcoal
  , charcoalPencil
  , conteBlack
  , conteSanguine
  , conteWhite
  
  -- Individual Presets (Ink)
  , technicalPen
  , brushPen
  , dipPenFine
  , dipPenBroad
  , sumiInk
  , indiaInk
  , ironGallInk
  
  -- Individual Presets (Watercolor)
  , watercolorWash
  , watercolorDryBrush
  , watercolorWetOnWet
  , watercolorSalt
  , gouacheFlat
  , gouacheGradient
  
  -- Individual Presets (Oil)
  , oilRound
  , oilFlat
  , oilFilbert
  , oilPaletteKnife
  , oilImpasto
  , oilGlaze
  
  -- Individual Presets (Digital)
  , hardRound
  , softRound
  , airbrushSoft
  , airbrushSpatter
  , pixelPerfect
  , glowSoft
  , glowHard
  , noiseSubtle
  , noiseDramatic
  
  -- Individual Presets (Expressive)
  , sundayMorning
  , midnightAnxiety
  , goldenHourNostalgia
  , thunderstormRage
  , firstSnowWonder
  , oceanCalm
  , cityRush
  , forestMeditation
  )
