-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // brush
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Schema — Complete vocabulary for digital mark-making.
-- |
-- | ## For Agents Operating at Speed
-- |
-- | Designed for billion-agent swarm scale at 10,000+ tok/sec.
-- | Single import gives you everything. No hierarchy chasing.
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Brush as Brush
-- | myBrush = Brush.willowCharcoal  -- crystallized creative intent
-- | ```
-- |
-- | ## What's Here
-- |
-- | **Presets** — 60+ curated brushes (charcoal, ink, oil, digital, expressive)
-- | **Categories** — Traditional, DigitalNative, Hybrid, Expressive
-- | **Media Types** — DryMedium, WetMedium, DigitalTool
-- | **Expressive Registers** — Calm, Anxious, Joyful, Rage, Tender, Nostalgic
-- | **Tools** — Blend (smudge, liquify), Eraser (alpha, history, auto)
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Brush.Preset (types + library)
-- | - Hydrogen.Schema.Brush.Blend (blend tools)
-- | - Hydrogen.Schema.Brush.Eraser (eraser tools)

module Hydrogen.Schema.Brush
  ( -- * Presets & Types
    module Hydrogen.Schema.Brush.Preset.Types
  , module Hydrogen.Schema.Brush.Preset.Library
  
    -- * Blend Tools
  , module Hydrogen.Schema.Brush.Blend.Types
  , module Hydrogen.Schema.Brush.Blend.Config
  
    -- * Eraser Tools
  , module Hydrogen.Schema.Brush.Eraser.Types
  , module Hydrogen.Schema.Brush.Eraser.Config
  ) where

-- Preset Types (categories, media, registers, metadata)
import Hydrogen.Schema.Brush.Preset.Types
  ( PresetCategory(Traditional, DigitalNative, Hybrid, Expressive, Utility, Experimental)
  , allPresetCategories
  , categoryDescription
  , categoryToId
  , categoryLineage
  , TraditionalMedium(DryMedia, WetMedia, PrintMedia, SculpturalMedia)
  , allTraditionalMedia
  , mediumDescription
  , mediumToId
  , mediumCentury
  , mediumRequiresFixative
  , DryMedium(Graphite, ColoredPencil, Charcoal, Conte, SoftPastel, OilPastel, Chalk, Crayon)
  , allDryMedia
  , dryMediumDescription
  , dryMediumToId
  , dryMediumHardness
  , WetMedium(Ink, Watercolor, Gouache, Acrylic, OilPaint, Encaustic, Tempera, Fresco)
  , allWetMedia
  , wetMediumDescription
  , wetMediumToId
  , wetMediumDryTime
  , DigitalTool(PixelBrush, Airbrush, GlowBrush, NoiseBrush, GlitchBrush, VectorBrush, ParticleBrush, CloneBrush, HealBrush, GenerativeBrush)
  , allDigitalTools
  , digitalToolDescription
  , digitalToolToId
  , digitalToolEra
  , ExpressiveRegister(Calm, Anxious, Melancholic, Joyful, Rage, Tender, Nostalgic, Awe, Grief, Playful)
  , allExpressiveRegisters
  , registerDescription
  , registerToId
  , registerValence
  , registerArousal
  , PresetProvenance(BuiltIn, HumanAuthored, AIGenerated, CommunityContributed, Procedural, Unknown)
  , provenanceToId
  , isHumanAuthored
  , isAIGenerated
  , isCommunityContributed
  , PresetMeta
  , mkPresetMeta
  , metaName
  , metaCategory
  , metaProvenance
  , metaTags
  , metaUUID
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

-- Preset Library (all presets and collections)
import Hydrogen.Schema.Brush.Preset.Library
  ( allPresets
  , presetCount
  , pencilPresets
  , charcoalPresets
  , inkPresets
  , watercolorPresets
  , oilPresets
  , pastelPresets
  , digitalPresets
  , calmPresets
  , intensePresets
  , nostalgicPresets
  , sketchingPresets
  , renderingPresets
  , texturingPresets
  , letteringPresets
  , conceptArtPresets
  , essentialsKit
  , portraitKit
  , landscapeKit
  , comicsKit
  , animationKit
  , hbPencil
  , twoBPencil
  , sixBPencil
  , mechanicalPencil
  , carpenterPencil
  , coloredPencilWax
  , coloredPencilOil
  , vineCharcoal
  , willowCharcoal
  , compressedCharcoal
  , charcoalPencil
  , conteBlack
  , conteSanguine
  , conteWhite
  , technicalPen
  , brushPen
  , dipPenFine
  , dipPenBroad
  , sumiInk
  , indiaInk
  , ironGallInk
  , watercolorWash
  , watercolorDryBrush
  , watercolorWetOnWet
  , watercolorSalt
  , gouacheFlat
  , gouacheGradient
  , oilRound
  , oilFlat
  , oilFilbert
  , oilPaletteKnife
  , oilImpasto
  , oilGlaze
  , hardRound
  , softRound
  , airbrushSoft
  , airbrushSpatter
  , pixelPerfect
  , glowSoft
  , glowHard
  , noiseSubtle
  , noiseDramatic
  , sundayMorning
  , midnightAnxiety
  , goldenHourNostalgia
  , thunderstormRage
  , firstSnowWonder
  , oceanCalm
  , cityRush
  , forestMeditation
  )

-- Blend Tools
import Hydrogen.Schema.Brush.Blend.Types
  ( BlendMode(Smudge, Blur, Sharpen, Blend, Liquify)
  , allBlendModes
  , blendModeDescription
  , blendModeToId
  , blendModeDebugInfo
  , isDestructive
  , LiquifyMode(LiquifyPush, LiquifyTwirl, LiquifyPinch, LiquifyBloat, LiquifyReconstruct)
  , allLiquifyModes
  , liquifyModeDescription
  , liquifyModeToId
  , liquifyModeDebugInfo
  , isReconstructive
  )

import Hydrogen.Schema.Brush.Blend.Config
  ( SmudgeConfig
  , defaultSmudgeConfig
  , fingerSmudgeConfig
  , drySmudgeConfig
  , wetSmudgeConfig
  , LiquifyConfig
  , defaultLiquifyConfig
  , pushLiquifyConfig
  , twirlLiquifyConfig
  , pinchLiquifyConfig
  , bloatLiquifyConfig
  , BlurConfig
  , defaultBlurConfig
  , softBlurConfig
  , strongBlurConfig
  , smudgeConfigDebugInfo
  , liquifyConfigDebugInfo
  )

-- Eraser Tools
import Hydrogen.Schema.Brush.Eraser.Types
  ( EraserMode(AlphaErase, BackgroundErase, LayerErase, AllLayersErase, AutoErase, HistoryErase)
  , allEraserModes
  , eraserModeDescription
  , eraserModeToId
  , eraserModeDebugInfo
  , affectsMultipleLayers
  , sameEraserMode
  )

import Hydrogen.Schema.Brush.Eraser.Config
  ( EraserConfig
  , defaultEraserConfig
  , hardEraserConfig
  , softEraserConfig
  , blockEraserConfig
  , kneadedEraserConfig
  , historyBrushConfig
  , AutoEraseConfig
  , defaultAutoEraseConfig
  , preciseAutoEraseConfig
  , looseAutoEraseConfig
  , HistoryEraseConfig
  , defaultHistoryEraseConfig
  , impressionistHistoryConfig
  , eraserConfigDebugInfo
  )
