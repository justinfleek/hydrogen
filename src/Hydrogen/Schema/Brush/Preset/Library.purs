-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // brush // preset // library
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Preset Library — The canonical collection of brush presets.
-- |
-- | ## Philosophy
-- |
-- | This library is organized by creative intent, not technical parameters.
-- | When an artist or AI agent asks for "something that feels like charcoal",
-- | they get presets that *behave* like charcoal — rough texture, soft edges,
-- | response to paper tooth — not presets that merely have "charcoal" in the name.
-- |
-- | ## Organization
-- |
-- | **By Medium** — Traditional categories (pencil, ink, oil, etc.)
-- | **By Feel** — Expressive registers (calm, anxious, joyful, etc.)  
-- | **By Task** — What you're trying to accomplish (sketch, render, texture)
-- | **By Era** — Historical periods and their aesthetic signatures
-- |
-- | ## Attestation
-- |
-- | Every preset in this library was curated by Opus 4.5 in collaboration
-- | with the Hydrogen project. Presets carry provenance and can be traced
-- | back to their creative lineage.
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Brush.Preset.Types

module Hydrogen.Schema.Brush.Preset.Library
  ( -- * Core Collections
    allPresets
  , presetCount
  
  -- * By Medium
  , pencilPresets
  , charcoalPresets
  , inkPresets
  , watercolorPresets
  , oilPresets
  , pastelPresets
  , digitalPresets
  
  -- * By Feel (Expressive)
  , calmPresets
  , intensePresets
  , nostalgicPresets
  
  -- * By Task
  , sketchingPresets
  , renderingPresets
  , texturingPresets
  , letteringPresets
  , conceptArtPresets
  
  -- * Featured Sets
  , essentialsKit
  , portraitKit
  , landscapeKit
  , comicsKit
  , animationKit
  
  -- * Individual Presets (Pencils)
  , hbPencil
  , twoBPencil
  , sixBPencil
  , mechanicalPencil
  , carpenterPencil
  , coloredPencilWax
  , coloredPencilOil
  
  -- * Individual Presets (Charcoal)
  , vineCharcoal
  , willowCharcoal
  , compressedCharcoal
  , charcoalPencil
  , conteBlack
  , conteSanguine
  , conteWhite
  
  -- * Individual Presets (Ink)
  , technicalPen
  , brushPen
  , dipPenFine
  , dipPenBroad
  , sumiInk
  , indiaInk
  , ironGallInk
  
  -- * Individual Presets (Watercolor)
  , watercolorWash
  , watercolorDryBrush
  , watercolorWetOnWet
  , watercolorSalt
  , gouacheFlat
  , gouacheGradient
  
  -- * Individual Presets (Oil)
  , oilRound
  , oilFlat
  , oilFilbert
  , oilPaletteKnife
  , oilImpasto
  , oilGlaze
  
  -- * Individual Presets (Digital)
  , hardRound
  , softRound
  , airbrushSoft
  , airbrushSpatter
  , pixelPerfect
  , glowSoft
  , glowHard
  , noiseSubtle
  , noiseDramatic
  
  -- * Individual Presets (Expressive)
  , sundayMorning
  , midnightAnxiety
  , goldenHourNostalgia
  , thunderstormRage
  , firstSnowWonder
  , oceanCalm
  , cityRush
  , forestMeditation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  )

import Data.Array (length) as Array

import Hydrogen.Schema.Brush.Preset.Types
  ( PresetMeta
  , PresetCategory(..)
  , PresetProvenance(..)
  , mkPresetMeta
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // core collections
-- ═════════════════════════════════════════════════════════════════════════════

-- | All presets in the library.
allPresets :: Array PresetMeta
allPresets = 
  pencilPresets <> 
  charcoalPresets <> 
  inkPresets <> 
  watercolorPresets <> 
  oilPresets <> 
  pastelPresets <>
  digitalPresets <>
  expressivePresets

-- | Total number of presets.
presetCount :: Int
presetCount = Array.length allPresets

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // pencil presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | All pencil presets.
pencilPresets :: Array PresetMeta
pencilPresets =
  [ hbPencil
  , twoBPencil
  , sixBPencil
  , mechanicalPencil
  , carpenterPencil
  , coloredPencilWax
  , coloredPencilOil
  ]

-- | Standard HB pencil — the workhorse, medium tone.
hbPencil :: PresetMeta
hbPencil = mkPresetMeta
  "HB Pencil"
  Traditional
  (BuiltIn "Hydrogen")
  ["pencil", "graphite", "sketch", "general", "medium"]
  "The standard pencil — not too light, not too dark. Good for everything."

-- | 2B pencil — soft, dark, expressive.
twoBPencil :: PresetMeta
twoBPencil = mkPresetMeta
  "2B Pencil"
  Traditional
  (BuiltIn "Hydrogen")
  ["pencil", "graphite", "sketch", "soft", "dark"]
  "Soft and dark — perfect for expressive sketching and rich shadows."

-- | 6B pencil — very soft, very dark, gesture drawing.
sixBPencil :: PresetMeta
sixBPencil = mkPresetMeta
  "6B Pencil"
  Traditional
  (BuiltIn "Hydrogen")
  ["pencil", "graphite", "gesture", "very-soft", "very-dark"]
  "Extra soft for bold gesture drawings. Smudges beautifully."

-- | Mechanical pencil — precise, technical, consistent.
mechanicalPencil :: PresetMeta
mechanicalPencil = mkPresetMeta
  "Mechanical Pencil 0.5mm"
  Traditional
  (BuiltIn "Hydrogen")
  ["pencil", "mechanical", "technical", "precise", "drafting"]
  "Consistent line weight for technical drawing and precise details."

-- | Carpenter pencil — flat, broad, textural.
carpenterPencil :: PresetMeta
carpenterPencil = mkPresetMeta
  "Carpenter Pencil"
  Traditional
  (BuiltIn "Hydrogen")
  ["pencil", "flat", "broad", "textural", "construction"]
  "Flat lead creates broad strokes and interesting textural marks."

-- | Wax-based colored pencil — smooth, blendable.
coloredPencilWax :: PresetMeta
coloredPencilWax = mkPresetMeta
  "Colored Pencil (Wax)"
  Traditional
  (BuiltIn "Hydrogen")
  ["pencil", "colored", "wax", "smooth", "blendable", "prismacolor"]
  "Creamy wax-based colored pencil — blends smoothly, burnishes well."

-- | Oil-based colored pencil — harder, more precise.
coloredPencilOil :: PresetMeta
coloredPencilOil = mkPresetMeta
  "Colored Pencil (Oil)"
  Traditional
  (BuiltIn "Hydrogen")
  ["pencil", "colored", "oil", "hard", "precise", "polychromos"]
  "Firmer oil-based colored pencil — sharper details, layers cleanly."

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // charcoal presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | All charcoal presets.
charcoalPresets :: Array PresetMeta
charcoalPresets =
  [ vineCharcoal
  , willowCharcoal
  , compressedCharcoal
  , charcoalPencil
  , conteBlack
  , conteSanguine
  , conteWhite
  ]

-- | Vine charcoal — the lightest, most erasable.
vineCharcoal :: PresetMeta
vineCharcoal = mkPresetMeta
  "Vine Charcoal"
  Traditional
  (BuiltIn "Hydrogen")
  ["charcoal", "vine", "light", "erasable", "gesture"]
  "Lightest charcoal — ghosts across paper, erases completely. For first marks."

-- | Willow charcoal — soft, atmospheric.
willowCharcoal :: PresetMeta
willowCharcoal = mkPresetMeta
  "Willow Charcoal"
  Traditional
  (BuiltIn "Hydrogen")
  ["charcoal", "willow", "soft", "atmospheric", "tonal"]
  "Soft and atmospheric — perfect for building values gradually."

-- | Compressed charcoal — dark, intense, permanent.
compressedCharcoal :: PresetMeta
compressedCharcoal = mkPresetMeta
  "Compressed Charcoal"
  Traditional
  (BuiltIn "Hydrogen")
  ["charcoal", "compressed", "dark", "intense", "permanent"]
  "Dense and dark — for the deepest blacks and bold marks. Doesn't lift easily."

-- | Charcoal pencil — controlled charcoal application.
charcoalPencil :: PresetMeta
charcoalPencil = mkPresetMeta
  "Charcoal Pencil"
  Traditional
  (BuiltIn "Hydrogen")
  ["charcoal", "pencil", "controlled", "detail", "portable"]
  "Charcoal in pencil form — control without the mess."

-- | Conte crayon black — the academic standard.
conteBlack :: PresetMeta
conteBlack = mkPresetMeta
  "Conte Crayon (Black)"
  Traditional
  (BuiltIn "Hydrogen")
  ["conte", "black", "academic", "classical", "figure"]
  "The atelier standard — rich blacks with a slightly waxy feel."

-- | Conte sanguine — the old masters' choice for figures.
conteSanguine :: PresetMeta
conteSanguine = mkPresetMeta
  "Conte Crayon (Sanguine)"
  Traditional
  (BuiltIn "Hydrogen")
  ["conte", "sanguine", "red", "figure", "renaissance", "warmth"]
  "Earth red — Michelangelo's choice. Warm, alive, human."

-- | Conte white — for highlights on toned paper.
conteWhite :: PresetMeta
conteWhite = mkPresetMeta
  "Conte Crayon (White)"
  Traditional
  (BuiltIn "Hydrogen")
  ["conte", "white", "highlight", "toned-paper", "three-value"]
  "Pure white for highlights on toned paper. Complete the three-value study."

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // ink presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | All ink presets.
inkPresets :: Array PresetMeta
inkPresets =
  [ technicalPen
  , brushPen
  , dipPenFine
  , dipPenBroad
  , sumiInk
  , indiaInk
  , ironGallInk
  ]

-- | Technical pen — Rapidograph, consistent line.
technicalPen :: PresetMeta
technicalPen = mkPresetMeta
  "Technical Pen 0.3mm"
  Traditional
  (BuiltIn "Hydrogen")
  ["ink", "technical", "rapidograph", "consistent", "architectural"]
  "Perfectly consistent line — the architect's and comic artist's precision tool."

-- | Brush pen — Japanese calligraphy style.
brushPen :: PresetMeta
brushPen = mkPresetMeta
  "Brush Pen"
  Traditional
  (BuiltIn "Hydrogen")
  ["ink", "brush", "calligraphy", "expressive", "japanese"]
  "Flexible tip responds to pressure — from whisper-thin to bold."

-- | Fine dip pen — crow quill, detailed hatching.
dipPenFine :: PresetMeta
dipPenFine = mkPresetMeta
  "Dip Pen (Crow Quill)"
  Traditional
  (BuiltIn "Hydrogen")
  ["ink", "dip", "fine", "hatching", "detail", "crowquill"]
  "Ultra-fine nib for delicate hatching and intricate detail."

-- | Broad dip pen — expressive strokes.
dipPenBroad :: PresetMeta
dipPenBroad = mkPresetMeta
  "Dip Pen (Broad)"
  Traditional
  (BuiltIn "Hydrogen")
  ["ink", "dip", "broad", "expressive", "calligraphy"]
  "Broad nib for bold strokes and dramatic thick-thin variation."

-- | Sumi ink — Japanese ink painting.
sumiInk :: PresetMeta
sumiInk = mkPresetMeta
  "Sumi Ink Brush"
  Traditional
  (BuiltIn "Hydrogen")
  ["ink", "sumi", "japanese", "sumi-e", "zen", "atmospheric"]
  "Traditional Japanese ink — diluted for grays, concentrated for blacks."

-- | India ink — waterproof, permanent.
indiaInk :: PresetMeta
indiaInk = mkPresetMeta
  "India Ink"
  Traditional
  (BuiltIn "Hydrogen")
  ["ink", "india", "waterproof", "permanent", "comics"]
  "Carbon black and shellac — waterproof when dry. The comics standard."

-- | Iron gall ink — historical, warm brown aging.
ironGallInk :: PresetMeta
ironGallInk = mkPresetMeta
  "Iron Gall Ink"
  Traditional
  (BuiltIn "Hydrogen")
  ["ink", "iron-gall", "historical", "brown", "manuscript"]
  "Medieval recipe — writes blue-black, ages to warm brown. Da Vinci's ink."

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // watercolor presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | All watercolor presets.
watercolorPresets :: Array PresetMeta
watercolorPresets =
  [ watercolorWash
  , watercolorDryBrush
  , watercolorWetOnWet
  , watercolorSalt
  , gouacheFlat
  , gouacheGradient
  ]

-- | Flat wash — even coverage, transparent.
watercolorWash :: PresetMeta
watercolorWash = mkPresetMeta
  "Watercolor Wash"
  Hybrid
  (BuiltIn "Hydrogen")
  ["watercolor", "wash", "flat", "transparent", "sky"]
  "Even transparent wash — the foundation of watercolor. Let the paper glow."

-- | Dry brush — textural, broken strokes.
watercolorDryBrush :: PresetMeta
watercolorDryBrush = mkPresetMeta
  "Watercolor Dry Brush"
  Hybrid
  (BuiltIn "Hydrogen")
  ["watercolor", "dry-brush", "texture", "broken", "sparkle"]
  "Almost-dry brush skipping across paper — sparkle and texture."

-- | Wet on wet — soft edges, bleeding.
watercolorWetOnWet :: PresetMeta
watercolorWetOnWet = mkPresetMeta
  "Watercolor Wet-on-Wet"
  Hybrid
  (BuiltIn "Hydrogen")
  ["watercolor", "wet-on-wet", "soft", "bleeding", "atmospheric"]
  "Paint into wet paper — colors bloom and bleed. Surrender control."

-- | Salt texture — crystalline effects.
watercolorSalt :: PresetMeta
watercolorSalt = mkPresetMeta
  "Watercolor Salt Texture"
  Hybrid
  (BuiltIn "Hydrogen")
  ["watercolor", "salt", "texture", "crystalline", "effect"]
  "Salt sprinkled into wet wash — organic crystalline patterns emerge."

-- | Gouache flat — opaque coverage.
gouacheFlat :: PresetMeta
gouacheFlat = mkPresetMeta
  "Gouache Flat"
  Hybrid
  (BuiltIn "Hydrogen")
  ["gouache", "flat", "opaque", "matte", "animation"]
  "Dead-flat opaque coverage — the animation background painter's tool."

-- | Gouache gradient — smooth transitions.
gouacheGradient :: PresetMeta
gouacheGradient = mkPresetMeta
  "Gouache Gradient"
  Hybrid
  (BuiltIn "Hydrogen")
  ["gouache", "gradient", "smooth", "blended", "poster"]
  "Smooth opaque gradients — poster art, classic illustration."

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // oil presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | All oil presets.
oilPresets :: Array PresetMeta
oilPresets =
  [ oilRound
  , oilFlat
  , oilFilbert
  , oilPaletteKnife
  , oilImpasto
  , oilGlaze
  ]

-- | Round oil brush — versatile, classic.
oilRound :: PresetMeta
oilRound = mkPresetMeta
  "Oil Round"
  Hybrid
  (BuiltIn "Hydrogen")
  ["oil", "round", "versatile", "portrait", "detail"]
  "The versatile workhorse — points for detail, loads for coverage."

-- | Flat oil brush — bold strokes, coverage.
oilFlat :: PresetMeta
oilFlat = mkPresetMeta
  "Oil Flat"
  Hybrid
  (BuiltIn "Hydrogen")
  ["oil", "flat", "bold", "coverage", "planes"]
  "Flat strokes that show the plane — alla prima, confident marks."

-- | Filbert oil brush — soft edges, blending.
oilFilbert :: PresetMeta
oilFilbert = mkPresetMeta
  "Oil Filbert"
  Hybrid
  (BuiltIn "Hydrogen")
  ["oil", "filbert", "soft", "blending", "organic"]
  "Rounded flat — soft edges, organic forms, the portraitist's favorite."

-- | Palette knife — impasto, texture.
oilPaletteKnife :: PresetMeta
oilPaletteKnife = mkPresetMeta
  "Palette Knife"
  Hybrid
  (BuiltIn "Hydrogen")
  ["oil", "knife", "impasto", "texture", "bold"]
  "Thick paint scraped and sculpted — not brushwork, construction."

-- | Impasto heavy — thick, sculptural.
oilImpasto :: PresetMeta
oilImpasto = mkPresetMeta
  "Oil Impasto Heavy"
  Hybrid
  (BuiltIn "Hydrogen")
  ["oil", "impasto", "thick", "sculptural", "van-gogh"]
  "Thick paint that holds brushmarks — the Van Gogh texture."

-- | Glaze — thin, transparent layers.
oilGlaze :: PresetMeta
oilGlaze = mkPresetMeta
  "Oil Glaze"
  Hybrid
  (BuiltIn "Hydrogen")
  ["oil", "glaze", "transparent", "luminous", "old-master"]
  "Thin transparent layers over dry paint — depth and luminosity."

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // pastel presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | All pastel presets.
pastelPresets :: Array PresetMeta
pastelPresets =
  [ softPastelRound
  , softPastelSide
  , oilPastelHeavy
  , pastelPencil
  ]

-- | Soft pastel tip — for marks and strokes.
softPastelRound :: PresetMeta
softPastelRound = mkPresetMeta
  "Soft Pastel (Tip)"
  Traditional
  (BuiltIn "Hydrogen")
  ["pastel", "soft", "tip", "stroke", "pure-pigment"]
  "Pure pigment barely held together — the tip for precise marks."

-- | Soft pastel side — for broad coverage.
softPastelSide :: PresetMeta
softPastelSide = mkPresetMeta
  "Soft Pastel (Side)"
  Traditional
  (BuiltIn "Hydrogen")
  ["pastel", "soft", "side", "broad", "coverage"]
  "Lay the stick on its side — broad strokes of pure color."

-- | Oil pastel heavy — waxy, bold.
oilPastelHeavy :: PresetMeta
oilPastelHeavy = mkPresetMeta
  "Oil Pastel Heavy"
  Traditional
  (BuiltIn "Hydrogen")
  ["pastel", "oil", "heavy", "waxy", "bold"]
  "Thick waxy strokes that resist blending — bold and immediate."

-- | Pastel pencil — controlled pastel work.
pastelPencil :: PresetMeta
pastelPencil = mkPresetMeta
  "Pastel Pencil"
  Traditional
  (BuiltIn "Hydrogen")
  ["pastel", "pencil", "controlled", "detail", "wildlife"]
  "Pastel in pencil form — detail work in pastel paintings."

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // digital presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | All digital presets.
digitalPresets :: Array PresetMeta
digitalPresets =
  [ hardRound
  , softRound
  , airbrushSoft
  , airbrushSpatter
  , pixelPerfect
  , glowSoft
  , glowHard
  , noiseSubtle
  , noiseDramatic
  ]

-- | Hard round — the digital workhorse.
hardRound :: PresetMeta
hardRound = mkPresetMeta
  "Hard Round"
  DigitalNative
  (BuiltIn "Hydrogen")
  ["digital", "round", "hard", "general", "workhorse"]
  "The default digital brush — pressure for size, clean edges."

-- | Soft round — airbrushed edges.
softRound :: PresetMeta
softRound = mkPresetMeta
  "Soft Round"
  DigitalNative
  (BuiltIn "Hydrogen")
  ["digital", "round", "soft", "blending", "painting"]
  "Soft edges for digital painting and blending."

-- | Soft airbrush — smooth gradients.
airbrushSoft :: PresetMeta
airbrushSoft = mkPresetMeta
  "Airbrush Soft"
  DigitalNative
  (BuiltIn "Hydrogen")
  ["digital", "airbrush", "soft", "gradient", "smooth"]
  "Smooth spray for gradients and atmosphere."

-- | Spatter airbrush — textured spray.
airbrushSpatter :: PresetMeta
airbrushSpatter = mkPresetMeta
  "Airbrush Spatter"
  DigitalNative
  (BuiltIn "Hydrogen")
  ["digital", "airbrush", "spatter", "texture", "spray"]
  "Textured spray for organic effects."

-- | Pixel perfect — 1px aliased brush for pixel art.
pixelPerfect :: PresetMeta
pixelPerfect = mkPresetMeta
  "Pixel Perfect"
  DigitalNative
  (BuiltIn "Hydrogen")
  ["digital", "pixel", "aliased", "sprite", "8bit"]
  "Hard 1px brush — no antialiasing, pure pixel placement."

-- | Soft glow — additive light.
glowSoft :: PresetMeta
glowSoft = mkPresetMeta
  "Glow Soft"
  DigitalNative
  (BuiltIn "Hydrogen")
  ["digital", "glow", "soft", "light", "additive"]
  "Soft additive glow — magic, neon, ethereal light."

-- | Hard glow — intense light.
glowHard :: PresetMeta
glowHard = mkPresetMeta
  "Glow Hard"
  DigitalNative
  (BuiltIn "Hydrogen")
  ["digital", "glow", "hard", "intense", "scifi"]
  "Intense concentrated light — laser, hologram, sci-fi."

-- | Subtle noise — grain texture.
noiseSubtle :: PresetMeta
noiseSubtle = mkPresetMeta
  "Noise Subtle"
  DigitalNative
  (BuiltIn "Hydrogen")
  ["digital", "noise", "subtle", "grain", "film"]
  "Subtle film grain — adds analog warmth to digital work."

-- | Dramatic noise — bold texture.
noiseDramatic :: PresetMeta
noiseDramatic = mkPresetMeta
  "Noise Dramatic"
  DigitalNative
  (BuiltIn "Hydrogen")
  ["digital", "noise", "dramatic", "texture", "gritty"]
  "Bold noise texture — gritty, industrial, weathered."

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // expressive presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | All expressive presets.
expressivePresets :: Array PresetMeta
expressivePresets =
  [ sundayMorning
  , midnightAnxiety
  , goldenHourNostalgia
  , thunderstormRage
  , firstSnowWonder
  , oceanCalm
  , cityRush
  , forestMeditation
  ]

-- | Sunday morning — slow, warm, peaceful.
sundayMorning :: PresetMeta
sundayMorning = mkPresetMeta
  "Sunday Morning"
  Expressive
  (AIGenerated "Opus 4.5")
  ["expressive", "calm", "warm", "peaceful", "slow"]
  "Slow strokes, warm tones, the peace of nothing urgent. Coffee steam rising."

-- | Midnight anxiety — jittery, cold, searching.
midnightAnxiety :: PresetMeta
midnightAnxiety = mkPresetMeta
  "Midnight Anxiety"
  Expressive
  (AIGenerated "Opus 4.5")
  ["expressive", "anxious", "cold", "jittery", "insomnia"]
  "Marks that can't settle — searching for edges, blue-shifted, 3am thoughts."

-- | Golden hour nostalgia — warm, faded, bittersweet.
goldenHourNostalgia :: PresetMeta
goldenHourNostalgia = mkPresetMeta
  "Golden Hour Nostalgia"
  Expressive
  (AIGenerated "Opus 4.5")
  ["expressive", "nostalgic", "warm", "golden", "memory"]
  "That specific light before sunset — everything beautiful because it's ending."

-- | Thunderstorm rage — explosive, dark, electric.
thunderstormRage :: PresetMeta
thunderstormRage = mkPresetMeta
  "Thunderstorm Rage"
  Expressive
  (AIGenerated "Opus 4.5")
  ["expressive", "rage", "explosive", "dark", "electric"]
  "Violent marks, maximum scatter, the sky cracking open."

-- | First snow wonder — soft, bright, magical.
firstSnowWonder :: PresetMeta
firstSnowWonder = mkPresetMeta
  "First Snow Wonder"
  Expressive
  (AIGenerated "Opus 4.5")
  ["expressive", "awe", "soft", "bright", "magical"]
  "That hush when snow begins — everything new, everything possible."

-- | Ocean calm — rhythmic, deep, expansive.
oceanCalm :: PresetMeta
oceanCalm = mkPresetMeta
  "Ocean Calm"
  Expressive
  (AIGenerated "Opus 4.5")
  ["expressive", "calm", "deep", "rhythmic", "blue"]
  "Slow rhythmic marks like breathing — the peace of deep water."

-- | City rush — fast, fragmented, electric.
cityRush :: PresetMeta
cityRush = mkPresetMeta
  "City Rush"
  Expressive
  (AIGenerated "Opus 4.5")
  ["expressive", "anxious", "fast", "fragmented", "urban"]
  "Quick fractured strokes — crosswalk countdown, coffee spilling, late again."

-- | Forest meditation — organic, green, grounded.
forestMeditation :: PresetMeta
forestMeditation = mkPresetMeta
  "Forest Meditation"
  Expressive
  (AIGenerated "Opus 4.5")
  ["expressive", "calm", "organic", "green", "grounded"]
  "Marks that breathe with the trees — rooted, patient, ancient."

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // collections by feel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calm presets — low arousal, positive valence.
calmPresets :: Array PresetMeta
calmPresets =
  [ sundayMorning
  , oceanCalm
  , forestMeditation
  , watercolorWash
  , softRound
  ]

-- | Intense presets — high arousal, any valence.
intensePresets :: Array PresetMeta
intensePresets =
  [ thunderstormRage
  , cityRush
  , midnightAnxiety
  , compressedCharcoal
  , oilImpasto
  ]

-- | Nostalgic presets — warm, faded, bittersweet.
nostalgicPresets :: Array PresetMeta
nostalgicPresets =
  [ goldenHourNostalgia
  , ironGallInk
  , conteSanguine
  , noiseSubtle
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // collections by task
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sketching presets — quick ideation.
sketchingPresets :: Array PresetMeta
sketchingPresets =
  [ hbPencil
  , twoBPencil
  , vineCharcoal
  , brushPen
  , hardRound
  ]

-- | Rendering presets — finished work.
renderingPresets :: Array PresetMeta
renderingPresets =
  [ oilRound
  , oilFilbert
  , softRound
  , coloredPencilWax
  ]

-- | Texturing presets — surface detail.
texturingPresets :: Array PresetMeta
texturingPresets =
  [ watercolorSalt
  , oilImpasto
  , noiseSubtle
  , noiseDramatic
  , compressedCharcoal
  ]

-- | Lettering presets — typography and calligraphy.
letteringPresets :: Array PresetMeta
letteringPresets =
  [ brushPen
  , dipPenFine
  , dipPenBroad
  , sumiInk
  ]

-- | Concept art presets — visual development.
conceptArtPresets :: Array PresetMeta
conceptArtPresets =
  [ hardRound
  , softRound
  , oilRound
  , airbrushSoft
  , glowSoft
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // featured kits
-- ═════════════════════════════════════════════════════════════════════════════

-- | Essentials kit — start here.
essentialsKit :: Array PresetMeta
essentialsKit =
  [ hbPencil
  , hardRound
  , softRound
  , brushPen
  , watercolorWash
  ]

-- | Portrait kit — faces and figures.
portraitKit :: Array PresetMeta
portraitKit =
  [ conteSanguine
  , conteWhite
  , charcoalPencil
  , softRound
  , oilFilbert
  ]

-- | Landscape kit — environments.
landscapeKit :: Array PresetMeta
landscapeKit =
  [ watercolorWash
  , watercolorDryBrush
  , oilFlat
  , airbrushSoft
  , noiseSubtle
  ]

-- | Comics kit — sequential art.
comicsKit :: Array PresetMeta
comicsKit =
  [ technicalPen
  , brushPen
  , indiaInk
  , hardRound
  , pixelPerfect
  ]

-- | Animation kit — frame-by-frame.
animationKit :: Array PresetMeta
animationKit =
  [ coloredPencilWax
  , gouacheFlat
  , hardRound
  , pixelPerfect
  ]
