-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // physical // mechanical // hardness
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mohs hardness scale — mineral scratch resistance.
-- |
-- | ## The Mohs Scale
-- |
-- | Developed by Friedrich Mohs in 1812, this scale ranks minerals by their
-- | ability to scratch each other. A harder mineral can scratch a softer one.
-- |
-- | ## Scale Values
-- |
-- | 1 - Talc (softest)
-- | 2 - Gypsum
-- | 3 - Calcite
-- | 4 - Fluorite
-- | 5 - Apatite
-- | 6 - Orthoclase feldspar
-- | 7 - Quartz
-- | 8 - Topaz
-- | 9 - Corundum (sapphire, ruby)
-- | 10 - Diamond (hardest natural material)
-- |
-- | ## Extended Scale
-- |
-- | Some modern references extend to materials harder than diamond:
-- | - Wurtzite boron nitride: ~10.5
-- | - Lonsdaleite: ~10.6
-- | - Aggregated diamond nanorods: ~11
-- |
-- | We support [1.0, 15.0] to accommodate synthetic super-hard materials.
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, hardness determines:
-- | - Haptic feedback resistance during simulated touch
-- | - Wear/scratch simulation in physics engines
-- | - Material selection for simulated manufacturing
-- | - Sound generation characteristics (harder = brighter timbre)
-- |
-- | ## Data Sources
-- |
-- | Standard Mohs values from GIA, CRC Handbook, and peer-reviewed mineralogy.

module Hydrogen.Schema.Physical.Mechanical.Hardness
  ( -- * Core Type
    MohsHardness
  , mohs
  , mohsUnsafe
  , unwrap
  , bounds
  
  -- * Reference Minerals (Standard Mohs Scale)
  , talc
  , gypsum
  , calcite
  , fluorite
  , apatite
  , orthoclase
  , quartz
  , topaz
  , corundum
  , diamond
  
  -- * Gemstones
  , pearl
  , amber
  , opal
  , turquoise
  , lapis
  , moonstone
  , peridot
  , garnet
  , emerald
  , aquamarine
  , tourmaline
  , tanzanite
  , spinel
  , alexandrite
  , sapphire
  , ruby
  , moissanite
  
  -- * Metals (approximate)
  , gold
  , silver
  , copper
  , platinum
  , iron
  , steel
  , titanium
  , tungsten
  
  -- * Common Materials
  , fingernail
  , pennyCopper
  , glassPlate
  , steelFile
  , streak
  
  -- * Synthetic Super-Hard Materials
  , cubicBoronNitride
  , wurtziteBoronNitride
  , lonsdaleite
  , aggregatedDiamondNanorods
  
  -- * Operations
  , canScratch
  , scratchResistance
  , lerp
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, abs, pow) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // core // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mohs hardness value [1.0, 15.0].
-- |
-- | Standard Mohs scale is 1-10, extended to 15 for synthetic super-hard
-- | materials that exceed diamond's hardness.
-- |
-- | ## Invariant
-- |
-- | Value is ALWAYS in [1.0, 15.0]. Values below 1 are clamped (nothing is
-- | softer than talc on Mohs scale). Values above 15 are clamped (beyond
-- | any known material).
newtype MohsHardness = MohsHardness Number

derive instance eqMohsHardness :: Eq MohsHardness
derive instance ordMohsHardness :: Ord MohsHardness

instance showMohsHardness :: Show MohsHardness where
  show (MohsHardness n) = "Mohs(" <> show n <> ")"

-- | Create MohsHardness with validation.
mohs :: Number -> Maybe MohsHardness
mohs n
  | n >= 1.0 && n <= 15.0 = Just (MohsHardness n)
  | otherwise = Nothing

-- | Create MohsHardness with clamping.
mohsUnsafe :: Number -> MohsHardness
mohsUnsafe n = MohsHardness (Bounded.clampNumber 1.0 15.0 n)

-- | Extract the underlying Number.
unwrap :: MohsHardness -> Number
unwrap (MohsHardness n) = n

-- | Bounds documentation for Mohs hardness.
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 1.0 15.0 Bounded.Clamps 
  "mohs" 
  "Mohs hardness scale (1=talc, 10=diamond, 15=synthetic max)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // standard mohs minerals
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mohs 1 — Talc (softest mineral, feels greasy)
talc :: MohsHardness
talc = MohsHardness 1.0

-- | Mohs 2 — Gypsum (scratched by fingernail)
gypsum :: MohsHardness
gypsum = MohsHardness 2.0

-- | Mohs 3 — Calcite (scratched by copper penny)
calcite :: MohsHardness
calcite = MohsHardness 3.0

-- | Mohs 4 — Fluorite (scratched by steel knife)
fluorite :: MohsHardness
fluorite = MohsHardness 4.0

-- | Mohs 5 — Apatite (scratched by steel knife with difficulty)
apatite :: MohsHardness
apatite = MohsHardness 5.0

-- | Mohs 6 — Orthoclase feldspar (scratches glass)
orthoclase :: MohsHardness
orthoclase = MohsHardness 6.0

-- | Mohs 7 — Quartz (scratches steel, common sand mineral)
quartz :: MohsHardness
quartz = MohsHardness 7.0

-- | Mohs 8 — Topaz (scratches quartz)
topaz :: MohsHardness
topaz = MohsHardness 8.0

-- | Mohs 9 — Corundum (sapphire, ruby — second hardest natural)
corundum :: MohsHardness
corundum = MohsHardness 9.0

-- | Mohs 10 — Diamond (hardest natural material)
diamond :: MohsHardness
diamond = MohsHardness 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // gemstones
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pearl — organic, soft for a "gem"
pearl :: MohsHardness
pearl = MohsHardness 2.5

-- | Amber — fossilized tree resin
amber :: MohsHardness
amber = MohsHardness 2.5

-- | Opal — hydrated silica, relatively soft
opal :: MohsHardness
opal = MohsHardness 6.0

-- | Turquoise — copper aluminum phosphate
turquoise :: MohsHardness
turquoise = MohsHardness 6.0

-- | Lapis lazuli — lazurite rock
lapis :: MohsHardness
lapis = MohsHardness 5.5

-- | Moonstone — orthoclase feldspar variety
moonstone :: MohsHardness
moonstone = MohsHardness 6.0

-- | Peridot — olivine gem variety
peridot :: MohsHardness
peridot = MohsHardness 6.5

-- | Garnet — varies by type, average value
garnet :: MohsHardness
garnet = MohsHardness 7.0

-- | Emerald — beryl variety (same mineral as aquamarine)
emerald :: MohsHardness
emerald = MohsHardness 7.5

-- | Aquamarine — beryl variety
aquamarine :: MohsHardness
aquamarine = MohsHardness 7.5

-- | Tourmaline — boron silicate
tourmaline :: MohsHardness
tourmaline = MohsHardness 7.5

-- | Tanzanite — zoisite variety
tanzanite :: MohsHardness
tanzanite = MohsHardness 6.5

-- | Spinel — magnesium aluminum oxide
spinel :: MohsHardness
spinel = MohsHardness 8.0

-- | Alexandrite — chrysoberyl variety (color-changing)
alexandrite :: MohsHardness
alexandrite = MohsHardness 8.5

-- | Sapphire — corundum (non-red)
sapphire :: MohsHardness
sapphire = MohsHardness 9.0

-- | Ruby — corundum (red)
ruby :: MohsHardness
ruby = MohsHardness 9.0

-- | Moissanite — silicon carbide (natural and synthetic)
moissanite :: MohsHardness
moissanite = MohsHardness 9.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // metals
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gold — pure 24K, very soft metal
gold :: MohsHardness
gold = MohsHardness 2.5

-- | Silver — pure, soft metal
silver :: MohsHardness
silver = MohsHardness 2.5

-- | Copper — pure, relatively soft
copper :: MohsHardness
copper = MohsHardness 3.0

-- | Platinum — harder precious metal
platinum :: MohsHardness
platinum = MohsHardness 4.5

-- | Iron — pure, relatively soft
iron :: MohsHardness
iron = MohsHardness 4.0

-- | Steel — iron alloy, hardened
steel :: MohsHardness
steel = MohsHardness 6.5

-- | Titanium — strong aerospace metal
titanium :: MohsHardness
titanium = MohsHardness 6.0

-- | Tungsten — very hard refractory metal
tungsten :: MohsHardness
tungsten = MohsHardness 7.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // common materials
-- ═════════════════════════════════════════════════════════════════════════════

-- | Human fingernail — ~2.5, scratches gypsum
fingernail :: MohsHardness
fingernail = MohsHardness 2.5

-- | Copper penny — ~3.5, traditional hardness test tool
pennyCopper :: MohsHardness
pennyCopper = MohsHardness 3.5

-- | Glass plate — ~5.5, common reference
glassPlate :: MohsHardness
glassPlate = MohsHardness 5.5

-- | Steel file — ~6.5, traditional hardness test tool
steelFile :: MohsHardness
steelFile = MohsHardness 6.5

-- | Streak plate (unglazed porcelain) — ~7.0, for mineral identification
streak :: MohsHardness
streak = MohsHardness 7.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // synthetic super-hard materials
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cubic boron nitride (c-BN) — synthetic, second to diamond industrially
cubicBoronNitride :: MohsHardness
cubicBoronNitride = MohsHardness 9.5

-- | Wurtzite boron nitride (w-BN) — theoretically harder than diamond
wurtziteBoronNitride :: MohsHardness
wurtziteBoronNitride = MohsHardness 10.5

-- | Lonsdaleite — hexagonal diamond, rare natural/synthetic
lonsdaleite :: MohsHardness
lonsdaleite = MohsHardness 10.6

-- | Aggregated diamond nanorods (ADNR) — hardest known material
aggregatedDiamondNanorods :: MohsHardness
aggregatedDiamondNanorods = MohsHardness 11.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if material A can scratch material B.
-- |
-- | A harder material can scratch a softer one. Equal hardness may or may not
-- | scratch depending on crystal orientation and other factors.
canScratch :: MohsHardness -> MohsHardness -> Boolean
canScratch (MohsHardness a) (MohsHardness b) = a > b

-- | Scratch resistance category based on Mohs hardness.
-- |
-- | - Soft (1-3): Easily scratched by common objects
-- | - Medium (3-6): Scratched by tools and hard objects
-- | - Hard (6-8): Resistant to most scratches
-- | - Very Hard (8+): Gem-quality durability
scratchResistance :: MohsHardness -> String
scratchResistance (MohsHardness n)
  | n <= 3.0 = "soft"
  | n <= 6.0 = "medium"
  | n <= 8.0 = "hard"
  | otherwise = "very-hard"

-- | Linear interpolation between two hardness values.
lerp :: Number -> MohsHardness -> MohsHardness -> MohsHardness
lerp t (MohsHardness a) (MohsHardness b) =
  mohsUnsafe (a + t * (b - a))
