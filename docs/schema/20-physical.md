━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // 20 // physical
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Physical Pillar

Material science primitives: optical properties (IOR, dispersion), mechanical
properties (density, hardness), thermal conductivity, fluid dynamics (viscosity,
surface tension, flow behavior), and the complete periodic table of elements.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Physical/`
- **Files**: 33 modules
- **Lines**: ~6,805 lines of PureScript
- **Key features**: Complete IOR database (120+ materials), density database
  (100+ materials), Mohs hardness, thermal conductivity, fluid viscosity,
  surface tension, non-Newtonian flow models, 118 periodic table elements

## Purpose

Physical provides bounded, deterministic primitives for:
- **Optical simulation**: Index of refraction, dispersion, Fresnel calculations
- **Haptic feedback**: Density, hardness, thermal conductivity (why metal feels
  cold, why wood feels warm)
- **Fluid simulation**: Viscosity, surface tension, Newtonian/non-Newtonian flow
- **Material science**: Complete periodic table with groups, periods, blocks
- **PBR rendering**: Physically-accurate material properties for real-time graphics

## Why This Matters

At billion-agent scale, physically accurate properties are non-negotiable:
- Same IOR value = same refraction angle (deterministic ray tracing)
- Same density = same weight perception (haptic feedback)
- Same thermal conductivity = same touch temperature (BMI systems)
- Same viscosity = same pour behavior (fluid simulation)

When an AI agent creates "diamond glass" or simulates "underwater viewing",
they compose from these verified atoms. No guessing. No approximations.

────────────────────────────────────────────────────────────────────────────────
                                                                // architecture
────────────────────────────────────────────────────────────────────────────────

## Module Structure

```
Physical/
├── Optical/
│   ├── IOR.purs                    -- Leader module
│   ├── IOR/
│   │   ├── Core.purs               -- Type, operations, predicates
│   │   ├── Gases.purs              -- Vacuum, air, noble gases
│   │   ├── Liquids.purs            -- Water, alcohols, solvents
│   │   ├── Glass.purs              -- Common and optical glass
│   │   ├── Plastics.purs           -- Polymers
│   │   ├── Gemstones.purs          -- Precious, semi-precious, quartz, beryl
│   │   ├── Materials.purs          -- Crystals, metals, semiconductors, bio
│   │   └── Database.purs           -- Complete material lookup
│   └── Dispersion.purs             -- Abbe number, fire value
├── Mechanical/
│   ├── Density.purs                -- Leader module
│   ├── Density/
│   │   ├── Types.purs              -- Core type
│   │   ├── Operations.purs         -- Comparison, interpolation
│   │   └── Materials/
│   │       ├── Gases.purs          -- Gas densities at STP
│   │       ├── Liquids.purs        -- Liquid densities
│   │       ├── Woods.purs          -- Wood densities
│   │       ├── Polymers.purs       -- Plastic densities
│   │       ├── Building.purs       -- Construction materials
│   │       ├── Metals.purs         -- Metal densities
│   │       ├── Gemstones.purs      -- Gemstone densities
│   │       └── Other.purs          -- Ice, sand, biological
│   └── Hardness.purs               -- Mohs scale
├── Thermal/
│   └── Conductivity.purs           -- Heat transfer properties
├── Fluid/
│   ├── Viscosity.purs              -- Dynamic viscosity
│   ├── SurfaceTension.purs         -- Surface tension
│   └── FlowBehavior.purs           -- Newtonian/non-Newtonian models
└── Element/
    ├── Element.purs                -- 118 elements ADT
    ├── Symbol.purs                 -- Chemical symbols
    ├── Category.purs               -- Metal/nonmetal classification
    ├── Group.purs                  -- Periodic table columns
    ├── Period.purs                 -- Periodic table rows
    └── Block.purs                  -- Orbital blocks (s, p, d, f)
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // optical // ior
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Index of Refraction (IOR)

The IOR describes how much light slows down and bends when entering a material.
Formula: **n = c / v** (speed of light in vacuum / speed in material).

### Core Type

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| IOR | Number | 1.0 | 4.0 | clamps | Ratio of light speed in vacuum to material |

**Bounds rationale:**
- **1.0**: Vacuum (by definition, the reference point)
- **4.0**: Germanium at infrared wavelengths (practical maximum)
- **Common range**: 1.0–2.5 for visible light applications

### Operations

```purescript
fresnel0 :: IOR -> Number
-- F0 = ((n1 - n2) / (n1 + n2))²
-- For air-to-material: F0 = ((1 - n) / (1 + n))²
-- Returns reflectance at normal incidence

criticalAngle :: IOR -> IOR -> Maybe Number
-- Returns angle (radians) where total internal reflection begins
-- Nothing if n1 <= n2 (no TIR possible)

blend :: Number -> IOR -> IOR -> IOR
-- Linear interpolation between two IOR values

totalInternalReflection :: IOR -> IOR -> Boolean
-- True if light going from higher to lower IOR
```

### Material Categories

```purescript
data MaterialCategory
  = Gas             -- n ~ 1.0 (1.0–1.001)
  | Liquid          -- n ~ 1.3–1.65
  | Glass           -- n ~ 1.45–1.9
  | Plastic         -- n ~ 1.4–1.6
  | GemPrecious     -- Diamond, ruby, sapphire
  | GemSemiPrecious -- Topaz, tourmaline, garnet
  | GemQuartz       -- Amethyst, citrine, agate
  | GemBeryl        -- Emerald, aquamarine, morganite
  | GemRare         -- Benitoite, painite, musgravite
  | Crystal         -- Halite, fluorite, calcite
  | Metal           -- Real part of complex IOR
  | Semiconductor   -- Silicon, germanium
  | Biological      -- Cornea, lens, skin
```

────────────────────────────────────────────────────────────────────────────────
                                                              // ior // presets
────────────────────────────────────────────────────────────────────────────────

## IOR Presets by Category

### Gases (n ~ 1.0)

| Material | IOR | Notes |
|----------|-----|-------|
| vacuum | 1.0 | Reference point, by definition |
| air | 1.000293 | Standard Temperature and Pressure |
| helium | 1.000036 | Lightest noble gas |
| hydrogen | 1.000132 | Lightest gas |
| oxygen | 1.000271 | |
| nitrogen | 1.000298 | 78% of atmosphere |
| carbonDioxide | 1.00045 | |
| methane | 1.000444 | Natural gas |
| argon | 1.000281 | Noble gas |
| neon | 1.000067 | Noble gas |

### Liquids (n ~ 1.3–1.65)

| Material | IOR | Notes |
|----------|-----|-------|
| water | 1.333 | Reference liquid at 20°C |
| waterIce | 1.31 | Solid form |
| seawater | 1.339 | 3.5% salinity |
| ethanol | 1.361 | Ethyl alcohol |
| methanol | 1.329 | Methyl alcohol |
| acetone | 1.359 | Common solvent |
| glycerol | 1.473 | Very viscous |
| benzene | 1.501 | Aromatic hydrocarbon |
| toluene | 1.497 | Paint thinner |
| carbonDisulfide | 1.628 | Highest common liquid IOR |
| oliveoil | 1.47 | Cooking oil |
| turpentine | 1.472 | Solvent |
| honey | 1.504 | Viscous sugar solution |

### Common Glass (n ~ 1.5–1.9)

| Material | IOR | Notes |
|----------|-----|-------|
| sodaLimeGlass | 1.52 | Window glass |
| borosilicateGlass | 1.474 | Lab glass |
| crownGlass | 1.52 | Low dispersion optical |
| flintGlass | 1.62 | High dispersion optical |
| denseFlintGlass | 1.75 | Very high dispersion |
| leadGlass | 1.65 | Crystal glassware |
| fusedSilica | 1.458 | Fused quartz |
| pyrex | 1.474 | Trade name borosilicate |

### Optical Glass (Schott catalog)

| Material | IOR | Notes |
|----------|-----|-------|
| bk7 | 1.5168 | Most common optical glass |
| sf11 | 1.7847 | Dense flint for dispersion |
| laf2 | 1.744 | Lanthanum flint |
| lasf9 | 1.850 | Lanthanum dense flint |
| nbk7 | 1.5168 | Modern BK7 formulation |
| nsk2 | 1.6074 | Dense crown |

### Plastics & Polymers (n ~ 1.35–1.6)

| Material | IOR | Notes |
|----------|-----|-------|
| acrylic | 1.49 | PMMA / Plexiglass |
| pmma | 1.49 | Polymethyl methacrylate |
| polycarbonate | 1.586 | Lexan, safety glasses |
| polystyrene | 1.59 | Styrofoam base polymer |
| polyethylene | 1.51 | HDPE/LDPE |
| pvc | 1.54 | Polyvinyl chloride |
| nylon | 1.53 | Polyamide |
| teflon | 1.35 | PTFE, lowest plastic IOR |
| epoxy | 1.55 | Resin |
| silicone | 1.43 | Rubber |

### Precious Gemstones (n ~ 1.5–2.5)

| Material | IOR | Notes |
|----------|-----|-------|
| diamond | 2.417 | Highest natural IOR, exceptional fire |
| ruby | 1.77 | Corundum + chromium |
| sapphire | 1.77 | Corundum (non-red) |
| emerald | 1.58 | Beryl + chromium/vanadium |
| aquamarine | 1.577 | Beryl (blue-green) |
| alexandrite | 1.746 | Chrysoberyl, color-change |

### Semi-Precious Gemstones (n ~ 1.4–1.85)

| Material | IOR | Notes |
|----------|-----|-------|
| amethyst | 1.544 | Purple quartz |
| citrine | 1.544 | Yellow quartz |
| topaz | 1.63 | Aluminum silicate |
| tourmaline | 1.64 | Boron silicate |
| garnet | 1.79 | Almandine type |
| peridot | 1.67 | Olivine gem |
| tanzanite | 1.70 | Zoisite (rare) |
| opal | 1.45 | Play of color (diffraction) |
| turquoise | 1.62 | Copper phosphate |
| jade | 1.61 | Nephrite |
| lapis | 1.50 | Lapis lazuli |
| malachite | 1.85 | Copper carbonate |
| obsidian | 1.50 | Volcanic glass |
| moonstone | 1.52 | Feldspar |
| labradorite | 1.56 | Labradorescence |
| amazonite | 1.53 | Feldspar |

### Quartz Family (n ~ 1.54)

| Material | IOR | Notes |
|----------|-----|-------|
| quartz | 1.544 | Clear / rock crystal |
| roseQuartz | 1.544 | Pink variety |
| smokyQuartz | 1.544 | Brown variety |
| tigerEye | 1.544 | Chatoyant |
| agate | 1.544 | Banded chalcedony |
| jasper | 1.54 | Opaque quartz |
| carnelian | 1.544 | Red-orange chalcedony |
| onyx | 1.544 | Black chalcedony |
| chalcedony | 1.544 | Cryptocrystalline quartz |

### Beryl Family (n ~ 1.57–1.60)

| Material | IOR | Notes |
|----------|-----|-------|
| beryl | 1.577 | Colorless |
| morganite | 1.59 | Pink beryl |
| heliodor | 1.577 | Yellow beryl |
| goshenite | 1.577 | Colorless beryl |

### Rare/Collector Gemstones (n ~ 1.7–2.0)

| Material | IOR | Notes |
|----------|-----|-------|
| spinel | 1.72 | Often mistaken for ruby |
| zircon | 1.95 | High dispersion (not CZ) |
| chrysoberyl | 1.746 | Cat's eye effect |
| sphene | 2.0 | Titanite, extreme dispersion |
| demantoid | 1.89 | Green garnet, diamond-like fire |
| tsavorite | 1.74 | Green garnet |
| rhodolite | 1.76 | Purple garnet |
| hessonite | 1.74 | Cinnamon garnet |
| spessartine | 1.80 | Orange garnet |
| benitoite | 1.80 | Rare California gem |
| taaffeite | 1.72 | Extremely rare |
| painite | 1.79 | Was rarest mineral |
| musgravite | 1.72 | Rarer than painite |

### Crystals & Minerals

| Material | IOR | Notes |
|----------|-----|-------|
| halite | 1.544 | Rock salt |
| fluorite | 1.434 | Calcium fluoride (low dispersion) |
| calcite | 1.658 | Birefringent (ordinary ray) |
| gypsum | 1.52 | Hydrated calcium sulfate |
| mica | 1.58 | Muscovite |

### Metals (real part of complex IOR)

| Material | IOR | Notes |
|----------|-----|-------|
| gold | 1.0 | Complex IOR, warm reflection |
| silver | 1.0 | Complex IOR |
| copper | 1.0 | Complex IOR |
| aluminum | 1.44 | Good reflector |
| iron | 2.95 | High real part |
| platinum | 2.33 | Precious metal |
| chromium | 3.18 | Highest real part common metal |
| titanium | 2.16 | Aerospace metal |

### Semiconductors (n ~ 3–4)

| Material | IOR | Notes |
|----------|-----|-------|
| silicon | 3.48 | At 589nm, higher at IR |
| germanium | 4.0 | Physical maximum for common materials |
| galliumArsenide | 3.93 | Compound semiconductor |

### Biological Tissues (n ~ 1.3–1.5)

| Material | IOR | Notes |
|----------|-----|-------|
| cornea | 1.376 | Human eye surface |
| lens | 1.42 | Human eye lens |
| vitreous | 1.336 | Eye interior fluid |
| skin | 1.44 | Epidermis |
| blood | 1.36 | Plasma + cells |
| bone | 1.55 | Cortical |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         // optical // dispersion
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Dispersion (Wavelength-Dependent Refraction)

Dispersion creates rainbows, gemstone "fire", and chromatic aberration.

### Abbe Number (Reciprocal Dispersion)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| AbbeNumber | Number | 15.0 | 100.0 | clamps | Vd = (nd - 1) / (nF - nC) |

**Formula**: Vd = (n_d - 1) / (n_F - n_C)
- n_d = refractive index at 587.6nm (yellow)
- n_F = refractive index at 486.1nm (blue)
- n_C = refractive index at 656.3nm (red)

**Higher Abbe = lower dispersion** (less rainbow effect)

**Categories:**
- High dispersion: Abbe < 30 (flint glass, diamonds)
- Medium dispersion: Abbe 30–55 (crown glass, water)
- Low dispersion: Abbe > 55 (fluorite, fused silica)

### Fire Value (Gemstone Dispersion)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| FireValue | Number | 0.0 | 0.2 | clamps | nB - nR (blue IOR minus red IOR) |

**Higher fire = more spectral flashes in gemstones**

**Categories:**
- Exceptional: > 0.05 (diamond, moissanite, CZ)
- High: 0.03–0.05 (zircon, demantoid)
- Moderate: 0.015–0.03 (sapphire, peridot)
- Low: < 0.015 (quartz, emerald)

### Abbe Number Presets

**Optical Glass — Low Dispersion:**
| Material | Abbe | Notes |
|----------|------|-------|
| fluorite | 95.0 | Lowest dispersion common material |
| fusedSilica | 67.8 | SiO2 |
| bk7 | 64.2 | Standard optical glass |
| pk52a | 81.6 | Extra-low dispersion phosphate crown |
| fk51a | 84.5 | Fluorophosphate, excellent for apochromats |

**Optical Glass — High Dispersion:**
| Material | Abbe | Notes |
|----------|------|-------|
| flintGlass | 36.0 | Lead-containing |
| denseFlint | 25.0 | Very high dispersion |
| sf11 | 25.8 | Schott dense flint |
| sf57 | 18.0 | Extra-dense flint |

### Fire Value Presets

| Material | Fire | Notes |
|----------|------|-------|
| sphaleriteFire | 0.156 | Extremely high but soft |
| moissaniteFire | 0.104 | More fire than diamond! |
| cubicZirconiaFire | 0.060 | Good diamond simulant |
| demantoidFire | 0.057 | Exceptional for colored stone |
| sphene_Fire | 0.051 | Titanite, very high |
| diamondFire | 0.044 | The benchmark |
| zirconFire | 0.039 | Natural zircon |
| sapphireFire | 0.018 | Same as ruby (corundum) |
| rubyFire | 0.018 | |
| topazFire | 0.014 | |
| emeraldFire | 0.014 | |
| quartzFire | 0.013 | |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // mechanical // density
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Density

Mass per unit volume. Critical for:
- Haptic weight perception
- Buoyancy simulation
- Physics engines (gravity, inertia)
- Audio properties (denser = brighter timbre)

### Core Type

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Density | Number | 0.001 | 50000.0 | clamps | kg/m³ |

**Bounds rationale:**
- **0.001**: Below interstellar medium (~0.00008)
- **50000.0**: Above osmium (22590), allows exotic alloys
- **Reference**: Water = 1000 kg/m³

### Operations

```purescript
isLighterThan :: Density -> Density -> Boolean
floatsIn :: Density -> Density -> Boolean  -- Solid floats in liquid?
relativeToWater :: Density -> Number       -- Specific gravity
lerp :: Number -> Density -> Density -> Density
```

### Constructor Variants

```purescript
kgPerM3 :: Number -> Density  -- SI units
gPerCm3 :: Number -> Density  -- Chemistry convention (1 g/cm³ = 1000 kg/m³)
```

────────────────────────────────────────────────────────────────────────────────
                                                         // density // presets
────────────────────────────────────────────────────────────────────────────────

### Gases at STP (kg/m³)

| Material | Density | Notes |
|----------|---------|-------|
| hydrogen | 0.0899 | Lightest gas |
| helium | 0.1785 | Balloon gas |
| methane | 0.717 | Natural gas |
| air | 1.225 | Reference atmosphere |
| nitrogen | 1.251 | 78% of air |
| oxygen | 1.429 | 21% of air |
| argon | 1.784 | Noble gas |
| carbonDioxide | 1.977 | Sinks in air |
| propane | 2.01 | LPG |
| butane | 2.48 | Lighter fluid |

### Liquids (kg/m³)

| Material | Density | Notes |
|----------|---------|-------|
| gasoline | 720.0 | Floats on water |
| ethanol | 789.0 | 78.9% of water |
| methanol | 792.0 | Wood alcohol |
| acetone | 784.0 | Nail polish remover |
| kerosene | 810.0 | Jet fuel base |
| diesel | 850.0 | Fuel oil |
| oliveoil | 920.0 | Floats on water |
| ice | 917.0 | Less dense than water! |
| water | 1000.0 | Reference liquid |
| seawater | 1025.0 | 2.5% denser than fresh |
| milk | 1030.0 | |
| blood | 1060.0 | Human blood |
| glycerol | 1261.0 | Viscous |
| honey | 1420.0 | Sugar solution |
| mercury | 13546.0 | Liquid metal |

### Woods (kg/m³ at 12% moisture)

| Material | Density | Notes |
|----------|---------|-------|
| cork | 120.0 | Bark, very light |
| balsa | 160.0 | Lightest commercial wood |
| bamboo | 350.0 | Grass, varies |
| pine | 510.0 | Common softwood |
| mahogany | 530.0 | Tropical hardwood |
| teak | 630.0 | Water-resistant |
| walnut | 650.0 | Furniture wood |
| maple | 700.0 | Hard, dense |
| oak | 750.0 | Common hardwood |
| ebony | 1120.0 | Nearly sinks |

### Polymers (kg/m³)

| Material | Density | Notes |
|----------|---------|-------|
| styrofoam | 50.0 | Expanded polystyrene |
| polypropylene | 905.0 | Floats on water |
| polyethylene | 950.0 | HDPE/LDPE average |
| rubber | 1100.0 | Natural |
| silicone | 1100.0 | Rubber |
| nylon | 1150.0 | Polyamide |
| acrylic | 1180.0 | PMMA |
| polycarbonate | 1200.0 | Lexan |
| epoxy | 1200.0 | Cured resin |
| pvc | 1400.0 | Rigid PVC |
| teflon | 2200.0 | PTFE, dense fluoropolymer |

### Building Materials (kg/m³)

| Material | Density | Notes |
|----------|---------|-------|
| plaster | 1200.0 | Gypsum-based |
| cement | 1500.0 | Powder |
| brick | 1920.0 | Common red |
| sandstone | 2300.0 | Sedimentary |
| concrete | 2400.0 | Reinforced average |
| asphalt | 2400.0 | Bitumen mix |
| limestone | 2500.0 | Sedimentary |
| glass | 2500.0 | Soda-lime |
| granite | 2700.0 | Igneous rock |
| marble | 2700.0 | Metamorphic |
| slate | 2800.0 | Metamorphic |

### Metals — Light (kg/m³)

| Material | Density | Notes |
|----------|---------|-------|
| lithium | 534.0 | Lightest metal |
| magnesium | 1738.0 | Structural light metal |
| aluminum | 2700.0 | Common light metal |
| titanium | 4507.0 | Aerospace metal |

### Metals — Common (kg/m³)

| Material | Density | Notes |
|----------|---------|-------|
| zinc | 7140.0 | |
| chromium | 7190.0 | |
| tin | 7310.0 | |
| steel | 7850.0 | Carbon steel |
| iron | 7874.0 | Pure |
| stainlessSteel | 8000.0 | 304 grade |
| brass | 8500.0 | Cu-Zn alloy |
| bronze | 8900.0 | Cu-Sn alloy |
| nickel | 8908.0 | |
| copper | 8960.0 | |

### Metals — Precious (kg/m³)

| Material | Density | Notes |
|----------|---------|-------|
| silver | 10490.0 | |
| palladium | 12023.0 | |
| rhodium | 12410.0 | |
| gold | 19320.0 | |
| platinum | 21450.0 | |

### Metals — Heavy (kg/m³)

| Material | Density | Notes |
|----------|---------|-------|
| lead | 11340.0 | Toxic |
| uranium | 19100.0 | Depleted |
| tungsten | 19250.0 | Refractory |
| iridium | 22560.0 | Second densest |
| osmium | 22590.0 | Densest stable element |

### Gemstones (kg/m³)

| Material | Density | Notes |
|----------|---------|-------|
| opal | 2100.0 | Hydrated silica |
| amethyst | 2650.0 | Quartz variety |
| turquoise | 2750.0 | Copper phosphate |
| emerald | 2760.0 | Beryl variety |
| diamond | 3520.0 | Carbon crystal |
| topaz | 3550.0 | Aluminum silicate |
| ruby | 4000.0 | Corundum |
| sapphire | 4000.0 | Corundum |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // mechanical // hardness
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Mohs Hardness Scale

Mineral scratch resistance. A harder material can scratch a softer one.

### Core Type

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| MohsHardness | Number | 1.0 | 15.0 | clamps | Extended scale for synthetics |

**Standard Mohs scale**: 1–10
**Extended scale**: 11+ for synthetic super-hard materials

### Operations

```purescript
canScratch :: MohsHardness -> MohsHardness -> Boolean
-- A can scratch B if A > B

scratchResistance :: MohsHardness -> String
-- "soft" (1-3), "medium" (3-6), "hard" (6-8), "very-hard" (8+)

lerp :: Number -> MohsHardness -> MohsHardness -> MohsHardness
```

### Standard Mohs Scale Minerals

| Mohs | Mineral | Notes |
|------|---------|-------|
| 1 | talc | Softest, feels greasy |
| 2 | gypsum | Scratched by fingernail |
| 3 | calcite | Scratched by copper penny |
| 4 | fluorite | Scratched by steel knife |
| 5 | apatite | Scratched with difficulty |
| 6 | orthoclase | Scratches glass |
| 7 | quartz | Scratches steel, common sand |
| 8 | topaz | Scratches quartz |
| 9 | corundum | Sapphire/ruby, second hardest natural |
| 10 | diamond | Hardest natural material |

### Gemstone Hardness

| Gemstone | Mohs | Notes |
|----------|------|-------|
| pearl | 2.5 | Organic, soft |
| amber | 2.5 | Fossilized resin |
| lapis | 5.5 | Lazurite rock |
| opal | 6.0 | Hydrated silica |
| turquoise | 6.0 | |
| moonstone | 6.0 | Orthoclase feldspar |
| tanzanite | 6.5 | Zoisite |
| peridot | 6.5 | Olivine |
| garnet | 7.0 | Varies by type |
| tourmaline | 7.5 | |
| emerald | 7.5 | Beryl |
| aquamarine | 7.5 | Beryl |
| spinel | 8.0 | |
| alexandrite | 8.5 | Chrysoberyl |
| sapphire | 9.0 | Corundum |
| ruby | 9.0 | Corundum |
| moissanite | 9.5 | Silicon carbide |
| diamond | 10.0 | Carbon |

### Metal Hardness

| Metal | Mohs | Notes |
|-------|------|-------|
| gold | 2.5 | Pure 24K, very soft |
| silver | 2.5 | Pure |
| copper | 3.0 | Pure |
| iron | 4.0 | Pure |
| platinum | 4.5 | |
| titanium | 6.0 | Aerospace |
| steel | 6.5 | Hardened alloy |
| tungsten | 7.5 | Refractory |

### Common Reference Materials

| Material | Mohs | Notes |
|----------|------|-------|
| fingernail | 2.5 | Scratches gypsum |
| pennyCopper | 3.5 | Traditional test tool |
| glassPlate | 5.5 | Window glass |
| steelFile | 6.5 | Traditional test tool |
| streak | 7.0 | Unglazed porcelain |

### Synthetic Super-Hard Materials

| Material | Mohs | Notes |
|----------|------|-------|
| cubicBoronNitride | 9.5 | c-BN, industrial cutting |
| wurtziteBoronNitride | 10.5 | Theoretically harder than diamond |
| lonsdaleite | 10.6 | Hexagonal diamond |
| aggregatedDiamondNanorods | 11.0 | ADNR, hardest known |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // thermal // conductivity
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Thermal Conductivity

Heat transfer through materials. **Why metal feels cold and wood feels warm**
at the same temperature—metal conducts heat away from your hand faster.

### Core Type

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ThermalConductivity | Number | 0.001 | 10000.0 | clamps | W/(m·K) |

**Formula**: Fourier's law: q = -k × ∇T (heat flux = conductivity × temperature gradient)

**Bounds rationale:**
- **0.001**: Below aerogel (~0.015)
- **10000**: Above carbon nanotubes (~6000)
- **Reference**: Copper = 401 W/(m·K)

### Operations

```purescript
conductsHeatWell :: ThermalConductivity -> Boolean  -- > 50 W/(m·K)
isInsulator :: ThermalConductivity -> Boolean       -- < 1 W/(m·K)
thermalCategory :: ThermalConductivity -> String
-- "insulator" (<1), "poor" (1-50), "good" (50-300), "excellent" (>300)
relativeToCopper :: ThermalConductivity -> Number   -- Copper = 1.0
lerp :: Number -> ThermalConductivity -> ThermalConductivity -> ThermalConductivity
```

────────────────────────────────────────────────────────────────────────────────
                                                       // thermal // presets
────────────────────────────────────────────────────────────────────────────────

### Gases at STP (W/(m·K))

| Material | k | Notes |
|----------|---|-------|
| carbonDioxide | 0.017 | |
| argon | 0.018 | Poor conductor, used in windows |
| steam | 0.025 | Water vapor at 100°C |
| air | 0.026 | Reference gas |
| nitrogen | 0.026 | |
| oxygen | 0.027 | |
| methane | 0.034 | |
| helium | 0.152 | Second best gas |
| hydrogen | 0.187 | Best conducting gas |

### Exceptional Insulators (W/(m·K))

| Material | k | Notes |
|----------|---|-------|
| vacuum_ | 0.001 | Near-zero (radiation only) |
| aerogel | 0.015 | Best solid insulator |
| polyurethaneFoam | 0.025 | Building insulation |
| styrofoam | 0.033 | EPS |
| mineralWool | 0.038 | Rock wool |
| fiberglass | 0.040 | |
| corkBoard | 0.043 | |

### Common Insulators (W/(m·K))

| Material | k | Notes |
|----------|---|-------|
| wool | 0.04 | Fabric |
| cotton | 0.04 | Fabric |
| paper | 0.05 | |
| polyester | 0.05 | Fabric |
| cardboard | 0.07 | |
| wood | 0.12 | Softwood average |
| leather | 0.14 | |
| rubber | 0.16 | Natural |
| drywall | 0.16 | Gypsum board |

### Building Materials (W/(m·K))

| Material | k | Notes |
|----------|---|-------|
| plaster | 0.48 | Gypsum |
| brick | 0.72 | |
| asphalt | 0.75 | |
| glass | 1.0 | Window |
| concrete | 1.0 | |
| pyrex | 1.1 | Borosilicate |
| fusedSilica | 1.4 | |
| porcelain | 1.5 | |
| limestone | 1.5 | |
| slate | 2.0 | |
| zirconia | 2.0 | Thermal barrier |
| ice | 2.2 | At 0°C |
| sandstone | 2.3 | |
| granite | 2.5 | |
| marble | 2.5 | |
| quartz | 3.0 | Crystal |
| alumina | 30.0 | Al₂O₃ ceramic |

### Metals — Low Conductivity (W/(m·K))

| Material | k | Notes |
|----------|---|-------|
| bismuth | 8.0 | Lowest metal |
| nickelAlloy | 11.0 | Inconel |
| stainlessSteel | 16.0 | 304 grade |
| titanium | 22.0 | |
| lead | 35.0 | |

### Metals — Medium Conductivity (W/(m·K))

| Material | k | Notes |
|----------|---|-------|
| steel | 50.0 | Carbon steel |
| bronze | 50.0 | Cu-Sn |
| tin | 67.0 | |
| iron | 80.0 | Pure |
| nickel | 91.0 | |
| chromium | 94.0 | |
| brass | 109.0 | Cu-Zn |
| zinc | 116.0 | |

### Metals — High Conductivity (W/(m·K))

| Material | k | Notes |
|----------|---|-------|
| aluminum | 237.0 | Lightweight |
| gold | 318.0 | |
| copper | 401.0 | Standard reference |
| silver | 429.0 | Best metallic conductor |

### Exceptional Conductors (W/(m·K))

| Material | k | Notes |
|----------|---|-------|
| copperTungsten | 200.0 | Composite |
| aluminumNitride | 285.0 | Ceramic with metal-like k |
| graphite | 400.0 | In-plane |
| siliconCarbide | 490.0 | SiC |
| diamond | 2200.0 | Best bulk conductor |
| graphene | 5000.0 | Theoretical |

### Biological Tissues (W/(m·K))

| Material | k | Notes |
|----------|---|-------|
| fat | 0.21 | Adipose, insulating |
| bone | 0.32 | Cortical |
| skin | 0.37 | |
| muscle | 0.49 | |
| blood | 0.52 | |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          // fluid // viscosity
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Dynamic Viscosity

Fluid resistance to flow. Determines how liquids pour, drip, and spread.

### Core Type

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| DynamicViscosity | Number | 0.000001 | 10000000000.0 | clamps | Pa·s |

**Formula**: Newton's law: τ = μ × (du/dy) (shear stress = viscosity × velocity gradient)

**Units:**
- **Pa·s** (Pascal-seconds) = kg/(m·s) — SI unit
- **cP** (centipoise) = 0.001 Pa·s — common unit
- **P** (poise) = 0.1 Pa·s

**Reference**: Water at 20°C = 0.001 Pa·s = 1 cP

### Operations

```purescript
isWatery :: DynamicViscosity -> Boolean   -- < 0.01 Pa·s
isSyrupy :: DynamicViscosity -> Boolean   -- 0.1–100 Pa·s
isViscous :: DynamicViscosity -> Boolean  -- > 100 Pa·s
viscosityCategory :: DynamicViscosity -> String
-- "thin" (<0.01), "light" (0.01-0.1), "medium" (0.1-10),
-- "heavy" (10-1000), "solid-like" (>1000)
relativeToWater :: DynamicViscosity -> Number  -- Water = 1.0
lerp :: Number -> DynamicViscosity -> DynamicViscosity -> DynamicViscosity
```

### Constructor Variants

```purescript
pascalSeconds :: Number -> DynamicViscosity
centipoise :: Number -> DynamicViscosity    -- 1 cP = 0.001 Pa·s
poise :: Number -> DynamicViscosity         -- 1 P = 0.1 Pa·s
```

────────────────────────────────────────────────────────────────────────────────
                                                      // viscosity // presets
────────────────────────────────────────────────────────────────────────────────

### Gases (Pa·s)

| Material | η | Notes |
|----------|---|-------|
| hydrogen | 0.0000088 | Lightest |
| steam | 0.0000125 | 100°C |
| carbonDioxide | 0.0000148 | |
| nitrogen | 0.0000178 | |
| air | 0.0000182 | |
| helium | 0.0000196 | |
| oxygen | 0.0000204 | |

### Water & Aqueous (Pa·s)

| Material | η | Notes |
|----------|---|-------|
| water100C | 0.000282 | Hot water, less viscous |
| methanol | 0.00054 | |
| water | 0.001 | Reference at 20°C |
| ethanol | 0.00109 | |
| seawater | 0.00108 | |
| brine | 0.0015 | Saturated |
| water0C | 0.00179 | Cold water, more viscous |
| isopropanol | 0.00243 | Rubbing alcohol |
| ethyleneGlycol | 0.0161 | Antifreeze |
| propyleneGlycol | 0.042 | |
| glycerol | 1.412 | Very viscous alcohol |

### Light Oils (Pa·s)

| Material | η | Notes |
|----------|---|-------|
| acetone | 0.000306 | Very low viscosity |
| gasoline | 0.0006 | |
| kerosene | 0.00164 | |
| diesel | 0.003 | |
| lightMineralOil | 0.015 | |
| hydraulicOil | 0.032 | |

### Medium Oils (Pa·s)

| Material | η | Notes |
|----------|---|-------|
| vegetableOil | 0.065 | |
| motorOil10W | 0.065 | Thin motor oil |
| oliveOil | 0.084 | |
| crude | 0.18 | Varies widely |
| motorOil30W | 0.25 | |
| siliconeOil | 0.35 | Medical grade |
| gearOil | 0.5 | SAE 90 |
| heavyFuelOil | 0.5 | Bunker |

### Heavy Oils (Pa·s)

| Material | η | Notes |
|----------|---|-------|
| castoroil | 0.986 | Very thick |

### Syrups & Food (Pa·s)

| Material | η | Notes |
|----------|---|-------|
| mapleSyrup | 0.15 | |
| corn_Syrup | 5.0 | |
| molasses | 8.0 | |
| honey | 10.0 | Classic example |
| chocolateSyrup | 25.0 | |
| caramel | 50.0 | Warm |
| ketchup | 50.0 | Shear-thinning at rest |
| mayonnaise | 200.0 | |
| peanutButter | 250.0 | |

### Industrial (Pa·s)

| Material | η | Notes |
|----------|---|-------|
| varnish | 0.6 | |
| paint | 1.0 | House paint |
| latex | 5.0 | Paint |
| epoxy | 30.0 | Uncured resin |

### Extreme Viscosity (Pa·s)

| Material | η | Notes |
|----------|---|-------|
| lava | 100.0 | Basaltic at ~1200°C |
| tar | 30000.0 | Hot |
| asphalt | 100000.0 | Hot |
| pitch | 230000000.0 | The pitch drop experiment |
| glass | 10000000000.0 | At softening point |
| waterIce | 10000000000.0 | Solid |

### Biological (Pa·s)

| Material | η | Notes |
|----------|---|-------|
| saliva | 0.001 | |
| bloodPlasma | 0.0015 | |
| wholeBlood | 0.004 | Shear-thinning |
| synovialFluid | 0.05 | Joint lubricant |
| mucus | 1.0 | Respiratory |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // fluid // surface tension
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Surface Tension

Force per unit length at liquid surface, causing minimization of surface area.
Determines droplet shape, capillary action, and bubble formation.

### Core Type

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| SurfaceTension | Number | 0.001 | 1.0 | clamps | N/m (or J/m²) |

**Formula**: Young-Laplace equation: ΔP = 2γ/r (pressure across curved surface)

**Reference**: Water at 20°C = 0.0728 N/m

### Operations

```purescript
hasHighTension :: SurfaceTension -> Boolean  -- > 0.05 N/m
hasLowTension :: SurfaceTension -> Boolean   -- < 0.03 N/m
tensionCategory :: SurfaceTension -> String
-- "very-low" (<0.02), "low" (0.02-0.04), "medium" (0.04-0.08), "high" (>0.08)
relativeToWater :: SurfaceTension -> Number  -- Water = 1.0
contactAngle :: SurfaceTension -> SurfaceTension -> Number  -- Degrees
capillaryRise :: SurfaceTension -> Number -> Number  -- Height in meters
dropletPressure :: SurfaceTension -> Number -> Number  -- Pascals
lerp :: Number -> SurfaceTension -> SurfaceTension -> SurfaceTension
```

────────────────────────────────────────────────────────────────────────────────
                                                  // surface tension // presets
────────────────────────────────────────────────────────────────────────────────

### Water & Aqueous (N/m)

| Material | γ | Notes |
|----------|---|-------|
| soapyWater | 0.025 | Surfactant reduced |
| waterDetergent | 0.030 | Strong surfactant |
| water100C | 0.0589 | Hot |
| water | 0.0728 | Reference at 20°C |
| seawater | 0.0735 | |
| sulfuricAcid | 0.0735 | Concentrated |
| water0C | 0.0756 | Cold |

### Alcohols (N/m)

| Material | γ | Notes |
|----------|---|-------|
| ethanol | 0.0223 | |
| methanol | 0.0226 | |
| ammonia | 0.0234 | Liquid at -33°C |
| propanol | 0.0237 | |
| butanol | 0.0245 | |
| nitricAcid | 0.0435 | |
| ethyleneGlycol | 0.0484 | |
| glycerol | 0.0634 | |

### Organic Solvents (N/m)

| Material | γ | Notes |
|----------|---|-------|
| diethylEther | 0.0170 | Low |
| hexane | 0.0184 | |
| acetone | 0.0237 | |
| carbonTetrachloride | 0.0270 | |
| chloroform | 0.0271 | |
| toluene | 0.0284 | |
| benzene | 0.0289 | |

### Oils (N/m)

| Material | γ | Notes |
|----------|---|-------|
| siliconeOil | 0.021 | PDMS |
| mineralOil | 0.030 | |
| oliveOil | 0.032 | |
| vegetableOil | 0.032 | |
| coconutOil | 0.033 | |
| castoroil | 0.035 | |

### Cryogenic Liquids (N/m)

| Material | γ | Notes |
|----------|---|-------|
| liquidHelium | 0.00012 | At -269°C, near zero |
| liquidNitrogen | 0.00885 | At -196°C |
| liquidOxygen | 0.0132 | At -183°C |

### Liquid Metals (N/m)

| Material | γ | Notes |
|----------|---|-------|
| liquidSodium | 0.191 | |
| mercury | 0.485 | Very high |
| gallium | 0.718 | |
| liquidIron | 0.860 | At melting point |
| liquidGold | 0.879 | At melting point |

### Biological (N/m)

| Material | γ | Notes |
|----------|---|-------|
| milk | 0.046 | |
| honey | 0.050 | |
| blood | 0.058 | |
| urine | 0.066 | |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // fluid // flow behavior
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Flow Behavior (Newtonian & Non-Newtonian)

Classification of fluid response to shear stress. Critical for accurate
simulation of complex fluids.

### FlowBehavior Enum

```purescript
data FlowBehavior
  = Newtonian          -- Constant viscosity (water, oils)
  | ShearThinning      -- Viscosity decreases with shear (ketchup, paint)
  | ShearThickening    -- Viscosity increases with shear (cornstarch)
  | BinghamPlasticType -- Yields only above threshold (toothpaste)
  | Thixotropic        -- Viscosity decreases over time (yogurt)
  | Rheopectic         -- Viscosity increases over time (rare)
  | Viscoelastic       -- Both viscous and elastic (silly putty)
```

### Mathematical Models

**Power Law**: τ = K × γ̇ⁿ
- n < 1: Shear-thinning (pseudoplastic)
- n = 1: Newtonian
- n > 1: Shear-thickening (dilatant)

**Bingham Plastic**: τ = τ₀ + μ × γ̇ (above yield stress τ₀)

**Herschel-Bulkley**: τ = τ₀ + K × γ̇ⁿ (generalized)

### Power Law Index

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| PowerLawIndex | Number | 0.1 | 3.0 | clamps | n in power law |

### Yield Stress

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| YieldStress | Number | 0.0 | 10000.0 | clamps | τ₀ in Pascals |

### Consistency Index

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| ConsistencyIndex | Number | 0.0001 | 10000.0 | clamps | K in Pa·sⁿ |

### Operations

```purescript
apparentViscosity :: PowerLawFluid -> Number -> Number
-- μ_app = K × γ̇^(n-1) at given shear rate

canFlow :: BinghamPlastic -> Number -> Boolean
-- True if applied stress > yield stress

flowCategory :: FlowBehavior -> String
-- "newtonian", "pseudoplastic", "dilatant", "yield-stress",
-- "time-thinning", "time-thickening", "viscoelastic"
```

────────────────────────────────────────────────────────────────────────────────
                                                    // flow behavior // presets
────────────────────────────────────────────────────────────────────────────────

### Newtonian Fluids

| Material | Viscosity (Pa·s) | Notes |
|----------|------------------|-------|
| waterBehavior | 0.001 | Classic Newtonian |
| oilBehavior | 0.08 | Room temperature |
| honeyBehavior | 10.0 | Newtonian despite thickness |

### Shear-Thinning (Pseudoplastic)

| Material | K | n | Notes |
|----------|---|---|-------|
| ketchupBehavior | 50.0 | 0.3 | Classic example |
| paintBehavior | 5.0 | 0.5 | Easy application |
| shampoo_Behavior | 3.0 | 0.45 | Easy dispensing |
| yogurtBehavior | 25.0 | 0.4 | Also thixotropic |
| bloodBehavior | 0.012 | 0.8 | Slightly shear-thinning |

### Shear-Thickening (Dilatant)

| Material | K | n | Notes |
|----------|---|---|-------|
| cornstarchSlurry | 2.0 | 1.8 | "Oobleck" |

### Bingham Plastics

| Material | τ₀ (Pa) | μ (Pa·s) | Notes |
|----------|---------|----------|-------|
| cementBehavior | 50.0 | 10.0 | |
| mayonnaiseBehavior | 90.0 | 30.0 | |
| toothpasteBehavior | 100.0 | 20.0 | Classic example |
| peanutButterBehavior | 200.0 | 50.0 | High yield |

### Herschel-Bulkley

| Material | τ₀ (Pa) | K | n | Notes |
|----------|---------|---|---|-------|
| chocolateBehavior | 20.0 | 15.0 | 0.6 | |
| lavaBehavior | 1000.0 | 100.0 | 0.7 | High yield, shear-thinning |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             // element // adt
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Chemical Elements (Periodic Table)

Complete IUPAC periodic table with all 118 elements.

### Core Type

```purescript
data Element
  -- Period 1
  = Hydrogen      -- Z=1
  | Helium        -- Z=2
  -- Period 2
  | Lithium       -- Z=3
  | Beryllium     -- Z=4
  | Boron         -- Z=5
  | Carbon        -- Z=6
  | Nitrogen      -- Z=7
  | Oxygen        -- Z=8
  | Fluorine      -- Z=9
  | Neon          -- Z=10
  -- ... 108 more elements through Oganesson (Z=118)
```

All 118 IUPAC elements from Hydrogen (Z=1) to Oganesson (Z=118).

### Atomic Number

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| AtomicNumber | Int | 1 | 118 | clamps | Proton count |

```purescript
atomicNumber :: Element -> AtomicNumber
fromAtomicNumber :: AtomicNumber -> Maybe Element
-- Bijection: fromAtomicNumber (atomicNumber e) = Just e
```

### Element Symbols

```purescript
symbol :: Element -> String
-- "H", "He", "Li", ..., "Og" (1-2 characters, IUPAC standard)

name :: Element -> String
-- "Hydrogen", "Helium", ..., "Oganesson"

fromSymbol :: String -> Maybe Element
-- Case-insensitive lookup
```

────────────────────────────────────────────────────────────────────────────────
                                                        // element // category
────────────────────────────────────────────────────────────────────────────────

### Element Category

```purescript
data ElementCategory
  = AlkaliMetal          -- Group 1 (except H): Li, Na, K, Rb, Cs, Fr
  | AlkalineEarthMetal   -- Group 2: Be, Mg, Ca, Sr, Ba, Ra
  | TransitionMetal      -- Groups 3-12 (d-block)
  | PostTransitionMetal  -- Al, Ga, In, Sn, Tl, Pb, Bi, Po, Fl, Mc, Lv
  | Metalloid            -- B, Si, Ge, As, Sb, Te, At
  | ReactiveNonmetal     -- H, C, N, O, P, S, Se, F, Cl, Br, I
  | NobleGas             -- Group 18: He, Ne, Ar, Kr, Xe, Rn, Og
  | Lanthanide           -- Z=57-71: La through Lu
  | Actinide             -- Z=89-103: Ac through Lr
  | Unknown              -- Nh, Ts (properties unconfirmed)
```

### Category Operations

```purescript
category :: Element -> ElementCategory
categoryColor :: ElementCategory -> String  -- Hex for periodic table UI

isMetal :: Element -> Boolean
isNonmetal :: Element -> Boolean
isMetalloid :: Element -> Boolean
isNobleGas :: Element -> Boolean
isAlkaliMetal :: Element -> Boolean
isAlkalineEarthMetal :: Element -> Boolean
isTransitionMetal :: Element -> Boolean
isLanthanide :: Element -> Boolean
isActinide :: Element -> Boolean
isHalogen :: Element -> Boolean
isPostTransitionMetal :: Element -> Boolean
isReactiveNonmetal :: Element -> Boolean

isNaturallyOccurring :: Element -> Boolean  -- Z <= 94
isSynthetic :: Element -> Boolean           -- Z > 94
isRadioactive :: Element -> Boolean         -- Z >= 84 or Z == 43 or Z == 61
```

### Category Colors (Periodic Table UI)

| Category | Color |
|----------|-------|
| AlkaliMetal | #FF6B6B |
| AlkalineEarthMetal | #FFE66D |
| TransitionMetal | #4ECDC4 |
| PostTransitionMetal | #95E1D3 |
| Metalloid | #A8D8EA |
| ReactiveNonmetal | #98D8C8 |
| NobleGas | #C9B1FF |
| Lanthanide | #FFB7B2 |
| Actinide | #FFDAC1 |
| Unknown | #E2E2E2 |

────────────────────────────────────────────────────────────────────────────────
                                                    // element // group period
────────────────────────────────────────────────────────────────────────────────

### Group (Column 1-18)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Group | Int | 1 | 18 | clamps | Periodic table column |

```purescript
group :: Element -> Group
groupName :: Group -> Maybe String
-- Just "Alkali metals" (1), Just "Alkaline earth metals" (2),
-- Just "Halogens" (17), Just "Noble gases" (18), Nothing (others)
```

### Period (Row 1-7)

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Period | Int | 1 | 7 | clamps | Periodic table row |

```purescript
period :: Element -> Period
```

**Element count by period:**
- Period 1: 2 elements (H, He)
- Period 2: 8 elements (Li–Ne)
- Period 3: 8 elements (Na–Ar)
- Period 4: 18 elements (K–Kr)
- Period 5: 18 elements (Rb–Xe)
- Period 6: 32 elements (Cs–Rn)
- Period 7: 32 elements (Fr–Og)

────────────────────────────────────────────────────────────────────────────────
                                                          // element // block
────────────────────────────────────────────────────────────────────────────────

### Block (Orbital Classification)

```purescript
data ElementBlock
  = SBlock  -- Groups 1-2 + He (s orbital filling)
  | PBlock  -- Groups 13-18 (p orbital filling)
  | DBlock  -- Groups 3-12 (d orbital, transition metals)
  | FBlock  -- Lanthanides and Actinides (f orbital filling)
```

```purescript
block :: Element -> ElementBlock
```

**Block composition:**
- **s-block**: 14 elements (H, He, Li, Be, Na, Mg, K, Ca, Rb, Sr, Cs, Ba, Fr, Ra)
- **p-block**: 36 elements (B–Ne, Al–Ar, Ga–Kr, In–Xe, Tl–Rn, Nh–Og)
- **d-block**: 40 elements (Sc–Zn, Y–Cd, Hf–Cn, Rf–Cn)
- **f-block**: 28 elements (La–Lu, Ac–Lr)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                // formulas
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Physical Formulas

### Fresnel Reflectance at Normal Incidence

```
F₀ = ((n₁ - n₂) / (n₁ + n₂))²
```

For air-to-material (n₁ = 1):
```
F₀ = ((1 - n) / (1 + n))²
```

### Critical Angle for Total Internal Reflection

```
θ_c = arcsin(n₂ / n₁)    (only when n₁ > n₂)
```

### Abbe Number (Dispersion)

```
Vd = (n_d - 1) / (n_F - n_C)
```
Where:
- n_d = refractive index at 587.6nm (helium d-line)
- n_F = refractive index at 486.1nm (hydrogen F-line)
- n_C = refractive index at 656.3nm (hydrogen C-line)

### Fourier's Law (Heat Conduction)

```
q = -k × ∇T
```
Heat flux = conductivity × temperature gradient

### Newton's Law of Viscosity

```
τ = μ × (du/dy)
```
Shear stress = viscosity × velocity gradient

### Power Law (Non-Newtonian)

```
τ = K × γ̇ⁿ
```
- n < 1: Shear-thinning
- n = 1: Newtonian
- n > 1: Shear-thickening

### Bingham Plastic

```
τ = τ₀ + μ × γ̇    (when τ > τ₀)
```
Requires yield stress to flow

### Young-Laplace Equation (Surface Tension)

```
ΔP = 2γ/r
```
Pressure difference across curved surface

### Capillary Rise

```
h = 2γ cos(θ) / (ρgr)
```
Height of liquid rise in tube

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                // philosophy
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Design Philosophy

### Why Physical Properties Matter

The Physical pillar exists because **perception is not presentation**.

When a user touches simulated gold in a BMI system, they don't just see gold—
they *feel* gold. The thermal conductivity matters. The density matters. The
hardness matters. Gold feels cold because it conducts heat away from your hand
at 318 W/(m·K). Gold feels heavy because it's 19,320 kg/m³. Gold feels soft
because it's only Mohs 2.5.

### Data Source Authority

All values come from authoritative sources:
- **CRC Handbook of Chemistry and Physics** — fundamental reference
- **Schott Glass Catalog** — optical glass properties
- **Gemological Institute of America (GIA)** — gemstone properties
- **MatWeb** — engineering materials database
- **IUPAC** — periodic table authority

Values are for:
- **Temperature**: 20-25°C (room temperature) unless otherwise noted
- **Pressure**: 1 atm (STP) for gases
- **Wavelength**: 589nm (sodium D-line) for optical properties

### Bounded Determinism

Every type has explicit bounds. No unbounded Numbers. No Infinity. No NaN.

This ensures:
- **Reproducibility**: Same input = same output, always
- **Composability**: Agents can combine properties without fear of edge cases
- **Verifiability**: Lean4 proofs can reason about bounded values

### Material Composition

Physical properties compose into materials:

```purescript
type Material =
  { ior :: IOR
  , density :: Density
  , hardness :: MohsHardness
  , thermalK :: ThermalConductivity
  , viscosity :: Maybe DynamicViscosity  -- Liquids only
  , surfaceTension :: Maybe SurfaceTension  -- Liquids only
  , flowBehavior :: Maybe FlowBehavior  -- Fluids only
  }
```

An agent creating "crystal glass" composes:
- IOR: 1.65 (lead glass)
- Density: 2500 kg/m³
- Hardness: 5.5 Mohs
- Thermal K: 1.0 W/(m·K)

Deterministic. Composable. Verifiable.

### The "Cold Metal" Insight

The most important insight in the Physical pillar: **thermal conductivity
determines touch temperature perception**.

Metal and wood at the same temperature feel different because metal conducts
heat 4000× faster than wood:
- Copper: 401 W/(m·K)
- Wood: 0.12 W/(m·K)

This single value—thermal conductivity—is the difference between a warm wooden
handle and a cold metal blade. For haptic feedback in BMI systems, this is
foundational.

### Why Non-Newtonian Matters

Most "interesting" fluids are non-Newtonian:
- Ketchup thins when you shake it (shear-thinning)
- Cornstarch thickens when you punch it (shear-thickening)
- Toothpaste stays on your brush until you press (yield stress)
- Paint brushes on smooth but doesn't drip (shear-thinning)

For realistic fluid simulation, the FlowBehavior enum and associated models
(power law, Bingham, Herschel-Bulkley) capture this complexity in deterministic,
bounded types.

────────────────────────────────────────────────────────────────────────────────
                                                                // data sources
────────────────────────────────────────────────────────────────────────────────

## References

**Optical Properties:**
- CRC Handbook of Chemistry and Physics, 97th Edition (2016)
- Schott Optical Glass Catalog (2023)
- Gemological Institute of America Technical Reference

**Mechanical Properties:**
- MatWeb Material Property Data (matweb.com)
- Engineering ToolBox (engineeringtoolbox.com)
- CRC Handbook of Chemistry and Physics

**Thermal Properties:**
- CRC Handbook of Chemistry and Physics
- NIST Standard Reference Database
- Engineering ToolBox

**Fluid Properties:**
- CRC Handbook of Chemistry and Physics
- Food Science literature (rheology)
- Petroleum engineering handbooks

**Periodic Table:**
- IUPAC (iupac.org/what-we-do/periodic-table-of-elements/)
- Updated to 2024 naming conventions

────────────────────────────────────────────────────────────────────────────────

*Physical pillar: where atoms meet materials meet reality.*

```
                                                       — Hydrogen Schema // 2026
```
