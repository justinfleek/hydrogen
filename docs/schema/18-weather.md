━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // 18 // weather
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Weather Pillar

Atmospheric conditions, precipitation, wind, and meteorological classification.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Weather/`
- **Files**: 17 modules (3 leader + 14 submodules)
- **Lines**: 3,334 total
- **Key features**: Atmosphere (temperature, pressure, humidity, visibility),
  precipitation (rain, snow, hail), wind (speed, direction, Beaufort scale)

## Purpose

Weather provides bounded, deterministic primitives for:
- Atmospheric state (temperature, pressure, humidity, dew point)
- Visibility and cloud cover with aviation-standard categories
- Precipitation types, rates, and physical properties
- Wind speed, direction, gusts, and turbulence
- The complete Beaufort wind scale (0-12)
- Meteorological calculations (heat index, wind chill, density altitude)

## Why This Matters

At billion-agent scale, weather state determines:
- **Rendering**: Fog, haze, sky color, cloud rendering, precipitation particles
- **Audio**: Sound propagation, rain/wind ambience, muffling
- **Haptic**: Humidity feel, temperature sensation, wind resistance
- **Simulation**: Flight physics, thermal updrafts, visibility constraints
- **Mood**: Oppressive humidity, crisp cold, stormy drama

────────────────────────────────────────────────────────────────────────────────
                                                             // module structure
────────────────────────────────────────────────────────────────────────────────

## Module Hierarchy

```
Weather/
├── Atmosphere.purs          (331 lines) — Leader module
│   ├── Temperature.purs     (148 lines)
│   ├── Pressure.purs        (150 lines)
│   ├── Humidity.purs        (214 lines)
│   ├── Visibility.purs      (185 lines)
│   ├── CloudCover.purs      (164 lines)
│   └── Layer.purs           (69 lines)
├── Precipitation.purs       (299 lines) — Leader module
│   ├── Types.purs           (96 lines)
│   ├── Rate.purs            (197 lines)
│   ├── Rain.purs            (131 lines)
│   ├── Snow.purs            (169 lines)
│   └── Hail.purs            (149 lines)
└── Wind.purs                (300 lines) — Leader module
    ├── Speed.purs           (180 lines)
    ├── Direction.purs       (222 lines)
    ├── Beaufort.purs        (165 lines)
    └── Gust.purs            (165 lines)
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                  // ATMOSPHERE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

────────────────────────────────────────────────────────────────────────────────
                                                         // temperature // atom
────────────────────────────────────────────────────────────────────────────────

## Temperature

Air temperature at measurement height, stored in Celsius.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Temperature | Number | -100.0 | 100.0 | clamps | Celsius, covers all Earth records |

**Bounds Rationale:**
- Minimum -100C: Below coldest recorded (-89.2C Vostok, Antarctica)
- Maximum +100C: Above boiling point, covers extreme scenarios

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `tempAbsoluteZero` | -100.0C | Clamped from true -273.15C |
| `tempFreezingPoint` | 0.0C | Water freezing at sea level |
| `tempRoomTemp` | 20.0C | Standard comfortable indoor |
| `tempBodyTemp` | 37.0C | Human body temperature |
| `tempBoilingPoint` | 100.0C | Water boiling at sea level |
| `tempRecordLow` | -89.2C | Vostok Station, Antarctica |
| `tempRecordHigh` | 56.7C | Death Valley |

**Unit Conversions:**

| Function | Formula | Example |
|----------|---------|---------|
| `celsius` | identity | 20.0 -> 20.0 |
| `fahrenheit` | C * 9/5 + 32 | 20.0 -> 68.0 |
| `kelvin` | C + 273.15 | 20.0 -> 293.15 |

**Operations:**
- `lerp :: Number -> Temperature -> Temperature -> Temperature`
  Linear interpolation between temperatures

────────────────────────────────────────────────────────────────────────────────
                                                            // pressure // atom
────────────────────────────────────────────────────────────────────────────────

## Pressure

Barometric pressure, stored in hectopascals (hPa = millibars).

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Pressure | Number | 300.0 | 1100.0 | clamps | hPa, covers Everest to record highs |

**Bounds Rationale:**
- Minimum 300 hPa: ~9000m altitude, above Everest summit (~337 hPa)
- Maximum 1100 hPa: Above highest recorded sea-level pressure (~1085 hPa)

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `pressureStandard` | 1013.25 hPa | ISA sea-level standard |
| `pressureRecordLow` | 870.0 hPa | Typhoon center |
| `pressureRecordHigh` | 1085.0 hPa | Siberian anticyclone |
| `pressureEverest` | 337.0 hPa | Mt. Everest summit |
| `pressureDeadSea` | 1065.0 hPa | Below sea level |

**Unit Conversions:**

| Function | Formula | Example |
|----------|---------|---------|
| `hectopascals` | identity | 1013.25 -> 1013.25 |
| `millibars` | identity (same unit) | 1013.25 -> 1013.25 |
| `atmospheres` | P / 1013.25 | 1013.25 -> 1.0 |
| `inchesOfMercury` | P * 0.02953 | 1013.25 -> 29.92 |
| `mmOfMercury` | P * 0.75006 | 1013.25 -> 760.0 |

**Operations:**
- `pressureAltitude :: Pressure -> Number`
  Calculate altitude in meters: `h = 44330 * (1 - (P / P0)^0.1903)`

────────────────────────────────────────────────────────────────────────────────
                                                            // humidity // atom
────────────────────────────────────────────────────────────────────────────────

## RelativeHumidity

Ratio of actual water vapor to saturation vapor pressure.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| RelativeHumidity | Number | 0.0 | 100.0 | clamps | Percent |

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `humidityDesert` | 15% | Arid desert air |
| `humidityComfortable` | 45% | Ideal indoor range |
| `humidityHumid` | 75% | Muggy conditions |
| `humiditySaturated` | 100% | Fog/cloud formation |

## DewPoint

Temperature at which condensation occurs, indicates moisture content.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| DewPoint | Number | -80.0 | 40.0 | clamps | Celsius |

**Bounds Rationale:**
- Minimum -80C: Extremely dry air (Antarctica interior)
- Maximum +40C: Extremely humid (Persian Gulf extremes)

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `dewPointDry` | -10C | Very dry air |
| `dewPointComfortable` | 10C | Pleasant humidity |
| `dewPointHumid` | 18C | Noticeable humidity |
| `dewPointOppressive` | 24C | Tropical, sticky |

**Dew Point Comfort Scale:**

| Dew Point | Perception |
|-----------|------------|
| < 10C | Dry, pleasant |
| 10-15C | Comfortable |
| 16-18C | Slightly humid |
| 19-21C | Somewhat uncomfortable |
| 22-24C | Very humid, muggy |
| > 24C | Oppressive, tropical |

**Operations:**

```purescript
-- Magnus-Tetens approximation
calculateDewPoint :: Temperature -> RelativeHumidity -> DewPoint
-- Td = b * alpha / (a - alpha)
-- where alpha = a * T / (b + T) + ln(RH/100)
-- a = 17.27, b = 237.7C

calculateHumidity :: Temperature -> DewPoint -> RelativeHumidity
-- RH = 100 * exp(a * Td / (b + Td)) / exp(a * T / (b + T))
```

────────────────────────────────────────────────────────────────────────────────
                                                          // visibility // atom
────────────────────────────────────────────────────────────────────────────────

## Visibility

Distance at which objects can be discerned, in meters.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Visibility | Number | 0.0 | 100000.0 | clamps | Meters |

**Bounds Rationale:**
- Minimum 0: Zero visibility (dense fog, whiteout)
- Maximum 100000: 100km "unlimited" visibility in very clear air

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `visibilityZero` | 0m | Total obscuration |
| `visibilityDenseFog` | 30m | Extremely hazardous |
| `visibilityFog` | 100m | Standard fog |
| `visibilityMist` | 500m | Light fog/mist |
| `visibilityHaze` | 5000m | Atmospheric haze |
| `visibilityClear` | 20000m | Good conditions |
| `visibilityUnlimited` | 80000m | Crystal clear |

**Unit Conversions:**

| Function | Formula | Example |
|----------|---------|---------|
| `visibilityMeters` | identity | 10000 -> 10000 |
| `visibilityKilometers` | m / 1000 | 10000 -> 10.0 |
| `visibilityMiles` | m / 1609.34 | 10000 -> 6.21 |

## VisibilityCategory Enum

Aviation-standard visibility classification.

| Constructor | Range | Description |
|-------------|-------|-------------|
| `VisZero` | < 50m | Zero visibility, LIFR conditions |
| `VisDenseFog` | 50-200m | Dense fog |
| `VisFog` | 200-1000m | Standard fog |
| `VisMist` | 1-5km | Mist or light fog |
| `VisHaze` | 5-10km | Atmospheric haze |
| `VisClear` | > 10km | Clear conditions |

**Operations:**
- `visibilityToCategory :: Visibility -> VisibilityCategory`
- `categoryToMinVisibility :: VisibilityCategory -> Visibility`

────────────────────────────────────────────────────────────────────────────────
                                                         // cloud cover // atom
────────────────────────────────────────────────────────────────────────────────

## CloudCover

Percentage of sky obscured by clouds.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| CloudCover | Number | 0.0 | 100.0 | clamps | Percent |

**Presets:**

| Name | Value | Oktas | Description |
|------|-------|-------|-------------|
| `cloudCoverClear` | 0% | 0 | No clouds |
| `cloudCoverFewClouds` | 12.5% | 1 | Few scattered |
| `cloudCoverScattered` | 37.5% | 3 | Scattered |
| `cloudCoverBroken` | 62.5% | 5 | More cloud than sky |
| `cloudCoverOvercast` | 100% | 8 | Complete cover |

**Okta Conversion:**

Oktas are eighths of sky coverage (0-8), standard in meteorology.

| Percent Range | Oktas |
|---------------|-------|
| 0% | 0 |
| 0.1-12.5% | 1 |
| 12.6-25% | 2 |
| 25.1-37.5% | 3 |
| 37.6-50% | 4 |
| 50.1-62.5% | 5 |
| 62.6-75% | 6 |
| 75.1-87.5% | 7 |
| 87.6-100% | 8 |

## CloudCategory Enum (METAR Standard)

| Constructor | Oktas | Abbreviation | Description |
|-------------|-------|--------------|-------------|
| `SKC` | 0 | SKC | Sky clear |
| `FEW` | 1-2 | FEW | Few clouds |
| `SCT` | 3-4 | SCT | Scattered |
| `BKN` | 5-7 | BKN | Broken |
| `OVC` | 8 | OVC | Overcast |

────────────────────────────────────────────────────────────────────────────────
                                                    // atmospheric layer // enum
────────────────────────────────────────────────────────────────────────────────

## AtmosphericLayer Enum

Classification by altitude and temperature profile.

| Constructor | Altitude Range | Description |
|-------------|----------------|-------------|
| `Troposphere` | 0-12 km | Weather layer, temp decreases with altitude |
| `Stratosphere` | 12-50 km | Ozone layer, temp increases with altitude |
| `Mesosphere` | 50-80 km | Coldest layer, meteors burn up here |
| `Thermosphere` | 80-700 km | Hot but thin, aurora and ISS orbit here |
| `Exosphere` | 700-10000 km | Transition to space, particles escape |

**Operations:**
- `layerAltitudeRange :: AtmosphericLayer -> { min :: Number, max :: Number }`
- `layerDescription :: AtmosphericLayer -> String`

────────────────────────────────────────────────────────────────────────────────
                                                 // atmospheric state // compound
────────────────────────────────────────────────────────────────────────────────

## AtmosphericState

Complete atmospheric state combining all atmosphere atoms.

```purescript
data AtmosphericState = AtmosphericState
  { temp :: Temperature
  , press :: Pressure
  , humidity :: RelativeHumidity
  , dewPt :: DewPoint
  , vis :: Visibility
  , clouds :: CloudCover
  }
```

**Presets:**

| Name | Description |
|------|-------------|
| `defaultAtmosphere` | Comfortable conditions (20C, 1013.25hPa, 45% RH, clear) |
| `standardAtmosphere` | ICAO ISA at sea level (15C, 1013.25hPa, dry air) |

**Composite Operations:**

```purescript
-- Density altitude in meters
-- densityAltitude = PA + 120 * (ISA_temp - actual_temp)
densityAltitude :: Pressure -> Temperature -> Number

-- Speed of sound in m/s
-- c = 331.3 * sqrt(1 + T/273.15)
soundSpeed :: Temperature -> Number

-- Air density in kg/m3
-- rho = P / (R * T) where R = 287.05 J/(kg*K)
airDensity :: Pressure -> Temperature -> Number

-- Heat index (feels-like) using Rothfusz regression
-- Valid for T > 27C and RH > 40%
heatIndex :: Temperature -> RelativeHumidity -> Temperature

-- Humidex (Canadian "feels like")
-- Humidex = T + 5/9 * (e - 10)
humidex :: Temperature -> DewPoint -> Temperature

-- Comfort check (18-26C, 30-60% RH, vis > 5km)
isComfortable :: AtmosphericState -> Boolean

-- Fog check (visibility < 1000m)
isFoggy :: AtmosphericState -> Boolean
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                // PRECIPITATION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

────────────────────────────────────────────────────────────────────────────────
                                                   // precipitation type // enum
────────────────────────────────────────────────────────────────────────────────

## PrecipitationType Enum

Classification by physical form and formation mechanism.

| Constructor | Phase | Description |
|-------------|-------|-------------|
| `Rain` | Liquid | Drops 0.5-5mm diameter |
| `Drizzle` | Liquid | Fine drops < 0.5mm |
| `Snow` | Frozen | Ice crystals (various forms) |
| `Sleet` | Frozen | Ice pellets (frozen rain) |
| `FreezingRain` | Liquid* | Supercooled, freezes on contact |
| `Hail` | Frozen | Layered ice spheres from convection |
| `Graupel` | Frozen | Soft rime pellets |
| `IcePellets` | Frozen | Small clear ice |
| `MixedRainSnow` | Mixed | Rain/snow transition zone |
| `MixedSleet` | Mixed | Sleet/freezing rain combination |

**Classification Functions:**
- `isLiquid :: PrecipitationType -> Boolean` -- Rain, Drizzle, FreezingRain
- `isFrozen :: PrecipitationType -> Boolean` -- Snow, Sleet, Hail, Graupel, IcePellets
- `isMixed :: PrecipitationType -> Boolean` -- MixedRainSnow, MixedSleet

────────────────────────────────────────────────────────────────────────────────
                                                              // rate // atom
────────────────────────────────────────────────────────────────────────────────

## PrecipitationRate

Precipitation intensity in mm/hour (water equivalent).

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| PrecipitationRate | Number | 0.0 | 500.0 | clamps | mm/hr |

**Bounds Rationale:**
- Minimum 0: No precipitation
- Maximum 500: Exceeds any recorded sustained rate (~300 mm/hr max bursts)

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `rateNone` | 0.0 mm/hr | No precipitation |
| `rateTrace` | 0.1 mm/hr | Barely measurable |
| `rateLight` | 1.5 mm/hr | Light rain |
| `rateModerate` | 5.0 mm/hr | Steady rain |
| `rateHeavy` | 25.0 mm/hr | Heavy rain |
| `rateViolent` | 75.0 mm/hr | Severe rain |
| `rateTorrential` | 150.0 mm/hr | Tropical deluge |

**Unit Conversions:**

| Function | Formula | Example |
|----------|---------|---------|
| `mmPerHour` | identity | 25.0 -> 25.0 |
| `inchesPerHour` | mm / 25.4 | 25.0 -> 0.98 |

## Intensity Enum (WMO Standard)

| Constructor | Range | Description |
|-------------|-------|-------------|
| `IntensityNone` | 0 mm/hr | No precipitation |
| `IntensityTrace` | < 0.5 mm/hr | Barely measurable |
| `IntensityLight` | 0.5-2.5 mm/hr | Light precipitation |
| `IntensityModerate` | 2.5-10 mm/hr | Moderate |
| `IntensityHeavy` | 10-50 mm/hr | Heavy |
| `IntensityViolent` | > 50 mm/hr | Violent/extreme |

**Operations:**
- `rateToIntensity :: PrecipitationRate -> Intensity`
- `intensityToMinRate :: Intensity -> PrecipitationRate`
- `lerp :: Number -> PrecipitationRate -> PrecipitationRate -> PrecipitationRate`

────────────────────────────────────────────────────────────────────────────────
                                                         // rain droplet // atom
────────────────────────────────────────────────────────────────────────────────

## DropletDiameter

Raindrop diameter in millimeters.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| DropletDiameter | Number | 0.1 | 8.0 | clamps | mm |

**Bounds Rationale:**
- Minimum 0.1mm: Below this is mist/fog (suspended, not falling)
- Maximum 8.0mm: Drops break up above ~6mm due to drag; 8mm theoretical max

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `dropletMist` | 0.15 mm | Suspended mist |
| `dropletDrizzle` | 0.4 mm | Fine drizzle |
| `dropletLight` | 1.0 mm | Light rain |
| `dropletModerate` | 2.5 mm | Moderate rain |
| `dropletHeavy` | 4.0 mm | Heavy rain |

**Operations:**

```purescript
-- Terminal velocity (m/s)
-- v = 4.5 * sqrt(d) (where d in mm)
-- Valid for d in [0.5, 6] mm, returns ~2-9 m/s
terminalVelocity :: DropletDiameter -> Number

-- Impact energy (millijoules)
-- E = 0.5 * m * v^2
-- m = (4/3) * pi * r^3 * rho_water
impactEnergy :: DropletDiameter -> Number
```

**Terminal Velocity Reference:**

| Diameter | Terminal Velocity |
|----------|-------------------|
| 0.5 mm | ~3.2 m/s |
| 1.0 mm | ~4.5 m/s |
| 2.0 mm | ~6.4 m/s |
| 4.0 mm | ~9.0 m/s |

────────────────────────────────────────────────────────────────────────────────
                                                       // snowflake type // enum
────────────────────────────────────────────────────────────────────────────────

## SnowflakeType Enum (Nakaya Classification)

Crystal form depends on temperature and supersaturation.

| Constructor | Temperature | Description |
|-------------|-------------|-------------|
| `Plates` | 0 to -4C | Flat hexagonal plates |
| `StellarDendrites` | -12 to -16C | Classic six-branched stars |
| `Columns` | -5 to -8C | Hexagonal columns |
| `Needles` | -5 to -8C | Long thin crystals |
| `SpatialDendrites` | -12 to -16C | Three-dimensional branching |
| `CappedColumns` | varies | Columns with plate caps at ends |
| `IrregularCrystals` | varies | Mixed or deformed forms |
| `SnowGraupel` | varies | Rime-coated crystals (soft hail) |
| `SleetCrystals` | varies | Refrozen raindrops |

────────────────────────────────────────────────────────────────────────────────
                                                        // snow density // atom
────────────────────────────────────────────────────────────────────────────────

## SnowDensity

Snow density in kg/m3, determines snow:water ratio.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| SnowDensity | Number | 20.0 | 917.0 | clamps | kg/m3 |

**Bounds Rationale:**
- Minimum 20 kg/m3: Very light powder (50:1 ratio)
- Maximum 917 kg/m3: Pure ice density

**Presets:**

| Name | Value | Ratio | Description |
|------|-------|-------|-------------|
| `densityPowder` | 50 kg/m3 | ~20:1 | Fresh powder snow |
| `densityFresh` | 100 kg/m3 | ~10:1 | Fresh fallen snow |
| `densitySettled` | 200 kg/m3 | ~5:1 | Settled, aged snow |
| `densityWet` | 400 kg/m3 | ~2.5:1 | Heavy wet snow |
| `densityCompacted` | 550 kg/m3 | ~1.8:1 | Near firn |
| `densityIce` | 917 kg/m3 | 1:1 | Glacial ice |

**Snow:Water Ratio:**

The ratio tells how many inches of snow equals one inch of liquid water:
- 20:1 = 20 inches of powder per 1 inch water
- 10:1 = 10 inches of fresh snow per 1 inch water
- 5:1 = 5 inches of wet snow per 1 inch water

────────────────────────────────────────────────────────────────────────────────
                                                        // hail diameter // atom
────────────────────────────────────────────────────────────────────────────────

## HailDiameter

Hail stone diameter in millimeters.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| HailDiameter | Number | 5.0 | 150.0 | clamps | mm |

**Bounds Rationale:**
- Minimum 5mm: Below this is graupel/ice pellets
- Maximum 150mm: ~6 inches, near record sizes

**Presets:**

| Name | Value | Comparison | Description |
|------|-------|------------|-------------|
| `hailPea` | 6 mm | Pea | Typical small hail |
| `hailMarble` | 15 mm | Marble | Common hail |
| `hailGolfBall` | 44 mm | Golf ball | Severe hail |
| `hailTennisBall` | 64 mm | Tennis ball | Significant |
| `hailSoftball` | 100 mm | Softball | Giant, damaging |

## HailCategory Enum (NOAA/NWS)

| Constructor | Range | Description |
|-------------|-------|-------------|
| `HailSmall` | < 25mm | Quarter-sized or smaller |
| `HailSevere` | 25-50mm | Quarter to golf ball |
| `HailSignificant` | 50-75mm | Golf ball to tennis ball |
| `HailGiant` | > 75mm | Larger than tennis ball |

**Operations:**
- `hailToCategory :: HailDiameter -> HailCategory`
- `categoryToMinDiameter :: HailCategory -> HailDiameter`

────────────────────────────────────────────────────────────────────────────────
                                                         // accumulation // atom
────────────────────────────────────────────────────────────────────────────────

## Accumulation

Precipitation accumulation in millimeters.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Accumulation | Number | 0.0 | 5000.0 | clamps | mm |

**Bounds Rationale:**
- Minimum 0: No accumulation
- Maximum 5000: 5 meters of snow or 200 inches (extreme seasonal)

**Operations:**

```purescript
-- Convert snow depth to water equivalent
-- water_mm = snow_mm * (density / 1000)
waterEquivalent :: Accumulation -> SnowDensity -> Accumulation
```

────────────────────────────────────────────────────────────────────────────────
                                                // precipitation event // compound
────────────────────────────────────────────────────────────────────────────────

## PrecipitationEvent

Sum type capturing type-specific precipitation parameters.

```purescript
data PrecipitationEvent
  = RainEvent
      { rate :: PrecipitationRate
      , dropletSize :: DropletDiameter
      }
  | SnowEvent
      { rate :: PrecipitationRate  -- Water equivalent
      , snowflake :: SnowflakeType
      , density :: SnowDensity
      }
  | SleetEvent
      { rate :: PrecipitationRate
      }
  | HailEvent
      { rate :: PrecipitationRate
      , size :: HailDiameter
      }
  | FreezingRainEvent
      { rate :: PrecipitationRate
      , dropletSize :: DropletDiameter
      }
  | MixedEvent
      { rainRate :: PrecipitationRate
      , snowRate :: PrecipitationRate
      }
```

**Constructors:**
- `rainEvent :: PrecipitationRate -> DropletDiameter -> PrecipitationEvent`
- `snowEvent :: PrecipitationRate -> SnowflakeType -> SnowDensity -> PrecipitationEvent`
- `sleetEvent :: PrecipitationRate -> PrecipitationEvent`
- `hailEvent :: PrecipitationRate -> HailDiameter -> PrecipitationEvent`
- `freezingRainEvent :: PrecipitationRate -> DropletDiameter -> PrecipitationEvent`
- `mixedEvent :: PrecipitationRate -> PrecipitationRate -> PrecipitationEvent`

**Operations:**

```purescript
-- Visibility reduction factor [0, 1]
-- 1.0 = clear, 0.0 = zero visibility
-- Different reduction rates per precipitation type
visibilityReduction :: PrecipitationEvent -> Number
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                        // WIND
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

────────────────────────────────────────────────────────────────────────────────
                                                          // wind speed // atom
────────────────────────────────────────────────────────────────────────────────

## WindSpeed

Wind velocity, stored in meters per second.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| WindSpeed | Number | 0.0 | 150.0 | clamps | m/s |

**Bounds Rationale:**
- Minimum 0: Calm conditions
- Maximum 150: Above highest recorded gusts (~113 m/s)

**Beaufort Scale Presets:**

| Name | Value | Beaufort | Description |
|------|-------|----------|-------------|
| `speedCalm` | 0.3 m/s | 0 | Smoke rises vertically |
| `speedLightAir` | 1.0 m/s | 1 | Smoke drift |
| `speedLightBreeze` | 2.5 m/s | 2 | Leaves rustle |
| `speedGentleBreeze` | 4.4 m/s | 3 | Twigs in motion |
| `speedModerateBreeze` | 6.7 m/s | 4 | Small branches move |
| `speedFreshBreeze` | 9.4 m/s | 5 | Small trees sway |
| `speedStrongBreeze` | 12.3 m/s | 6 | Large branches move |
| `speedNearGale` | 15.5 m/s | 7 | Whole trees in motion |
| `speedGale` | 19.0 m/s | 8 | Twigs break off |
| `speedStrongGale` | 22.6 m/s | 9 | Slight structural damage |
| `speedStorm` | 26.5 m/s | 10 | Trees uprooted |
| `speedViolentStorm` | 30.5 m/s | 11 | Widespread damage |
| `speedHurricane` | 40.0 m/s | 12 | Severe damage |

**Unit Conversions:**

| Function | Formula | Example |
|----------|---------|---------|
| `metersPerSecond` | identity | 10.0 -> 10.0 |
| `kilometersPerHour` | v * 3.6 | 10.0 -> 36.0 |
| `knots` | v * 1.944 | 10.0 -> 19.44 |
| `milesPerHour` | v * 2.237 | 10.0 -> 22.37 |

**Operations:**

```purescript
-- Linear interpolation
lerp :: Number -> WindSpeed -> WindSpeed -> WindSpeed

-- Dynamic pressure (Pa)
-- P = 0.5 * rho * v^2 (rho = 1.225 kg/m3)
pressureFromSpeed :: WindSpeed -> Number
```

────────────────────────────────────────────────────────────────────────────────
                                                      // wind direction // atom
────────────────────────────────────────────────────────────────────────────────

## WindDirection

Compass bearing the wind is coming FROM (meteorological convention).

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| WindDirection | Number | 0.0 | 360.0 | wraps | Degrees |

**Convention:**
- 0/360 = North (wind FROM north)
- 90 = East (wind FROM east)
- 180 = South (wind FROM south)
- 270 = West (wind FROM west)

This matches weather reports: "westerly wind" = wind from west = 270.

**Cardinal Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `directionNorth` | 0 | From north |
| `directionNorthEast` | 45 | From NE |
| `directionEast` | 90 | From east |
| `directionSouthEast` | 135 | From SE |
| `directionSouth` | 180 | From south |
| `directionSouthWest` | 225 | From SW |
| `directionWest` | 270 | From west |
| `directionNorthWest` | 315 | From NW |

**Unit Conversions:**

| Function | Formula | Example |
|----------|---------|---------|
| `degrees` | identity | 180.0 -> 180.0 |
| `radians` | d * pi / 180 | 180.0 -> 3.14159 |

## Cardinal Enum (16-Point Compass)

| Constructor | Degrees | Abbreviation |
|-------------|---------|--------------|
| `N` | 0 | N |
| `NNE` | 22.5 | NNE |
| `NE` | 45 | NE |
| `ENE` | 67.5 | ENE |
| `E` | 90 | E |
| `ESE` | 112.5 | ESE |
| `SE` | 135 | SE |
| `SSE` | 157.5 | SSE |
| `S` | 180 | S |
| `SSW` | 202.5 | SSW |
| `SW` | 225 | SW |
| `WSW` | 247.5 | WSW |
| `W` | 270 | W |
| `WNW` | 292.5 | WNW |
| `NW` | 315 | NW |
| `NNW` | 337.5 | NNW |

**Operations:**
- `cardinalToDegrees :: Cardinal -> WindDirection`
- `degreesToCardinal :: WindDirection -> Cardinal`
- `cardinalAbbreviation :: Cardinal -> String`

────────────────────────────────────────────────────────────────────────────────
                                                           // beaufort // scale
────────────────────────────────────────────────────────────────────────────────

## BeaufortNumber

The Beaufort scale (0-12) relates wind speed to observed conditions.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| BeaufortNumber | Int | 0 | 12 | clamps | Beaufort scale number |

**Complete Beaufort Scale:**

| Bft | Speed (m/s) | Description | Sea Condition | Land Condition |
|-----|-------------|-------------|---------------|----------------|
| 0 | < 0.5 | Calm | Mirror-like | Smoke rises vertically |
| 1 | 0.5-1.5 | Light air | Ripples, no crests | Smoke drifts |
| 2 | 1.6-3.3 | Light breeze | Small wavelets, glassy crests | Leaves rustle, wind felt |
| 3 | 3.4-5.4 | Gentle breeze | Large wavelets, crests break | Leaves/twigs in motion |
| 4 | 5.5-7.9 | Moderate breeze | Small waves, whitecaps | Small branches move |
| 5 | 8.0-10.7 | Fresh breeze | Moderate waves, many whitecaps | Small trees sway |
| 6 | 10.8-13.8 | Strong breeze | Large waves, white foam | Large branches move |
| 7 | 13.9-17.1 | Near gale | Sea heaps up, foam streaks | Trees in motion, hard to walk |
| 8 | 17.2-20.7 | Gale | Moderately high waves, spray | Twigs break off |
| 9 | 20.8-24.4 | Strong gale | High waves, dense foam | Slight structural damage |
| 10 | 24.5-28.4 | Storm | Very high waves, overhanging crests | Trees uprooted |
| 11 | 28.5-32.6 | Violent storm | Exceptionally high waves | Widespread damage |
| 12 | > 32.7 | Hurricane | Air filled with foam and spray | Severe/extensive damage |

**Operations:**
- `speedToBeaufort :: WindSpeed -> BeaufortNumber`
- `beaufortToMinSpeed :: BeaufortNumber -> WindSpeed`
- `beaufortDescription :: BeaufortNumber -> String`
- `beaufortSeaCondition :: BeaufortNumber -> String`
- `beaufortLandCondition :: BeaufortNumber -> String`

────────────────────────────────────────────────────────────────────────────────
                                                         // gust factor // atom
────────────────────────────────────────────────────────────────────────────────

## GustFactor

Ratio of gust speed to sustained wind speed.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| GustFactor | Number | 1.0 | 3.0 | clamps | Ratio |

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `gustNone` | 1.0 | No gusts (steady wind) |
| `gustLight` | 1.2 | Light gustiness |
| `gustModerate` | 1.4 | Moderate gustiness |
| `gustStrong` | 1.7 | Strong gusts |
| `gustSevere` | 2.2 | Severe/turbulent |

**Gust Factor Interpretation:**

| Factor | Gustiness |
|--------|-----------|
| 1.0-1.2 | Steady to light gusts |
| 1.2-1.3 | Light gustiness |
| 1.3-1.5 | Moderate gustiness |
| 1.5-2.0 | Strong gustiness |
| > 2.0 | Severe/turbulent conditions |

────────────────────────────────────────────────────────────────────────────────
                                                        // turbulence // atom
────────────────────────────────────────────────────────────────────────────────

## TurbulenceIntensity

Dimensionless measure of wind variability.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| TurbulenceIntensity | Number | 0.0 | 1.0 | clamps | Normalized |

**Presets:**

| Name | Value | Description |
|------|-------|-------------|
| `turbulenceNone` | 0.0 | Perfectly steady |
| `turbulenceLight` | 0.1 | Light turbulence |
| `turbulenceModerate` | 0.3 | Moderate |
| `turbulenceSevere` | 0.5 | Severe |
| `turbulenceExtreme` | 0.8 | Extreme |

────────────────────────────────────────────────────────────────────────────────
                                                       // wind vector // molecule
────────────────────────────────────────────────────────────────────────────────

## WindVector

Wind as a 2D vector with u (east-west) and v (north-south) components.

```purescript
data WindVector = WindVector
  { u :: Number  -- East-west component (m/s)
  , v :: Number  -- North-south component (m/s)
  }
```

**Convention:**
- u > 0: Wind blowing eastward (from west)
- v > 0: Wind blowing northward (from south)

**Operations:**

```purescript
-- Create from speed and direction
windVector :: WindSpeed -> WindDirection -> WindVector

-- Create from components
windVectorFromComponents :: Number -> Number -> WindVector

-- Extract speed (magnitude)
speedFromVector :: WindVector -> WindSpeed

-- Extract direction
directionFromVector :: WindVector -> WindDirection

-- Component accessors
uComponent :: WindVector -> Number
vComponent :: WindVector -> Number
```

────────────────────────────────────────────────────────────────────────────────
                                                       // wind event // compound
────────────────────────────────────────────────────────────────────────────────

## WindEvent

Sum type capturing wind conditions.

```purescript
data WindEvent
  = SteadyWind
      { speed :: WindSpeed
      , direction :: WindDirection
      }
  | GustyWind
      { sustained :: WindSpeed
      , direction :: WindDirection
      , gustFactor_ :: GustFactor
      , turbulence :: TurbulenceIntensity
      }
  | CalmConditions
```

**Constructors:**
- `steadyWind :: WindSpeed -> WindDirection -> WindEvent`
- `gustyWind :: WindSpeed -> WindDirection -> GustFactor -> TurbulenceIntensity -> WindEvent`
- `calmConditions :: WindEvent`

**Operations:**

```purescript
-- Wind chill temperature (Celsius)
-- NWS/Environment Canada formula:
-- T_wc = 13.12 + 0.6215*T - 11.37*v^0.16 + 0.3965*T*v^0.16
-- Valid for T <= 10C and v >= 4.8 km/h
windChill :: Number -> WindSpeed -> Number

-- Apparent temperature (heat index + wind chill combined)
apparentTemperature :: Number -> Number -> WindSpeed -> Number

-- Is wind gusty (factor > 1.3)?
isGusty :: WindEvent -> Boolean

-- Is wind calm (Beaufort 0)?
isCalm :: WindEvent -> Boolean

-- Is wind hazardous (Beaufort 8+)?
isHazardous :: WindEvent -> Boolean
```

**Wind Chill Reference:**

| Temp (C) | 10 km/h | 30 km/h | 50 km/h |
|----------|---------|---------|---------|
| 0 | -3 | -7 | -9 |
| -10 | -15 | -21 | -24 |
| -20 | -27 | -34 | -38 |
| -30 | -39 | -48 | -53 |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         // design // philosophy
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Why Weather Matters for Hydrogen

### Multi-Domain Applications

Weather primitives enable:

**Visual Rendering**
- Sky gradients (temperature + humidity -> color)
- Cloud rendering (CloudCover + AtmosphericLayer)
- Precipitation particles (DropletDiameter, SnowflakeType)
- Fog and haze (Visibility)
- Wind effects (vegetation movement, particle drift)

**Audio Design**
- Rain intensity (Rate -> audio amplitude)
- Wind ambience (BeaufortNumber -> audio profile)
- Thunder timing (tied to precipitation events)
- Sound propagation (Temperature, Humidity -> speed of sound)

**Haptic Feedback**
- Temperature sensation
- Humidity perception
- Wind resistance
- Rain/snow impact

**Simulation**
- Flight physics (density altitude, wind vectors)
- Thermal modeling (air density, heat index)
- Visibility constraints (fog, precipitation)
- Storm tracking

### Bounded by Physical Reality

Every Weather atom has bounds derived from physical observation:

- Temperature: -89.2C to +56.7C (Earth records), bounded to +/-100C
- Pressure: 300-1100 hPa (Everest to record high)
- Wind: 0-150 m/s (above any recorded gust)
- Hail: 5-150mm (graupel threshold to record size)

These bounds ensure agents cannot generate impossible weather states.

### Standard Compliance

Weather uses industry standards:

- **METAR cloud codes**: SKC, FEW, SCT, BKN, OVC
- **WMO precipitation intensity**: Light/Moderate/Heavy/Violent
- **Beaufort wind scale**: Full 0-12 with sea/land descriptions
- **ICAO Standard Atmosphere**: ISA reference conditions
- **16-point compass**: Full cardinal/intercardinal directions

This ensures interoperability with real meteorological data.

### Compositional Design

Weather follows the Hydrogen pattern:

1. **Atoms**: Temperature, Pressure, Humidity (bounded primitives)
2. **Molecules**: WindVector, SnowDensity (composed from atoms)
3. **Compounds**: AtmosphericState, PrecipitationEvent, WindEvent (complete states)

Each layer composes cleanly without escape hatches.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // formula // index
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Mathematical Formulas

### Atmospheric Physics

**Pressure Altitude**
```
h = 44330 * (1 - (P / P0)^0.1903)
```
Where P0 = 1013.25 hPa

**Density Altitude**
```
DA = PA + 120 * (T_actual - T_ISA)
T_ISA = 15 - 0.00198 * PA
```

**Speed of Sound**
```
c = 331.3 * sqrt(1 + T/273.15)
```
In m/s, T in C

**Air Density**
```
rho = P / (R * T)
```
Where R = 287.05 J/(kg*K), T in Kelvin

### Humidity Calculations

**Dew Point (Magnus-Tetens)**
```
alpha = (a * T) / (b + T) + ln(RH/100)
Td = (b * alpha) / (a - alpha)
```
Where a = 17.27, b = 237.7C

**Relative Humidity from Dew Point**
```
RH = 100 * exp(a * Td / (b + Td)) / exp(a * T / (b + T))
```

### Heat/Cold Indices

**Heat Index (Rothfusz Regression)**
```
HI = T + 0.5 * (RH - 40) / 60 * (T - 27)
```
Simplified, valid for T > 27C

**Humidex (Canadian)**
```
e = 6.11 * exp(5417.753 * (1/273.16 - 1/Td_K))
Humidex = T + (5/9) * (e - 10)
```

**Wind Chill (NWS)**
```
T_wc = 13.12 + 0.6215*T - 11.37*v^0.16 + 0.3965*T*v^0.16
```
Valid for T <= 10C, v >= 4.8 km/h

### Precipitation Physics

**Raindrop Terminal Velocity**
```
v = 4.5 * sqrt(d)
```
Where d in mm, v in m/s

**Raindrop Impact Energy**
```
E = 0.5 * m * v^2
m = (4/3) * pi * r^3 * rho_water
```

**Snow Water Equivalent**
```
SWE = depth * (density / 1000)
```

### Wind Dynamics

**Dynamic Pressure**
```
P = 0.5 * rho * v^2
```
Where rho = 1.225 kg/m3

**Vector Components**
```
u = speed * sin(direction + 180)
v = speed * cos(direction + 180)
```
The +180 converts from "FROM" to "TO" direction

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                       — Opus 4.5
                                                                       2026-03-02
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
