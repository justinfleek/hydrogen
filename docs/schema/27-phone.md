━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                 // 27 // phone
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Phone Pillar

International phone number handling: country codes, dial codes, formatting,
parsing, and validation per ITU-T E.164 specification.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Phone/`
- **Files**: 25 modules
- **Lines**: ~5,900 total
- **Key features**: E.164 compliance, format-as-you-type, country database,
  cursor position preservation, region-based organization

## Purpose

Phone provides bounded, deterministic primitives for:
- Country identification (ISO 3166-1 alpha-2)
- International dialing prefixes (E.164 dial codes)
- National number storage and manipulation
- Format-as-you-type with cursor tracking
- Country detection from pasted numbers
- Validation with country-specific length rules
- Complete global country database (~200 countries)

## Standards Compliance

| Standard | Description | Implementation |
|----------|-------------|----------------|
| ISO 3166-1 alpha-2 | 2-letter country codes | `CountryCode` atom |
| ITU-T E.164 | International numbering | `DialCode`, `PhoneNumber` |
| NANP | North American Numbering Plan | Shared +1 dial code |

## Architecture

```
Atom Layer:
  CountryCode    — ISO 3166-1 alpha-2 (exactly 2 uppercase letters)
  DialCode       — E.164 prefix (1-999)
  NationalNumber — Subscriber digits (max 14)
  FormatPattern  — Display template with # placeholders

Molecule Layer:
  Country        — CountryCode × DialCode × Name × Flag × Format × Example × Region

Compound Layer:
  PhoneNumber    — CountryCode × DialCode × NationalNumber
  ParseResult    — Maybe Country × NationalNumber × Confidence
  CursorResult   — Formatted string × cursor position

Engine Layer:
  Format         — Apply patterns, preserve cursor
  Parse          — Detect country from input
  Validate       — Check length rules
  Database       — Complete country lookup
```

────────────────────────────────────────────────────────────────────────────────
                                                                       // atoms
────────────────────────────────────────────────────────────────────────────────

## Atoms

Primitive bounded types for phone number components.

### CountryCode

ISO 3166-1 alpha-2 country identifier.

| Name | Type | Chars | Charset | Notes |
|------|------|-------|---------|-------|
| CountryCode | String | exactly 2 | A-Z | 676 possible values (26²) |

**Construction:**
```purescript
countryCode :: String -> Maybe CountryCode
-- Validates length = 2, all chars A-Z
-- Normalizes to uppercase

unsafeCountryCode :: String -> CountryCode
-- For known-valid codes (database constants)
```

**Common Codes:**
| Code | Country | Code | Country |
|------|---------|------|---------|
| `us` | United States | `gb` | United Kingdom |
| `ca` | Canada | `au` | Australia |
| `de` | Germany | `fr` | France |
| `jp` | Japan | `cn` | China |
| `in_` | India | `br` | Brazil |

**Accessors:**
- `toString :: CountryCode -> String` — Raw 2-letter code
- `toUpper :: CountryCode -> String` — Identity (always uppercase)

### DialCode

E.164 international dialing prefix.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| DialCode | Int | 1 | 999 | clamps | 1-3 digit prefix |

**Construction:**
```purescript
dialCode :: Int -> Maybe DialCode
-- Returns Nothing if outside 1-999 range

unsafeDialCode :: Int -> DialCode
-- Clamps to valid range
```

**Common Codes:**
| Dial Code | Countries | Notes |
|-----------|-----------|-------|
| +1 | US, Canada, Caribbean NANP | North American Numbering Plan |
| +7 | Russia, Kazakhstan | Shared CIS code |
| +20 | Egypt | First African code |
| +27 | South Africa | |
| +30-39 | Southern Europe | Greece, Netherlands, Belgium, France, Spain, etc. |
| +40-49 | Central/Western Europe | Romania, Switzerland, Austria, UK, Denmark, Sweden, Norway, Germany |
| +51-58 | South America | Peru, Mexico, Cuba, Argentina, Brazil, Chile, Colombia, Venezuela |
| +60-66 | Southeast Asia | Malaysia, Australia, Indonesia, Philippines, NZ, Singapore, Thailand |
| +81-86 | East Asia | Japan, Korea, Vietnam, China |
| +90-98 | West/South Asia | Turkey, India, Pakistan, Afghanistan, Sri Lanka, Myanmar, Iran |

**Accessors:**
- `toInt :: DialCode -> Int` — Numeric value
- `toNumber :: DialCode -> Number` — For calculations
- `toDisplayString :: DialCode -> String` — "+{code}" format
- `toE164Prefix :: DialCode -> String` — Same as display

**Presets:**
| Name | Value | Description |
|------|-------|-------------|
| `nanp` | +1 | North American Numbering Plan |
| `uk` | +44 | United Kingdom |
| `germany` | +49 | Germany |
| `france` | +33 | France |
| `japan` | +81 | Japan |
| `china` | +86 | China |
| `india` | +91 | India |
| `australia` | +61 | Australia |
| `brazil` | +55 | Brazil |
| `russia` | +7 | Russia/Kazakhstan |

### NationalNumber

National significant number (subscriber digits without country code).

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| NationalNumber | String (digits) | 0 | 14 | truncates | E.164: 15 total - 1 country code |

**Construction:**
```purescript
nationalNumber :: String -> NationalNumber
-- Filters to digits only, truncates to max 14
-- "(555) 123-4567" becomes "5551234567"

fromDigits :: Array Char -> NationalNumber
-- From character array, filters digits

empty :: NationalNumber
-- Empty string
```

**Manipulation:**
| Function | Description |
|----------|-------------|
| `appendDigit` | Add digit to end (respects max) |
| `prependDigit` | Add digit to start |
| `insertDigitAt` | Insert at index |
| `dropLast` | Remove last digit |
| `dropFirst` | Remove first digit |
| `removeDigitAt` | Remove at index |
| `takeDigits` | First n digits |
| `dropDigits` | Skip first n digits |
| `slice` | Extract range |
| `reverse` | Reverse order |
| `concat` | Join two numbers |

**Validation:**
- `isValid :: NationalNumber -> Boolean` — Has 4-14 digits
- `hasMinLength :: NationalNumber -> Boolean` — At least 4 digits
- `hasMaxLength :: NationalNumber -> Boolean` — At most 14 digits
- `isLongerThan :: NationalNumber -> NationalNumber -> Boolean`
- `isShorterThan :: NationalNumber -> NationalNumber -> Boolean`
- `hasSameLengthAs :: NationalNumber -> NationalNumber -> Boolean`

**Bounds:**
| Constant | Value | Purpose |
|----------|-------|---------|
| `maxLength` | 14 | E.164 max (15 - 1 for country) |
| `minUsableLength` | 4 | Shortest meaningful numbers |

### FormatPattern

Display pattern with digit placeholders.

| Name | Type | Placeholder | Literals | Notes |
|------|------|-------------|----------|-------|
| FormatPattern | String | `#` | Any other char | Applied during formatting |

**Construction:**
```purescript
formatPattern_ :: String -> FormatPattern
```

**Examples:**
| Pattern | Country | Result |
|---------|---------|--------|
| `(###) ###-####` | US/Canada | (555) 123-4567 |
| `## ## ## ## ##` | France | 06 12 34 56 78 |
| `##-####-####` | Japan | 90-1234-5678 |
| `### ### ###` | Australia | 412 345 678 |
| `#### ####` | Hong Kong | 5123 4567 |
| `##### #####` | India | 98765 43210 |

**Analysis:**
- `patternToString :: FormatPattern -> String` — Raw pattern
- `countFormatSlots :: FormatPattern -> Int` — Number of `#` placeholders

────────────────────────────────────────────────────────────────────────────────
                                                                       // enums
────────────────────────────────────────────────────────────────────────────────

## Enums

### Region

Geographic grouping for country organization.

```purescript
data Region
  = NorthAmerica    -- US, Canada
  | Europe          -- Western + Eastern Europe
  | Asia            -- East, Southeast, South, Central Asia
  | SouthAmerica    -- All South American nations
  | Africa          -- North, West, East, Central, Southern Africa
  | Oceania         -- Australia, NZ, Pacific Islands
  | Caribbean       -- Island nations, NANP members
  | MiddleEast      -- Western Asia, Levant, Gulf states
  | CentralAmerica  -- Mexico through Panama
```

| Variant | Display Name | Notes |
|---------|--------------|-------|
| `NorthAmerica` | "North America" | NANP zone |
| `Europe` | "Europe" | 40+ countries |
| `Asia` | "Asia" | 40+ countries |
| `SouthAmerica` | "South America" | 13 countries |
| `Africa` | "Africa" | 54 countries |
| `Oceania` | "Oceania" | 20+ countries/territories |
| `Caribbean` | "Caribbean" | 23 countries/territories |
| `MiddleEast` | "Middle East" | 19 countries |
| `CentralAmerica` | "Central America" | 8 countries |

**Functions:**
- `regionName :: Region -> String` — Display name
- `regionToInt :: Region -> Int` — Ord comparison (internal)

### Confidence

Parse result confidence level.

```purescript
data Confidence
  = High    -- E.164 format or explicit dial code match
  | Medium  -- Likely match from number format/length
  | Low     -- Ambiguous, multiple possible countries
  | None    -- Could not determine country
```

| Level | Value | When Used |
|-------|-------|-----------|
| `High` | 3 | E.164 with clear dial code |
| `Medium` | 2 | National format matching length rules |
| `Low` | 1 | Multiple countries possible |
| `None` | 0 | No country could be determined |

**Functions:**
- `confidenceToInt :: Confidence -> Int` — Numeric comparison

### ValidationError

Validation failure reasons.

```purescript
data ValidationError
  = TooShort Int Int        -- (actual, minimum)
  | TooLong Int Int         -- (actual, maximum)
  | InvalidCharacters       -- Non-digit characters
  | MissingCountry          -- No country selected
  | IncompleteNumber Int Int -- (actual, expected)
```

| Variant | Code | Message Template |
|---------|------|------------------|
| `TooShort actual min` | `TOO_SHORT` | "Phone number is too short ({actual} digits, minimum {min})" |
| `TooLong actual max` | `TOO_LONG` | "Phone number is too long ({actual} digits, maximum {max})" |
| `InvalidCharacters` | `INVALID_CHARS` | "Phone number contains invalid characters" |
| `MissingCountry` | `MISSING_COUNTRY` | "Please select a country" |
| `IncompleteNumber actual expected` | `INCOMPLETE` | "Phone number is incomplete ({actual} of {expected} digits)" |

**Functions:**
- `errorMessage :: ValidationError -> String` — Human-readable
- `errorCode :: ValidationError -> String` — Programmatic code

### ValidationResult

Validation outcome.

```purescript
data ValidationResult
  = Valid
  | Invalid (Array ValidationError)
```

**Functions:**
- `validationErrors :: ValidationResult -> Array ValidationError`
- `isValid :: ValidationResult -> Boolean`
- `isInvalid :: ValidationResult -> Boolean`

────────────────────────────────────────────────────────────────────────────────
                                                                   // molecules
────────────────────────────────────────────────────────────────────────────────

## Molecules

Composed types combining multiple atoms.

### Country

Complete phone metadata for a country or territory.

```purescript
type Country =
  { code     :: CountryCode      -- ISO 3166-1 alpha-2
  , dialCode :: DialCode         -- E.164 prefix
  , name     :: String           -- Display name
  , flag     :: String           -- Emoji flag
  , format   :: FormatPattern    -- National number format
  , example  :: String           -- Example formatted number
  , region   :: Region           -- Geographic grouping
  }
```

**Construction:**
```purescript
country 
  :: CountryCode 
  -> DialCode 
  -> String        -- name
  -> String        -- flag
  -> FormatPattern 
  -> String        -- example
  -> Region
  -> Country

mkCountry :: ... -- Alias for country
```

**Accessors:**
| Function | Returns |
|----------|---------|
| `code` | `CountryCode` |
| `dialCode` | `DialCode` |
| `name` | `String` |
| `flag` | `String` |
| `formatPattern` | `FormatPattern` |
| `exampleNumber` | `String` |

**Predicates:**
| Function | Description |
|----------|-------------|
| `hasDialCode :: Int -> Country -> Boolean` | Check dial code match |
| `matchesSearch :: String -> Country -> Boolean` | Search name/code/dial |
| `isInRegion :: Region -> Country -> Boolean` | Region membership |

**Example Country Definitions:**
```purescript
unitedStates :: Country
unitedStates = country
  (unsafeCountryCode "US")
  (unsafeDialCode 1)
  "United States"
  "🇺🇸"
  (formatPattern_ "(###) ###-####")
  "(555) 123-4567"
  NorthAmerica

japan :: Country
japan = country
  (unsafeCountryCode "JP")
  (unsafeDialCode 81)
  "Japan"
  "🇯🇵"
  (formatPattern_ "##-####-####")
  "90-1234-5678"
  Asia
```

### LengthRule

Validation length constraints.

```purescript
type LengthRule =
  { min :: Int
  , max :: Int
  }
```

**Construction:**
```purescript
lengthRule :: Int -> Int -> LengthRule
```

**Accessors:**
- `minDigits :: LengthRule -> Int`
- `maxDigits :: LengthRule -> Int`

**Default:**
```purescript
defaultLengthRule :: LengthRule
defaultLengthRule = { min: 4, max: 14 }
-- E.164 compliant: 4 minimum, 14 maximum national digits
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // compounds
────────────────────────────────────────────────────────────────────────────────

## Compounds

Complex compositions for complete phone number handling.

### PhoneNumber

Complete international phone number.

```purescript
type PhoneNumber =
  { country :: CountryCode
  , dial    :: DialCode
  , number  :: NationalNumber
  }
```

**Canonical Format:** E.164 — `+{dialCode}{nationalNumber}`

Example: `+14155551234` (US number)

**Construction:**
```purescript
phoneNumber :: CountryCode -> DialCode -> NationalNumber -> PhoneNumber

fromParts :: CountryCode -> DialCode -> String -> PhoneNumber
-- String is filtered to digits

fromE164 :: String -> Maybe PhoneNumber
-- Parse "+14155551234" format

empty :: PhoneNumber
-- US default, no digits
```

**Accessors:**
| Function | Returns |
|----------|---------|
| `countryCode` | `CountryCode` |
| `dialCode` | `DialCode` |
| `nationalNumber` | `NationalNumber` |

**Conversion:**
| Function | Description |
|----------|-------------|
| `toE164` | "+14155551234" format |
| `toDisplayParts` | `{ dialDisplay, nationalDigits }` |
| `toCountryCodeString` | "US", "GB", etc. |

**Manipulation:**
| Function | Description |
|----------|-------------|
| `setCountryCode` | Change country |
| `setDialCode` | Change dial code |
| `setNationalNumber` | Replace number |
| `appendDigit` | Add digit |
| `dropLastDigit` | Remove last digit |
| `clearNumber` | Reset to empty |

**Validation:**
| Function | Description |
|----------|-------------|
| `isEmpty` | No national digits |
| `hasNationalNumber` | At least 1 digit |
| `isComplete` | At least 7 digits (heuristic) |
| `digitCount` | Number of national digits |

**Comparison:**
| Function | Description |
|----------|-------------|
| `sameCountry` | Both have same country/dial |
| `sameNumber` | Same national number |
| `compareByCountry` | Sort by country |
| `compareByDigitCount` | Sort by length |

### ParseResult

Result of parsing a phone number string.

```purescript
type ParseResult =
  { country       :: Maybe Country
  , national      :: NationalNumber
  , confidence    :: Confidence
  , originalInput :: String
  }
```

**Construction:**
```purescript
parseResult 
  :: Maybe Country 
  -> NationalNumber 
  -> Confidence 
  -> String 
  -> ParseResult
```

**Accessors:**
- `parsedCountry :: ParseResult -> Maybe Country`
- `parsedNational :: ParseResult -> NationalNumber`
- `parseConfidence :: ParseResult -> Confidence`
- `isSuccessfulParse :: ParseResult -> Boolean` — Has country and confidence > None

### CursorResult

Formatting result with cursor position.

```purescript
type CursorResult =
  { formatted :: String
  , cursor    :: Int
  }
```

**Accessors:**
- `formattedValue :: CursorResult -> String`
- `cursorPosition :: CursorResult -> Int`

────────────────────────────────────────────────────────────────────────────────
                                                              // format // engine
────────────────────────────────────────────────────────────────────────────────

## Format Engine

Pure formatting with cursor position preservation.

### Core Formatting

```purescript
format :: Country -> NationalNumber -> String
-- Full format using country pattern

formatWithPattern :: FormatPattern -> NationalNumber -> String
-- Format with explicit pattern

formatPartial :: FormatPattern -> NationalNumber -> String
-- During typing: trims trailing literals
```

**Example:**
```purescript
format usCountry (nationalNumber "5551234567")
-- Returns: "(555) 123-4567"

formatPartial usPattern (nationalNumber "555123")
-- Returns: "(555) 123"  -- No trailing dash
```

### Cursor Handling

Critical for format-as-you-type UX.

```purescript
formatWithCursor :: FormatPattern -> NationalNumber -> Int -> CursorResult
-- Format and calculate new cursor position

calculateCursorAfterFormat :: FormatPattern -> Int -> Int
-- Map digit index to formatted position

calculateCursorAfterDelete :: FormatPattern -> String -> Int -> Int
-- Handle backspace through literals
```

**Why cursor preservation matters:**

When user types `555`, the formatted result is `(555)`. If they type `1`,
the result becomes `(555) 1`. The cursor must move from position 4 to 
position 6 (past the `) ` literal).

Without cursor tracking, the cursor would stay at position 4, breaking UX.

### Unformatting

```purescript
unformat :: String -> String
-- Strip all formatting, return digits only

extractDigits :: String -> String
-- Same as unformat
```

### Pattern Analysis

```purescript
digitPositions :: FormatPattern -> Array Int
-- Indices where digits appear: "(###) ###-####" -> [1,2,3,6,7,8,10,11,12,13]

literalPositions :: FormatPattern -> Array Int
-- Indices of non-digit characters

isDigitPosition :: FormatPattern -> Int -> Boolean
-- Check if position is a digit slot

positionToDigitIndex :: FormatPattern -> Int -> Maybe Int
-- Map formatted position to digit index

digitIndexToPosition :: FormatPattern -> Int -> Int
-- Map digit index to formatted position
```

### Pattern Utilities

```purescript
patternDigitCount :: FormatPattern -> Int
-- Number of # placeholders

findFirstDigitPosition :: FormatPattern -> Int
-- Position of first # (for initial cursor)

appendDigit :: FormatPattern -> String -> Char -> String
-- Append and reformat

formatOrDefault :: FormatPattern -> NationalNumber -> String -> String
-- Format with fallback for empty
```

────────────────────────────────────────────────────────────────────────────────
                                                               // parse // engine
────────────────────────────────────────────────────────────────────────────────

## Parse Engine

Intelligent phone number parsing and country detection.

### Parsing Functions

```purescript
parse :: Array Country -> String -> ParseResult
-- Auto-detect format and country

parseWithHint :: Array Country -> Country -> String -> ParseResult
-- Prefer hint country for ambiguous cases

parseE164 :: Array Country -> String -> ParseResult
-- Parse +{dial}{national} format

parseNational :: Array Country -> String -> ParseResult
-- Parse national format (no country code)
```

### Detection Functions

```purescript
detectCountry :: Array Country -> String -> Maybe Country
-- Find country from number

detectCountryFromDialCode :: Array Country -> String -> Maybe { country, remaining }
-- Match dial code prefix (tries 3, 2, 1 digit lengths)

detectCountryFromNumber :: Array Country -> String -> Maybe Country
-- Heuristic from number characteristics

extractDialCode :: Array Country -> String -> Maybe Int
-- Get dial code from digits

hasInternationalPrefix :: String -> Boolean
-- Starts with "+" or "00"
```

### Normalization

```purescript
normalize :: String -> String
-- Remove non-digits, handle 00 prefix
-- "00 44 7911 123456" -> "+447911123456"

stripInternationalPrefix :: String -> String
-- Remove + or 00

stripTrunkPrefix :: String -> String
-- Remove leading 0 (national dialing)
```

### Dial Code Detection Algorithm

1. Try 3-digit prefix (e.g., +852 Hong Kong)
2. If no match, try 2-digit prefix (e.g., +44 UK)
3. If no match, try 1-digit prefix (e.g., +1 NANP, +7 Russia)
4. Return first match with remaining digits as national number

This handles overlapping dial codes correctly (e.g., +1 vs +1242 Bahamas).

────────────────────────────────────────────────────────────────────────────────
                                                           // validate // engine
────────────────────────────────────────────────────────────────────────────────

## Validate Engine

Phone number validation with detailed error reporting.

### Validation Functions

```purescript
validate :: NationalNumber -> ValidationResult
-- Default rules: 4-14 digits, digits only

validateStrict :: Country -> NationalNumber -> ValidationResult
-- Exact match to country's format pattern length

validateWithCountry :: Country -> NationalNumber -> ValidationResult
-- Less strict: allows partial numbers

validateE164 :: String -> ValidationResult
-- Validate E.164 format string
```

### Individual Checks

```purescript
checkMinLength :: Int -> NationalNumber -> Maybe ValidationError
-- Returns TooShort if below minimum

checkMaxLength :: Int -> NationalNumber -> Maybe ValidationError
-- Returns TooLong if above maximum

checkDigitsOnly :: NationalNumber -> Maybe ValidationError
-- Returns InvalidCharacters if non-digits

checkCountryLength :: Country -> NationalNumber -> Maybe ValidationError
-- Returns IncompleteNumber or TooLong based on format slots
```

### E.164 Validation Rules

| Rule | Constraint |
|------|------------|
| Starts with + | Required |
| After + all digits | Required |
| Digit count | 1-15 |
| Total length | 2-16 characters |

────────────────────────────────────────────────────────────────────────────────
                                                                    // database
────────────────────────────────────────────────────────────────────────────────

## Country Database

Complete international phone metadata for ~200 countries and territories.

### Organization

```
Database
├── NorthAmerica (2 countries)
├── Europe
│   ├── Western (22 countries)
│   └── Eastern (re-exported)
├── Asia (40 countries)
│   ├── East Asia
│   ├── Southeast Asia
│   ├── South Asia
│   └── Central Asia
├── SouthAmerica (13 countries)
├── Africa
│   ├── North (6 countries)
│   ├── West (16 countries)
│   ├── East (10 countries)
│   ├── Central (8 countries)
│   └── Southern (14 countries)
├── Oceania (19 countries/territories)
│   ├── Australasia
│   ├── Melanesia
│   ├── Micronesia
│   └── Polynesia
├── Caribbean (23 countries/territories)
├── MiddleEast (19 countries)
└── CentralAmerica (8 countries)
```

### Lookup Functions

```purescript
allCountries :: Array Country
-- Complete list of all countries

countryCount :: Int
-- Total count

findByCode :: CountryCode -> Maybe Country
-- ISO 3166-1 alpha-2 lookup

findByDialCode :: Int -> Maybe Country
-- First match (note: dial codes can be shared)

findByName :: String -> Maybe Country
-- Case-insensitive partial match
```

### Filtering Functions

```purescript
countriesInRegion :: Region -> Array Country
-- All countries in a region

countriesWithDialCode :: Int -> Array Country
-- All countries sharing a dial code

searchCountries :: String -> Array Country
-- Search by name, code, or dial code
```

### Regional Modules

| Module | Export | Count |
|--------|--------|-------|
| `Database.NorthAmerica` | `northAmericanCountries` | 2 |
| `Database.Europe` | `europeanCountries` | 40+ |
| `Database.Europe.Western` | `westernEuropeanCountries` | 22 |
| `Database.Europe.Eastern` | `easternEuropeanCountries` | — |
| `Database.Asia` | `asianCountries` | 40 |
| `Database.SouthAmerica` | `southAmericanCountries` | 13 |
| `Database.Africa` | `africanCountries` | 54 |
| `Database.Africa.North` | `northAfricanCountries` | 6 |
| `Database.Africa.West` | `westAfricanCountries` | 16 |
| `Database.Africa.East` | `eastAfricanCountries` | 10 |
| `Database.Africa.Central` | `centralAfricanCountries` | 8 |
| `Database.Africa.Southern` | `southernAfricanCountries` | 14 |
| `Database.Oceania` | `oceanianCountries` | 19 |
| `Database.Caribbean` | `caribbeanCountries` | 23 |
| `Database.MiddleEast` | `middleEasternCountries` | 19 |
| `Database.CentralAmerica` | `centralAmericanCountries` | 8 |

────────────────────────────────────────────────────────────────────────────────
                                                            // country // roster
────────────────────────────────────────────────────────────────────────────────

## Country Roster (Sample)

### North American Numbering Plan (+1)

| Code | Name | Format | Example |
|------|------|--------|---------|
| US | United States | (###) ###-#### | (555) 123-4567 |
| CA | Canada | (###) ###-#### | (555) 123-4567 |
| JM | Jamaica | (###) ###-#### | (876) 123-4567 |
| BS | Bahamas | (###) ###-#### | (242) 123-4567 |
| BB | Barbados | (###) ###-#### | (246) 123-4567 |
| PR | Puerto Rico | (###) ###-#### | (787) 123-4567 |
| VI | US Virgin Islands | (###) ###-#### | (340) 123-4567 |
| GU | Guam | (###) ###-#### | (671) 123-4567 |

### Western Europe

| Code | Name | Dial | Format | Example |
|------|------|------|--------|---------|
| GB | United Kingdom | +44 | #### ### #### | 7911 123456 |
| DE | Germany | +49 | ### ####### | 151 12345678 |
| FR | France | +33 | ## ## ## ## ## | 06 12 34 56 78 |
| IT | Italy | +39 | ### ### #### | 312 345 6789 |
| ES | Spain | +34 | ### ### ### | 612 345 678 |
| NL | Netherlands | +31 | ## ######## | 06 12345678 |
| BE | Belgium | +32 | ### ## ## ## | 470 12 34 56 |
| CH | Switzerland | +41 | ## ### ## ## | 78 123 45 67 |
| AT | Austria | +43 | ### ####### | 664 1234567 |
| SE | Sweden | +46 | ##-### ## ## | 70-123 45 67 |
| NO | Norway | +47 | ### ## ### | 406 12 345 |
| DK | Denmark | +45 | ## ## ## ## | 32 12 34 56 |
| FI | Finland | +358 | ## ### #### | 41 234 5678 |
| IE | Ireland | +353 | ## ### #### | 85 123 4567 |
| PT | Portugal | +351 | ### ### ### | 912 345 678 |

### East Asia

| Code | Name | Dial | Format | Example |
|------|------|------|--------|---------|
| CN | China | +86 | ### #### #### | 131 2345 6789 |
| JP | Japan | +81 | ##-####-#### | 90-1234-5678 |
| KR | South Korea | +82 | ##-####-#### | 10-1234-5678 |
| TW | Taiwan | +886 | ### ### ### | 912 345 678 |
| HK | Hong Kong | +852 | #### #### | 5123 4567 |
| MO | Macau | +853 | #### #### | 6612 3456 |

### South/Southeast Asia

| Code | Name | Dial | Format | Example |
|------|------|------|--------|---------|
| IN | India | +91 | ##### ##### | 98765 43210 |
| PK | Pakistan | +92 | ### ####### | 300 1234567 |
| BD | Bangladesh | +880 | #### ###### | 1712 345678 |
| SG | Singapore | +65 | #### #### | 8123 4567 |
| MY | Malaysia | +60 | ##-### #### | 12-345 6789 |
| TH | Thailand | +66 | ## ### #### | 81 234 5678 |
| VN | Vietnam | +84 | ## ### ## ## | 91 234 56 78 |
| ID | Indonesia | +62 | ###-####-#### | 812-3456-7890 |
| PH | Philippines | +63 | ### ### #### | 917 123 4567 |

### Middle East

| Code | Name | Dial | Format | Example |
|------|------|------|--------|---------|
| SA | Saudi Arabia | +966 | ## ### #### | 50 123 4567 |
| AE | United Arab Emirates | +971 | ## ### #### | 50 123 4567 |
| IL | Israel | +972 | ##-###-#### | 50-123-4567 |
| TR | Turkey | +90 | ### ### ## ## | 532 123 45 67 |
| IR | Iran | +98 | ### ### #### | 912 345 6789 |
| IQ | Iraq | +964 | ### ### #### | 790 123 4567 |

### South America

| Code | Name | Dial | Format | Example |
|------|------|------|--------|---------|
| BR | Brazil | +55 | (##) #####-#### | (11) 91234-5678 |
| AR | Argentina | +54 | ## ####-#### | 11 1234-5678 |
| CO | Colombia | +57 | ### ### #### | 310 123 4567 |
| CL | Chile | +56 | # #### #### | 9 1234 5678 |
| PE | Peru | +51 | ### ### ### | 912 345 678 |
| VE | Venezuela | +58 | ###-####### | 412-1234567 |

### Africa (Sample)

| Code | Name | Dial | Format | Example |
|------|------|------|--------|---------|
| ZA | South Africa | +27 | ## ### #### | 82 123 4567 |
| EG | Egypt | +20 | ### ### #### | 100 123 4567 |
| NG | Nigeria | +234 | ### ### #### | 802 123 4567 |
| KE | Kenya | +254 | ### ### ### | 712 345 678 |
| MA | Morocco | +212 | ###-###### | 661-234567 |
| GH | Ghana | +233 | ## ### #### | 24 123 4567 |

### Oceania

| Code | Name | Dial | Format | Example |
|------|------|------|--------|---------|
| AU | Australia | +61 | ### ### ### | 412 345 678 |
| NZ | New Zealand | +64 | ## ### #### | 21 123 4567 |
| FJ | Fiji | +679 | ### #### | 912 3456 |
| PG | Papua New Guinea | +675 | ### #### | 712 3456 |

────────────────────────────────────────────────────────────────────────────────
                                                          // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Design Philosophy

### Why Not libphonenumber?

Google's libphonenumber is the industry standard, but:

1. **FFI dependency** — Requires JavaScript interop, breaks pure reasoning
2. **Massive bundle** — ~200KB+ of metadata
3. **String-based** — No type safety for phone components
4. **Mutable state** — Formatter instances with internal state
5. **Non-deterministic** — Version updates can change behavior

Hydrogen's Phone pillar provides:

1. **Pure PureScript** — No FFI, all deterministic
2. **Bounded atoms** — Every component has known limits
3. **Type safety** — CountryCode, DialCode, NationalNumber are distinct types
4. **Stateless** — All functions are pure transformations
5. **Reproducible** — Same input = same output, always

### Format Pattern Design

Format patterns use `#` as digit placeholders because:

1. **Visual clarity** — Easy to read pattern structure
2. **No regex** — Simple character iteration
3. **Predictable** — One placeholder = one digit
4. **Extensible** — Add new countries without code changes

### Cursor Preservation

Format-as-you-type requires precise cursor tracking:

```
User types:    5   5   5   1   2   3
Display:       5   55  555 (555) 1   (555) 12   (555) 123
Cursor:        1   2   3   6      7       8         9
```

The cursor must skip over `(`, `)`, ` ` literals automatically.

### E.164 as Canonical Form

All phone numbers are stored as:
- CountryCode (for routing/display)
- DialCode (for E.164 prefix)
- NationalNumber (raw digits)

Formatting is computed at display time, never stored. This ensures:
- Consistent storage across systems
- No format ambiguity
- Easy comparison (same digits = same number)

### Region Organization

Countries are grouped by region for:
- UI dropdown organization
- Efficient filtering
- Cultural/linguistic groupings
- Numbering plan similarities

────────────────────────────────────────────────────────────────────────────────
                                                               // usage // guide
────────────────────────────────────────────────────────────────────────────────

## Usage Guide

### Basic Phone Input Component

```purescript
-- State
type PhoneInputState =
  { phone :: PhoneNumber
  , countries :: Array Country
  }

-- Initialize
init :: PhoneInputState
init =
  { phone: PhoneNumber.empty
  , countries: Database.allCountries
  }

-- Handle digit input
onDigit :: Char -> PhoneInputState -> PhoneInputState
onDigit c state =
  state { phone = PhoneNumber.appendDigit c state.phone }

-- Handle country selection
onCountrySelect :: Country -> PhoneInputState -> PhoneInputState
onCountrySelect country state =
  state { phone = state.phone
    # PhoneNumber.setCountryCode (Country.code country)
    # PhoneNumber.setDialCode (Country.dialCode country)
  }

-- Render
render :: PhoneInputState -> Element
render state =
  let formatted = Format.format currentCountry state.phone.number
  in phoneInputElement formatted
```

### Paste Handling

```purescript
onPaste :: String -> PhoneInputState -> PhoneInputState
onPaste pastedText state =
  let result = Parse.parse state.countries pastedText
  in case Parse.parsedCountry result of
       Just country ->
         { phone: PhoneNumber.phoneNumber
             (Country.code country)
             (Country.dialCode country)
             (Parse.parsedNational result)
         , countries: state.countries
         }
       Nothing ->
         -- Keep current country, use pasted digits
         state { phone = PhoneNumber.setNationalNumber 
                   (Parse.parsedNational result) 
                   state.phone }
```

### Validation

```purescript
validatePhoneNumber :: Country -> PhoneNumber -> ValidationResult
validatePhoneNumber country phone =
  Validate.validateStrict country (PhoneNumber.nationalNumber phone)

-- In submit handler
onSubmit :: PhoneInputState -> Effect Unit
onSubmit state =
  case validatePhoneNumber currentCountry state.phone of
    Valid -> submitForm (PhoneNumber.toE164 state.phone)
    Invalid errors -> showErrors (map Validate.errorMessage errors)
```

────────────────────────────────────────────────────────────────────────────────
                                                                // e164 // spec
────────────────────────────────────────────────────────────────────────────────

## E.164 Specification Reference

ITU-T Recommendation E.164 defines the international numbering plan.

### Structure

```
+[Country Code][National Significant Number]
 └─ 1-3 digits  └─ variable length
```

**Total maximum: 15 digits** (not including +)

### Country Code Allocation

| Range | Allocation |
|-------|------------|
| +1 | North American Numbering Plan (NANP) |
| +20 | Egypt |
| +21x | North/West Africa |
| +22x | West Africa |
| +23x | West/Central Africa |
| +24x | Central Africa |
| +25x | East Africa |
| +26x | Southern Africa |
| +27 | South Africa |
| +28x | Unassigned |
| +29x | Atlantic Ocean islands |
| +30 | Greece |
| +31 | Netherlands |
| +32 | Belgium |
| +33 | France |
| +34 | Spain |
| +35x | Southern Europe (small states) |
| +36 | Hungary |
| +37x | Baltic/Balkans |
| +38x | Balkans |
| +39 | Italy |
| +40 | Romania |
| +41 | Switzerland |
| +42x | Central Europe |
| +43 | Austria |
| +44 | United Kingdom |
| +45 | Denmark |
| +46 | Sweden |
| +47 | Norway |
| +48 | Poland |
| +49 | Germany |
| +50x | Mexico/Central America |
| +51 | Peru |
| +52 | Mexico |
| +53 | Cuba |
| +54 | Argentina |
| +55 | Brazil |
| +56 | Chile |
| +57 | Colombia |
| +58 | Venezuela |
| +59x | Caribbean/South America |
| +60 | Malaysia |
| +61 | Australia |
| +62 | Indonesia |
| +63 | Philippines |
| +64 | New Zealand |
| +65 | Singapore |
| +66 | Thailand |
| +67x | Pacific |
| +68x | Pacific |
| +69x | Pacific |
| +7 | Russia/Kazakhstan |
| +81 | Japan |
| +82 | South Korea |
| +84 | Vietnam |
| +86 | China |
| +850-859 | North Korea/Cambodia |
| +870-879 | Satellite/Networks |
| +880-889 | Bangladesh/Taiwan |
| +90 | Turkey |
| +91 | India |
| +92 | Pakistan |
| +93 | Afghanistan |
| +94 | Sri Lanka |
| +95 | Myanmar |
| +96x | Middle East |
| +97x | Middle East/Gulf |
| +98 | Iran |
| +99x | Central Asia |

────────────────────────────────────────────────────────────────────────────────
                                                                // module // map
────────────────────────────────────────────────────────────────────────────────

## Module Map

```
Hydrogen.Schema.Phone
├── CountryCode             -- ISO 3166-1 alpha-2 atom
├── DialCode                -- E.164 prefix atom
├── NationalNumber          -- Subscriber digits atom
├── Country                 -- Country molecule + FormatPattern + Region enum
├── PhoneNumber             -- Complete phone compound
├── Format                  -- Formatting engine + CursorResult
├── Parse                   -- Parsing engine + ParseResult + Confidence
├── Validate                -- Validation engine + ValidationError/Result
└── Database                -- Complete country database
    ├── NorthAmerica
    ├── Europe
    │   ├── Western
    │   └── Eastern
    ├── Asia
    ├── SouthAmerica
    ├── Africa
    │   ├── North
    │   ├── West
    │   ├── East
    │   ├── Central
    │   └── Southern
    ├── Oceania
    ├── Caribbean
    ├── MiddleEast
    └── CentralAmerica
```

────────────────────────────────────────────────────────────────────────────────
                                                                  // references
────────────────────────────────────────────────────────────────────────────────

## References

- ITU-T E.164: The International Public Telecommunication Numbering Plan
- ISO 3166-1 alpha-2: Country codes
- NANP: North American Numbering Plan Administration
- Google libphonenumber: Reference implementation (for comparison)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
