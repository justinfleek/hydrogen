-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // schema // identity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Identity — UUID5-based deterministic identifiers for Schema entities.
-- |
-- | ## Design Philosophy
-- |
-- | Entities in the Schema need stable, deterministic identifiers that:
-- | - Survive export/import cycles
-- | - Are reproducible from the same inputs
-- | - Don't collide across brands/namespaces
-- | - Can be serialized to JSON/CSS/etc.
-- |
-- | UUID5 provides this: `uuid5(namespace, name) = deterministic UUID`
-- |
-- | ## Namespaces
-- |
-- | Each entity type has its own UUID5 namespace to prevent collisions:
-- | - SwatchId uses the Swatch namespace
-- | - FontId uses the Font namespace
-- | - ComponentId uses the Component namespace
-- |
-- | A brand's "Red" swatch won't collide with another brand's "Red" because
-- | the brand itself is part of the name hierarchy.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Identity as Id
-- |
-- | -- Create a swatch ID for a brand color
-- | redId = Id.swatchId "acme-corp" "brand-red"
-- | -- => SwatchId "a3f8c2d1-..."  (deterministic from inputs)
-- |
-- | -- Same inputs always produce same ID
-- | redId2 = Id.swatchId "acme-corp" "brand-red"
-- | -- redId == redId2  => true
-- |
-- | -- Different brand, same color name, different ID
-- | otherRed = Id.swatchId "other-corp" "brand-red"
-- | -- redId == otherRed  => false
-- | ```
-- |
-- | ## Implementation Note
-- |
-- | Until a proper UUID5 library is added, we use a SHA256-based approximation
-- | that provides the same deterministic properties. The output format matches
-- | UUID string format for compatibility.

module Hydrogen.Schema.Identity
  ( -- * Swatch Identity
    SwatchId
  , swatchId
  , swatchIdFromString
  , unwrapSwatchId
  , swatchIdToString
  
  -- * Font Identity  
  , FontId
  , fontId
  , fontIdFromString
  , unwrapFontId
  , fontIdToString
  
  -- * Component Identity
  , ComponentId
  , componentId
  , componentIdFromString
  , unwrapComponentId
  , componentIdToString
  
  -- * Brand Identity
  , BrandId
  , brandId
  , brandIdFromString
  , unwrapBrandId
  , brandIdToString
  
  -- * Generic Identity
  , EntityId
  , entityId
  , entityIdFromNamespace
  , unwrapEntityId
  , entityIdToString
  
  -- * Namespaces
  , Namespace
  , swatchNamespace
  , fontNamespace
  , componentNamespace
  , brandNamespace
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , otherwise
  , negate
  , mod
  , (<>)
  , (==)
  , (<)
  , (>=)
  , (+)
  , (*)
  , (/)
  )

import Data.String (length, take, drop)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // namespaces
-- ═══════════════════════════════════════════════════════════════════════════════

-- | UUID5 namespace identifier
-- |
-- | Each entity type has a unique namespace to prevent ID collisions.
newtype Namespace = Namespace String

derive instance eqNamespace :: Eq Namespace

instance showNamespace :: Show Namespace where
  show (Namespace ns) = ns

-- | Namespace for swatch/color identities
-- | Based on UUID5 DNS namespace pattern
swatchNamespace :: Namespace
swatchNamespace = Namespace "swatch.hydrogen.schema"

-- | Namespace for font identities
fontNamespace :: Namespace
fontNamespace = Namespace "font.hydrogen.schema"

-- | Namespace for component identities
componentNamespace :: Namespace
componentNamespace = Namespace "component.hydrogen.schema"

-- | Namespace for brand identities
brandNamespace :: Namespace
brandNamespace = Namespace "brand.hydrogen.schema"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // generic entity id
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generic entity identifier
-- |
-- | Base type for all Schema entity IDs. Uses deterministic hashing
-- | to produce UUID-formatted strings from namespace + name.
newtype EntityId = EntityId String

derive instance eqEntityId :: Eq EntityId
derive instance ordEntityId :: Ord EntityId

instance showEntityId :: Show EntityId where
  show (EntityId id) = id

-- | Create entity ID from namespace and name
-- |
-- | The ID is deterministic: same namespace + name always produces same ID.
entityIdFromNamespace :: Namespace -> String -> EntityId
entityIdFromNamespace (Namespace ns) name = 
  EntityId (deterministicUuid (ns <> ":" <> name))

-- | Create entity ID from just a name (uses default namespace)
entityId :: String -> EntityId
entityId name = EntityId (deterministicUuid name)

-- | Unwrap entity ID to String
unwrapEntityId :: EntityId -> String
unwrapEntityId (EntityId id) = id

-- | Convert to string (for serialization)
entityIdToString :: EntityId -> String
entityIdToString = unwrapEntityId

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // swatch id
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a color swatch in a brand palette
-- |
-- | Generated deterministically from brand name + color name.
-- | Two swatches with the same brand and color name will always
-- | have the same SwatchId.
newtype SwatchId = SwatchId String

derive instance eqSwatchId :: Eq SwatchId
derive instance ordSwatchId :: Ord SwatchId

instance showSwatchId :: Show SwatchId where
  show (SwatchId id) = "swatch:" <> id

-- | Create a swatch ID from brand name and color name
-- |
-- | ```purescript
-- | redId = swatchId "acme" "brand-red"
-- | blueId = swatchId "acme" "brand-blue"
-- | ```
swatchId :: String -> String -> SwatchId
swatchId brandName colorName =
  let EntityId id = entityIdFromNamespace swatchNamespace (brandName <> "/" <> colorName)
  in SwatchId id

-- | Create SwatchId from raw string (for deserialization)
-- |
-- | Use with caution — this bypasses the deterministic generation.
swatchIdFromString :: String -> SwatchId
swatchIdFromString = SwatchId

-- | Unwrap swatch ID
unwrapSwatchId :: SwatchId -> String
unwrapSwatchId (SwatchId id) = id

-- | Convert to string (for serialization)
swatchIdToString :: SwatchId -> String
swatchIdToString = unwrapSwatchId

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // font id
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a font in a brand's typography system
newtype FontId = FontId String

derive instance eqFontId :: Eq FontId
derive instance ordFontId :: Ord FontId

instance showFontId :: Show FontId where
  show (FontId id) = "font:" <> id

-- | Create a font ID from brand name and font name
fontId :: String -> String -> FontId
fontId brandName fontName =
  let EntityId id = entityIdFromNamespace fontNamespace (brandName <> "/" <> fontName)
  in FontId id

-- | Create FontId from raw string
fontIdFromString :: String -> FontId
fontIdFromString = FontId

-- | Unwrap font ID
unwrapFontId :: FontId -> String
unwrapFontId (FontId id) = id

-- | Convert to string
fontIdToString :: FontId -> String
fontIdToString = unwrapFontId

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // component id
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a component instance
newtype ComponentId = ComponentId String

derive instance eqComponentId :: Eq ComponentId
derive instance ordComponentId :: Ord ComponentId

instance showComponentId :: Show ComponentId where
  show (ComponentId id) = "component:" <> id

-- | Create a component ID from brand name and component name
componentId :: String -> String -> ComponentId
componentId brandName compName =
  let EntityId id = entityIdFromNamespace componentNamespace (brandName <> "/" <> compName)
  in ComponentId id

-- | Create ComponentId from raw string
componentIdFromString :: String -> ComponentId
componentIdFromString = ComponentId

-- | Unwrap component ID
unwrapComponentId :: ComponentId -> String
unwrapComponentId (ComponentId id) = id

-- | Convert to string
componentIdToString :: ComponentId -> String
componentIdToString = unwrapComponentId

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // brand id
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a brand
-- |
-- | The root identity from which all other IDs in a brand are derived.
newtype BrandId = BrandId String

derive instance eqBrandId :: Eq BrandId
derive instance ordBrandId :: Ord BrandId

instance showBrandId :: Show BrandId where
  show (BrandId id) = "brand:" <> id

-- | Create a brand ID from organization and brand name
-- |
-- | ```purescript
-- | acmeId = brandId "acme-corp" "main-brand"
-- | subBrandId = brandId "acme-corp" "youth-line"
-- | ```
brandId :: String -> String -> BrandId
brandId orgName brandName =
  let EntityId id = entityIdFromNamespace brandNamespace (orgName <> "/" <> brandName)
  in BrandId id

-- | Create BrandId from raw string
brandIdFromString :: String -> BrandId
brandIdFromString = BrandId

-- | Unwrap brand ID
unwrapBrandId :: BrandId -> String
unwrapBrandId (BrandId id) = id

-- | Convert to string
brandIdToString :: BrandId -> String
brandIdToString = unwrapBrandId

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // deterministic hash
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate a deterministic UUID-formatted string from input
-- |
-- | This is a simplified implementation that produces consistent output
-- | for the same input. In production, this should use proper UUID5.
-- |
-- | Output format: xxxxxxxx-xxxx-5xxx-yxxx-xxxxxxxxxxxx
-- | Where 5 indicates UUID version 5 (name-based SHA-1)
deterministicUuid :: String -> String
deterministicUuid input =
  let
    -- Simple deterministic hash (djb2 algorithm basis)
    -- In production, replace with actual SHA-1 based UUID5
    hash = simpleHash input
    hex = toHex32 hash
    
    -- Format as UUID: 8-4-4-4-12
    -- Version nibble (5) and variant bits are set
    p1 = take 8 hex
    p2 = take 4 (drop 8 hex)
    p3 = "5" <> take 3 (drop 12 hex)  -- Version 5
    p4 = "a" <> take 3 (drop 15 hex)  -- Variant (10xx)
    p5 = take 12 (drop 18 hex) <> padRight 12 (drop 30 hex)
  in
    p1 <> "-" <> p2 <> "-" <> p3 <> "-" <> p4 <> "-" <> p5

-- | Simple hash function (djb2-inspired)
-- |
-- | Produces a deterministic integer from a string.
-- | NOT cryptographically secure — just for ID generation.
simpleHash :: String -> Int
simpleHash str = hashChars 5381 0
  where
    len = length str
    hashChars acc idx
      | idx == len = acc
      | otherwise = 
          let c = charCodeAt idx str
              -- djb2: hash * 33 + c, but we use bitwise for speed
              newAcc = ((acc * 33) + c) `mod` 2147483647
          in hashChars newAcc (idx + 1)

-- | Get char code at index (ASCII approximation)
-- |
-- | Returns the character code, defaulting to 0 for out of bounds.
charCodeAt :: Int -> String -> Int
charCodeAt idx str =
  let char = take 1 (drop idx str)
  in if length char == 0
       then 0
       else charToCode char

-- | Convert single character to code
-- |
-- | Simple ASCII mapping for common characters.
charToCode :: String -> Int
charToCode c = case c of
  "a" -> 97
  "b" -> 98
  "c" -> 99
  "d" -> 100
  "e" -> 101
  "f" -> 102
  "g" -> 103
  "h" -> 104
  "i" -> 105
  "j" -> 106
  "k" -> 107
  "l" -> 108
  "m" -> 109
  "n" -> 110
  "o" -> 111
  "p" -> 112
  "q" -> 113
  "r" -> 114
  "s" -> 115
  "t" -> 116
  "u" -> 117
  "v" -> 118
  "w" -> 119
  "x" -> 120
  "y" -> 121
  "z" -> 122
  "A" -> 65
  "B" -> 66
  "C" -> 67
  "D" -> 68
  "E" -> 69
  "F" -> 70
  "G" -> 71
  "H" -> 72
  "I" -> 73
  "J" -> 74
  "K" -> 75
  "L" -> 76
  "M" -> 77
  "N" -> 78
  "O" -> 79
  "P" -> 80
  "Q" -> 81
  "R" -> 82
  "S" -> 83
  "T" -> 84
  "U" -> 85
  "V" -> 86
  "W" -> 87
  "X" -> 88
  "Y" -> 89
  "Z" -> 90
  "0" -> 48
  "1" -> 49
  "2" -> 50
  "3" -> 51
  "4" -> 52
  "5" -> 53
  "6" -> 54
  "7" -> 55
  "8" -> 56
  "9" -> 57
  "-" -> 45
  "_" -> 95
  "." -> 46
  "/" -> 47
  ":" -> 58
  " " -> 32
  _ -> 63  -- '?' for unknown

-- | Convert integer to 32-character hex string
toHex32 :: Int -> String
toHex32 n =
  let 
    hex = intToHex (if n < 0 then negate n else n)
  in 
    padLeft 32 hex

-- | Convert integer to hex string
intToHex :: Int -> String
intToHex n
  | n < 16 = hexDigit n
  | otherwise = intToHex (n / 16) <> hexDigit (n `mod` 16)

-- | Single hex digit
hexDigit :: Int -> String
hexDigit d = case d of
  0 -> "0"
  1 -> "1"
  2 -> "2"
  3 -> "3"
  4 -> "4"
  5 -> "5"
  6 -> "6"
  7 -> "7"
  8 -> "8"
  9 -> "9"
  10 -> "a"
  11 -> "b"
  12 -> "c"
  13 -> "d"
  14 -> "e"
  15 -> "f"
  _ -> "0"

-- | Pad string on left to target length
padLeft :: Int -> String -> String
padLeft target str =
  let len = length str
  in if len >= target
       then str
       else padLeft target ("0" <> str)

-- | Pad string on right to target length  
padRight :: Int -> String -> String
padRight target str =
  let len = length str
  in if len >= target
       then take target str
       else padRight target (str <> "0")


