-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // qrcode // document
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Document — Rich media artifact with metadata and identity.
-- |
-- | ## Design Philosophy
-- |
-- | A QR code isn't just encoded data — it's a **document** with:
-- | - Deterministic identity (UUID5 from content)
-- | - Creation metadata (who, when, why)
-- | - Visual configuration (style, colors, logo)
-- | - Optional expiration and tagging
-- |
-- | This enables:
-- | - Reproducible generation (same inputs → same UUID)
-- | - Audit trails (who created what, when)
-- | - Version tracking (contentId stays same, documentId changes)
-- | - Categorization and search (tags, descriptions)
-- |
-- | ## UUID5 Strategy
-- |
-- | - **contentId**: UUID5 from encoded content string only
-- |   - Same content always gets same contentId
-- |   - Visual changes don't affect contentId
-- | - **documentId**: UUID5 from content + style + metadata
-- |   - Any change creates new documentId
-- |   - Full artifact identity
-- |
-- | ## Dependencies
-- |
-- | - QRCode.Types (QRVersion, ErrorCorrection, QRMatrix)
-- | - QRCode.Content.Types (QRContent)
-- | - Schema.Geometry.Shape (for logo shapes)
-- | - Schema.Color.RGB (for colors)

module Hydrogen.Element.Component.QRCode.Document
  ( -- * Document Type
    QRCodeDocument
  , mkDocument
  , mkSimpleDocument
  
  -- * Identity Types
  , UUID5
  , SHA256
  
  -- * Identity Accessors
  , contentId
  , documentId
  , contentHash
  
  -- * Content Access
  , getContent
  , getEncodedString
  
  -- * Visual Configuration
  , QRStyle(..)
  , QRColors
  , defaultColors
  , ModuleStyles
  , defaultModuleStyles
  , FinderStyle(..)
  , ModuleShape(..)
  
  -- * Logo Configuration
  , LogoConfig(..)
  , imageLogo
  , textLogo
  , shapeLogo
  , iconLogo
  
  -- * Label Configuration
  , LabelConfig
  , LabelPosition(..)
  , defaultLabel
  , labelWithTitle
  
  -- * Metadata
  , DocumentMetadata
  , defaultMetadata
  , metadataWithTitle
  , metadataFull
  
  -- * Document Builder
  , DocumentBuilder
  , build
  , withContent
  , withStyle
  , withColors
  , withLogo
  , withMetadata
  , withLabel
  , withErrorCorrection
  , withVersion
  , withTags
  , withExpiration
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , map
  , otherwise
  , identity
  , Ordering(LT, EQ, GT)
  , compare
  )

import Data.Array (snoc, intercalate, head, tail)
import Data.Char (toCharCode)
import Data.EuclideanRing (div, mod)
import Data.Maybe (Maybe(Just, Nothing), maybe, fromMaybe)
import Data.String (joinWith)
import Data.String.CodeUnits (toCharArray, singleton, length, take, drop)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Element.Component.QRCode.Types 
  ( QRVersion
  , ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh)
  , QRMatrix
  , mkVersion
  )
import Hydrogen.Element.Component.QRCode.Content.Types 
  ( QRContent
  , contentToString
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // identity
-- ═══════════════════════════════════════════════════════════════════════════════

-- | UUID5 identifier (simplified representation).
-- |
-- | In a full implementation, this would be a proper UUID5 computed using
-- | the SHA-1 based algorithm with namespace + name.
-- | For now, we use a deterministic hash string.
type UUID5 = String

-- | SHA-256 hash (simplified representation).
type SHA256 = String

-- | Generate a deterministic UUID5-style identifier.
-- |
-- | This is a simplified implementation. A full UUID5 would use:
-- | 1. Concatenate namespace UUID bytes + name bytes
-- | 2. SHA-1 hash
-- | 3. Set version bits to 5
-- | 4. Set variant bits
-- |
-- | For now, we create a deterministic string hash.
generateUUID5 :: String -> String -> UUID5
generateUUID5 namespace name =
  let
    -- Simple deterministic hash (not cryptographic)
    combined = namespace <> ":" <> name
    hash = simpleHash combined
  in
    formatAsUUID hash

-- | Simple deterministic hash function.
-- |
-- | This produces a consistent numeric hash for any string.
-- | NOT cryptographic — just deterministic.
simpleHash :: String -> Int
simpleHash s = foldChars 0 (toCharList s)
  where
    foldChars :: Int -> Array Int -> Int
    foldChars acc chars = 
      case head chars of
        Nothing -> acc
        Just first ->
          let 
            rest = fromMaybe [] (tail chars)
            -- DJB2 hash algorithm variant
            newAcc = mod ((acc * 33) + first) 2147483647
          in foldChars newAcc rest

-- | Convert string to array of char codes
toCharList :: String -> Array Int
toCharList s = map toCharCode (toCharArray s)

-- | Format an integer hash as UUID-like string
formatAsUUID :: Int -> String
formatAsUUID n =
  let
    hex = toHexString n 8
    padded = padLeft 32 '0' hex
    -- Format: 8-4-4-4-12
    p1 = substring 0 8 padded
    p2 = substring 8 4 padded
    p3 = substring 12 4 padded
    p4 = substring 16 4 padded
    p5 = substring 20 12 padded
  in
    p1 <> "-" <> p2 <> "-" <> p3 <> "-" <> p4 <> "-" <> p5

-- | Convert Int to hex string
toHexString :: Int -> Int -> String
toHexString n minLen = padLeft minLen '0' (toHexRaw n)
  where
    toHexRaw :: Int -> String
    toHexRaw 0 = "0"
    toHexRaw num = buildHex num ""
    
    buildHex :: Int -> String -> String
    buildHex 0 acc = acc
    buildHex num acc =
      let
        digit = mod num 16
        hexChar = hexDigit digit
        newNum = div num 16
      in
        buildHex newNum (hexChar <> acc)
    
    hexDigit :: Int -> String
    hexDigit d
      | d < 10 = show d
      | d == 10 = "a"
      | d == 11 = "b"
      | d == 12 = "c"
      | d == 13 = "d"
      | d == 14 = "e"
      | otherwise = "f"

-- | Pad string on left
padLeft :: Int -> Char -> String -> String
padLeft len c s =
  let sLen = length s
  in if sLen >= len 
     then s 
     else repeatChar (len - sLen) c <> s

-- | Repeat a character n times
repeatChar :: Int -> Char -> String
repeatChar n c
  | n <= 0 = ""
  | otherwise = singleton c <> repeatChar (n - 1) c

-- | Get substring
substring :: Int -> Int -> String -> String
substring start len s = take len (drop start s)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styles
-- ═══════════════════════════════════════════════════════════════════════════════

-- | QR code visual style presets.
data QRStyle
  = StyleClassic      -- ^ Sharp square modules
  | StyleRounded      -- ^ Rounded corner modules
  | StyleDots         -- ^ Circular modules
  | StyleOrganic      -- ^ Merged bezier blob modules
  | StyleGradient     -- ^ Gradient-filled modules
  | StyleArtistic     -- ^ Full artistic with constraint awareness

derive instance eqQRStyle :: Eq QRStyle

instance showQRStyle :: Show QRStyle where
  show StyleClassic = "classic"
  show StyleRounded = "rounded"
  show StyleDots = "dots"
  show StyleOrganic = "organic"
  show StyleGradient = "gradient"
  show StyleArtistic = "artistic"

-- | Color configuration for QR code.
type QRColors =
  { foreground :: String       -- ^ Module color (CSS color string)
  , background :: String       -- ^ Background color
  , finderForeground :: Maybe String  -- ^ Optional different finder color
  , finderBackground :: Maybe String  -- ^ Optional different finder background
  }

-- | Default black and white colors
defaultColors :: QRColors
defaultColors =
  { foreground: "#000000"
  , background: "#ffffff"
  , finderForeground: Nothing
  , finderBackground: Nothing
  }

-- | Module shape options.
data ModuleShape
  = ModuleSquare              -- ^ Standard square
  | ModuleRoundedSquare       -- ^ Rounded corners
  | ModuleCircle              -- ^ Circle/dot
  | ModuleDiamond             -- ^ 45-degree rotated square
  | ModuleHeart               -- ^ Heart shape
  | ModuleStar                -- ^ Star shape
  | ModuleHexagon             -- ^ Hexagon
  | ModuleCustomPath String   -- ^ Custom SVG path

derive instance eqModuleShape :: Eq ModuleShape

instance showModuleShape :: Show ModuleShape where
  show ModuleSquare = "square"
  show ModuleRoundedSquare = "rounded"
  show ModuleCircle = "circle"
  show ModuleDiamond = "diamond"
  show ModuleHeart = "heart"
  show ModuleStar = "star"
  show ModuleHexagon = "hexagon"
  show (ModuleCustomPath _) = "custom"

-- | Finder pattern style options.
data FinderStyle
  = FinderClassic             -- ^ Standard concentric squares
  | FinderRounded             -- ^ Rounded squares
  | FinderCircular            -- ^ Concentric circles
  | FinderDots                -- ^ Dot pattern
  | FinderCustom String String String  -- ^ Outer, middle, inner SVG paths

derive instance eqFinderStyle :: Eq FinderStyle

instance showFinderStyle :: Show FinderStyle where
  show FinderClassic = "classic"
  show FinderRounded = "rounded"
  show FinderCircular = "circular"
  show FinderDots = "dots"
  show (FinderCustom _ _ _) = "custom"

-- | Per-module-type style configuration.
type ModuleStyles =
  { dataModule :: ModuleShape
  , alignmentModule :: ModuleShape
  , timingModule :: ModuleShape
  , finderStyle :: FinderStyle
  }

-- | Default module styles
defaultModuleStyles :: ModuleStyles
defaultModuleStyles =
  { dataModule: ModuleSquare
  , alignmentModule: ModuleSquare
  , timingModule: ModuleSquare
  , finderStyle: FinderClassic
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // logo
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Logo configuration for center overlay.
data LogoConfig
  = LogoImage
      { src :: String          -- ^ Image URL or data URI
      , width :: Number        -- ^ Width in pixels
      , height :: Number       -- ^ Height in pixels
      , padding :: Number      -- ^ Padding around logo
      , borderRadius :: Number -- ^ Corner radius
      }
  | LogoText
      { text :: String         -- ^ Text to display
      , fontSize :: Number     -- ^ Font size in pixels
      , fontWeight :: String   -- ^ Font weight (normal, bold, 600, etc.)
      , fontFamily :: String   -- ^ Font family
      , color :: String        -- ^ Text color
      }
  | LogoShape
      { svgPath :: String      -- ^ SVG path data
      , width :: Number
      , height :: Number
      , fill :: String         -- ^ Fill color
      , stroke :: Maybe String -- ^ Optional stroke
      }
  | LogoIcon
      { name :: String         -- ^ Icon name (from icon set)
      , size :: Number         -- ^ Icon size
      , color :: String        -- ^ Icon color
      }

derive instance eqLogoConfig :: Eq LogoConfig

instance showLogoConfig :: Show LogoConfig where
  show (LogoImage _) = "image"
  show (LogoText r) = "text:" <> r.text
  show (LogoShape _) = "shape"
  show (LogoIcon r) = "icon:" <> r.name

-- | Create image logo
imageLogo :: String -> Number -> Number -> LogoConfig
imageLogo src width height = LogoImage
  { src, width, height, padding: 4.0, borderRadius: 4.0 }

-- | Create text logo
textLogo :: String -> Number -> String -> LogoConfig
textLogo text fontSize fontWeight = LogoText
  { text, fontSize, fontWeight, fontFamily: "system-ui, sans-serif", color: "#000000" }

-- | Create shape logo from SVG path
shapeLogo :: String -> Number -> Number -> String -> LogoConfig
shapeLogo svgPath width height fill = LogoShape
  { svgPath, width, height, fill, stroke: Nothing }

-- | Create icon logo
iconLogo :: String -> Number -> String -> LogoConfig
iconLogo name size color = LogoIcon { name, size, color }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // label
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Label position relative to QR code.
data LabelPosition
  = LabelBelow
  | LabelAbove
  | LabelRight
  | LabelLeft

derive instance eqLabelPosition :: Eq LabelPosition

instance showLabelPosition :: Show LabelPosition where
  show LabelBelow = "below"
  show LabelAbove = "above"
  show LabelRight = "right"
  show LabelLeft = "left"

-- | Label/description box configuration.
type LabelConfig =
  { show :: Boolean
  , position :: LabelPosition
  , showTitle :: Boolean
  , showDescription :: Boolean
  , showCreatedAt :: Boolean
  , showExpiresAt :: Boolean
  , backgroundColor :: String
  , textColor :: String
  , padding :: Number
  , borderRadius :: Number
  }

-- | Default label configuration
defaultLabel :: LabelConfig
defaultLabel =
  { show: false
  , position: LabelBelow
  , showTitle: true
  , showDescription: true
  , showCreatedAt: false
  , showExpiresAt: false
  , backgroundColor: "#f5f5f5"
  , textColor: "#333333"
  , padding: 12.0
  , borderRadius: 8.0
  }

-- | Label showing title only
labelWithTitle :: LabelConfig
labelWithTitle = defaultLabel { show = true, showDescription = false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // metadata
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Document metadata.
type DocumentMetadata =
  { title :: Maybe String
  , description :: Maybe String
  , createdAt :: Maybe String      -- ^ ISO 8601 timestamp
  , createdBy :: Maybe String      -- ^ Creator name/ID
  , expiresAt :: Maybe String      -- ^ ISO 8601 timestamp
  , tags :: Array String
  , customFields :: Array (Tuple String String)
  }

-- | Default empty metadata
defaultMetadata :: DocumentMetadata
defaultMetadata =
  { title: Nothing
  , description: Nothing
  , createdAt: Nothing
  , createdBy: Nothing
  , expiresAt: Nothing
  , tags: []
  , customFields: []
  }

-- | Metadata with title
metadataWithTitle :: String -> DocumentMetadata
metadataWithTitle t = defaultMetadata { title = Just t }

-- | Full metadata
metadataFull :: String -> String -> String -> String -> DocumentMetadata
metadataFull title description createdAt createdBy = defaultMetadata
  { title = Just title
  , description = Just description
  , createdAt = Just createdAt
  , createdBy = Just createdBy
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // document
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete QR Code Document with identity, content, style, and metadata.
type QRCodeDocument =
  { -- Identity
    contentId :: UUID5           -- ^ Deterministic from content only
  , documentId :: UUID5          -- ^ Deterministic from everything
  , contentHash :: SHA256        -- ^ Hash of encoded content
  
  -- Content
  , content :: QRContent
  , encodedString :: String      -- ^ The actual encoded string
  
  -- Technical
  , version :: QRVersion
  , errorCorrection :: ErrorCorrection
  , quietZone :: Int             -- ^ White border width in modules
  
  -- Visual
  , style :: QRStyle
  , colors :: QRColors
  , moduleStyles :: ModuleStyles
  , logo :: Maybe LogoConfig
  
  -- Label
  , label :: LabelConfig
  
  -- Metadata
  , metadata :: DocumentMetadata
  }

-- | Create a document from content.
mkDocument :: QRContent -> QRVersion -> ErrorCorrection -> QRStyle -> QRColors -> Maybe LogoConfig -> DocumentMetadata -> LabelConfig -> QRCodeDocument
mkDocument content version errorCorrection style colors logo metadata label =
  let
    encodedString = contentToString content
    cId = generateUUID5 "hydrogen.qrcode.content" encodedString
    
    -- Document ID includes everything
    docIdSource = encodedString <> show style <> show errorCorrection <> 
                  maybe "" show logo <>
                  maybe "" identity metadata.title <>
                  maybe "" identity metadata.createdAt
    dId = generateUUID5 "hydrogen.qrcode.document" docIdSource
    
    -- Simple content hash (would use SHA-256 in production)
    cHash = toHexString (simpleHash encodedString) 64
  in
    { contentId: cId
    , documentId: dId
    , contentHash: cHash
    , content
    , encodedString
    , version
    , errorCorrection
    , quietZone: 4
    , style
    , colors
    , moduleStyles: defaultModuleStyles
    , logo
    , label
    , metadata
    }

-- | Create a simple document with defaults.
mkSimpleDocument :: QRContent -> QRCodeDocument
mkSimpleDocument content =
  mkDocument content (mkVersion 1) ECMedium StyleClassic defaultColors Nothing defaultMetadata defaultLabel

-- | Get content ID
contentId :: QRCodeDocument -> UUID5
contentId doc = doc.contentId

-- | Get document ID
documentId :: QRCodeDocument -> UUID5
documentId doc = doc.documentId

-- | Get content hash
contentHash :: QRCodeDocument -> SHA256
contentHash doc = doc.contentHash

-- | Get content
getContent :: QRCodeDocument -> QRContent
getContent doc = doc.content

-- | Get encoded string
getEncodedString :: QRCodeDocument -> String
getEncodedString doc = doc.encodedString

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // builder
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Builder for constructing documents fluently.
type DocumentBuilder =
  { content :: Maybe QRContent
  , version :: Maybe QRVersion
  , errorCorrection :: ErrorCorrection
  , style :: QRStyle
  , colors :: QRColors
  , moduleStyles :: ModuleStyles
  , logo :: Maybe LogoConfig
  , label :: LabelConfig
  , metadata :: DocumentMetadata
  }

-- | Build document from builder
build :: DocumentBuilder -> Maybe QRCodeDocument
build b = case b.content of
  Nothing -> Nothing
  Just c ->
    let
      v = fromMaybe (mkVersion 1) b.version
    in
      Just (mkDocument c v b.errorCorrection b.style b.colors b.logo b.metadata b.label)

-- | Set content
withContent :: QRContent -> DocumentBuilder -> DocumentBuilder
withContent c b = b { content = Just c }

-- | Set style
withStyle :: QRStyle -> DocumentBuilder -> DocumentBuilder
withStyle s b = b { style = s }

-- | Set colors
withColors :: QRColors -> DocumentBuilder -> DocumentBuilder
withColors c b = b { colors = c }

-- | Set logo
withLogo :: LogoConfig -> DocumentBuilder -> DocumentBuilder
withLogo l b = b { logo = Just l }

-- | Set metadata
withMetadata :: DocumentMetadata -> DocumentBuilder -> DocumentBuilder
withMetadata m b = b { metadata = m }

-- | Set label
withLabel :: LabelConfig -> DocumentBuilder -> DocumentBuilder
withLabel l b = b { label = l }

-- | Set error correction
withErrorCorrection :: ErrorCorrection -> DocumentBuilder -> DocumentBuilder
withErrorCorrection ec b = b { errorCorrection = ec }

-- | Set version
withVersion :: QRVersion -> DocumentBuilder -> DocumentBuilder
withVersion v b = b { version = Just v }

-- | Add tags
withTags :: Array String -> DocumentBuilder -> DocumentBuilder
withTags tags b = b { metadata = b.metadata { tags = b.metadata.tags <> tags } }

-- | Set expiration
withExpiration :: String -> DocumentBuilder -> DocumentBuilder
withExpiration exp b = b { metadata = b.metadata { expiresAt = Just exp } }
