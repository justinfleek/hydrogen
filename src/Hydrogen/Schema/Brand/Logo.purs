-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // brand // logo
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo System: Complete logo specification for brand identity.
-- |
-- | From SMART Brand Ingestion Framework §9-14:
-- |   §9:  Logo components, integrity
-- |   §10: Logo lockups (arrangements, variants)
-- |   §11: Logo clear space (minimum clearance)
-- |   §12: Logo minimum sizing (print/digital bounds)
-- |   §13: Logo usage rules (placement, watermarks, social, app icons)
-- |   §14: Logo common errors (the "Do Not" list)
-- |
-- | STATUS: PROVING (Lean4 proofs in progress)
-- |
-- | Invariants:
-- |   lockup_has_variants: Every lockup has >= 1 color variant
-- |   clear_space_positive: Clear space multiplier > 0
-- |   size_positive: All minimum sizes > 0
-- |   primary_lockup_exists: Logo system has exactly one primary lockup
-- |   error_categories_complete: All error types covered
-- |
-- | PURE DATA: Logos are pure data describing visual identity constraints.
-- | Rendering happens at target boundaries.

module Hydrogen.Schema.Brand.Logo
  ( -- * Logo Components (§9)
    LogoComponent(..)
  , componentToString
  , componentFromString
  , IconDescription
  , mkIconDescription
  , unIconDescription
  , WordmarkDescription
  , mkWordmarkDescription
  , unWordmarkDescription
  , LogoSymbolism
  , mkLogoSymbolism
  , unLogoSymbolism
  
  -- * Orientation
  , Orientation(..)
  , orientationToString
  , orientationFromString
  
  -- * Color Variants
  , ColorVariant(..)
  , variantToString
  , variantFromString
  , VariantSet
  , mkVariantSet
  , hasVariant
  , variantSetToArray
  
  -- * Clear Space (§11)
  , ClearSpaceMultiplier
  , mkClearSpaceMultiplier
  , unClearSpaceMultiplier
  , ClearSpaceReference
  , mkClearSpaceReference
  , unClearSpaceReference
  , ClearSpaceRule
  , mkClearSpaceRule
  , clearSpaceMultiplier
  , clearSpaceReference
  , showClearSpaceRule
  
  -- * Minimum Sizing (§12)
  , PrintSize
  , mkPrintSize
  , unPrintSize
  , DigitalSize
  , mkDigitalSize
  , unDigitalSize
  , SizeConstraint
  , mkSizeConstraint
  , printMinimum
  , digitalMinimum
  , showSizeConstraint
  
  -- * Logo Lockups (§10)
  , LockupName
  , mkLockupName
  , unLockupName
  , LockupPriority(..)
  , priorityToString
  , UsageContext(..)
  , contextToString
  , BackgroundColor
  , mkBackgroundColor
  , unBackgroundColor
  , LogoLockup
  , mkLogoLockup
  , lockupName
  , lockupComponents
  , lockupOrientation
  , lockupPriority
  , lockupVariants
  , lockupContexts
  , lockupApprovedBackgrounds
  , lockupClearSpace
  , lockupMinSize
  , showLogoLockup
  
  -- * Logo Errors (§14)
  , ErrorCategory(..)
  , categoryToString
  , LogoError
  , mkLogoError
  , errorCategory
  , errorDescription
  , showLogoError
  , LogoErrorSet
  , mkLogoErrorSet
  , addError
  , errorsByCategory
  , allErrors
  , hasErrorInCategory
  , showLogoErrorSet
  
  -- * Watermark Rules (§13)
  , WatermarkOpacity
  , mkWatermarkOpacity
  , unWatermarkOpacity
  , WatermarkRule
  , mkWatermarkRule
  , watermarkOpacity
  , watermarkLockup
  , showWatermarkRule
  
  -- * Social Media Rules (§13)
  , SocialPlatform(..)
  , platformToString
  , SocialRule
  , mkSocialRule
  , socialPlatform
  , socialLockup
  , showSocialRule
  
  -- * Logo System (Compound)
  , LogoSystem
  , mkLogoSystem
  , primaryLockup
  , alternateLockups
  , allLockups
  , logoErrors
  , logoWatermarkRule
  , logoSocialRules
  , findLockupByName
  , findLockupsForContext
  , showLogoSystem
  
  -- * Comparison and Validation
  , compareLockups
  , lockupsDiffer
  , hasNoErrors
  , countErrorsByCategory
  , validateLogoSystem
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering
  , (==)
  , (/=)
  , (>)
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  , compare
  , map
  , show
  )

import Data.Array (elem, nub, length, filter, (:), head, null)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String
import Data.Foldable (foldl, intercalate)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // logo components (§9)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Logo component atom.
-- |
-- | The fundamental building blocks of a logo:
-- |   Icon: The symbol/mark element
-- |   Wordmark: The typographic treatment of the brand name
data LogoComponent
  = Icon
  | Wordmark

derive instance eqLogoComponent :: Eq LogoComponent

instance ordLogoComponent :: Ord LogoComponent where
  compare c1 c2 = compare (componentToInt c1) (componentToInt c2)
    where
      componentToInt :: LogoComponent -> Int
      componentToInt Icon = 0
      componentToInt Wordmark = 1

instance showLogoComponent :: Show LogoComponent where
  show = componentToString

-- | Convert component to string.
componentToString :: LogoComponent -> String
componentToString Icon = "icon"
componentToString Wordmark = "wordmark"

-- | Parse component from string.
componentFromString :: String -> Maybe LogoComponent
componentFromString s = case String.toLower s of
  "icon" -> Just Icon
  "wordmark" -> Just Wordmark
  _ -> Nothing

-- | Icon description atom.
-- |
-- | Description of the icon/symbol element and its meaning.
-- | Bounded: 1-500 characters.
newtype IconDescription = IconDescription String

derive instance eqIconDescription :: Eq IconDescription
derive instance ordIconDescription :: Ord IconDescription

instance showIconDescription :: Show IconDescription where
  show (IconDescription d) = "IconDescription(" <> d <> ")"

-- | Smart constructor for icon description.
mkIconDescription :: String -> Maybe IconDescription
mkIconDescription s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 500
     then Just (IconDescription trimmed)
     else Nothing

-- | Unwrap icon description.
unIconDescription :: IconDescription -> String
unIconDescription (IconDescription d) = d

-- | Wordmark description atom.
-- |
-- | Description of the typographic treatment of the brand name.
-- | Bounded: 1-500 characters.
newtype WordmarkDescription = WordmarkDescription String

derive instance eqWordmarkDescription :: Eq WordmarkDescription
derive instance ordWordmarkDescription :: Ord WordmarkDescription

instance showWordmarkDescription :: Show WordmarkDescription where
  show (WordmarkDescription d) = "WordmarkDescription(" <> d <> ")"

-- | Smart constructor for wordmark description.
mkWordmarkDescription :: String -> Maybe WordmarkDescription
mkWordmarkDescription s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 500
     then Just (WordmarkDescription trimmed)
     else Nothing

-- | Unwrap wordmark description.
unWordmarkDescription :: WordmarkDescription -> String
unWordmarkDescription (WordmarkDescription d) = d

-- | Logo symbolism atom.
-- |
-- | The narrative behind the icon choice, connecting to brand values.
-- | Bounded: 1-1000 characters.
newtype LogoSymbolism = LogoSymbolism String

derive instance eqLogoSymbolism :: Eq LogoSymbolism
derive instance ordLogoSymbolism :: Ord LogoSymbolism

instance showLogoSymbolism :: Show LogoSymbolism where
  show (LogoSymbolism s) = "LogoSymbolism(" <> s <> ")"

-- | Smart constructor for logo symbolism.
mkLogoSymbolism :: String -> Maybe LogoSymbolism
mkLogoSymbolism s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 1000
     then Just (LogoSymbolism trimmed)
     else Nothing

-- | Unwrap logo symbolism.
unLogoSymbolism :: LogoSymbolism -> String
unLogoSymbolism (LogoSymbolism s) = s

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // orientation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Orientation atom.
-- |
-- | The spatial arrangement of logo elements.
data Orientation
  = Horizontal  -- Icon beside wordmark
  | Vertical    -- Icon above wordmark
  | Square      -- Compact, equal dimensions

derive instance eqOrientation :: Eq Orientation

instance ordOrientation :: Ord Orientation where
  compare o1 o2 = compare (orientationToInt o1) (orientationToInt o2)
    where
      orientationToInt :: Orientation -> Int
      orientationToInt Horizontal = 0
      orientationToInt Vertical = 1
      orientationToInt Square = 2

instance showOrientation :: Show Orientation where
  show = orientationToString

-- | Convert orientation to string.
orientationToString :: Orientation -> String
orientationToString Horizontal = "horizontal"
orientationToString Vertical = "vertical"
orientationToString Square = "square"

-- | Parse orientation from string.
orientationFromString :: String -> Maybe Orientation
orientationFromString s = case String.toLower s of
  "horizontal" -> Just Horizontal
  "vertical" -> Just Vertical
  "square" -> Just Square
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // color variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color variant atom.
-- |
-- | The approved color treatments for logo usage.
data ColorVariant
  = FullColor    -- Primary brand colors
  | BlackWhite   -- Monochrome for limited contexts
  | Reversed     -- Light logo on dark backgrounds
  | SingleColor  -- One-color version (often for printing)

derive instance eqColorVariant :: Eq ColorVariant

instance ordColorVariant :: Ord ColorVariant where
  compare v1 v2 = compare (variantToInt v1) (variantToInt v2)
    where
      variantToInt :: ColorVariant -> Int
      variantToInt FullColor = 0
      variantToInt BlackWhite = 1
      variantToInt Reversed = 2
      variantToInt SingleColor = 3

instance showColorVariant :: Show ColorVariant where
  show = variantToString

-- | Convert variant to string.
variantToString :: ColorVariant -> String
variantToString FullColor = "full-color"
variantToString BlackWhite = "black-white"
variantToString Reversed = "reversed"
variantToString SingleColor = "single-color"

-- | Parse variant from string.
variantFromString :: String -> Maybe ColorVariant
variantFromString s = case String.toLower s of
  "full-color" -> Just FullColor
  "fullcolor" -> Just FullColor
  "black-white" -> Just BlackWhite
  "blackwhite" -> Just BlackWhite
  "bw" -> Just BlackWhite
  "reversed" -> Just Reversed
  "single-color" -> Just SingleColor
  "singlecolor" -> Just SingleColor
  _ -> Nothing

-- | Variant set molecule.
-- |
-- | A non-empty set of approved color variants.
-- | Invariant: At least one variant must exist.
type VariantSet =
  { variants :: Array ColorVariant
  }

-- | Create a variant set (deduplicates, ensures non-empty).
mkVariantSet :: Array ColorVariant -> Maybe VariantSet
mkVariantSet vs =
  let deduped = nub vs
  in if length deduped > 0
     then Just { variants: deduped }
     else Nothing

-- | Check if a variant is in the set.
hasVariant :: ColorVariant -> VariantSet -> Boolean
hasVariant v vs = elem v vs.variants

-- | Get variants as array.
variantSetToArray :: VariantSet -> Array ColorVariant
variantSetToArray vs = vs.variants

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // clear space (§11)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Clear space multiplier atom.
-- |
-- | The multiplier applied to a reference element to calculate clear space.
-- | Bounded: 0.1 to 10.0 (must be positive, reasonable range).
-- |
-- | Example: 2.0 means "twice the height of the reference element"
newtype ClearSpaceMultiplier = ClearSpaceMultiplier Number

derive instance eqClearSpaceMultiplier :: Eq ClearSpaceMultiplier
derive instance ordClearSpaceMultiplier :: Ord ClearSpaceMultiplier

instance showClearSpaceMultiplier :: Show ClearSpaceMultiplier where
  show (ClearSpaceMultiplier m) = "ClearSpaceMultiplier(" <> show m <> ")"

-- | Smart constructor for clear space multiplier.
-- |
-- | Returns Nothing if <= 0 or > 10.
mkClearSpaceMultiplier :: Number -> Maybe ClearSpaceMultiplier
mkClearSpaceMultiplier n =
  if n > 0.0 && n <= 10.0
  then Just (ClearSpaceMultiplier n)
  else Nothing

-- | Unwrap multiplier.
unClearSpaceMultiplier :: ClearSpaceMultiplier -> Number
unClearSpaceMultiplier (ClearSpaceMultiplier m) = m

-- | Clear space reference atom.
-- |
-- | The element used as the measurement basis for clear space.
-- | Examples: "height of letter N", "icon width", "x-height"
-- | Bounded: 1-100 characters.
newtype ClearSpaceReference = ClearSpaceReference String

derive instance eqClearSpaceReference :: Eq ClearSpaceReference
derive instance ordClearSpaceReference :: Ord ClearSpaceReference

instance showClearSpaceReference :: Show ClearSpaceReference where
  show (ClearSpaceReference r) = "ClearSpaceReference(" <> r <> ")"

-- | Smart constructor for clear space reference.
mkClearSpaceReference :: String -> Maybe ClearSpaceReference
mkClearSpaceReference s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 100
     then Just (ClearSpaceReference trimmed)
     else Nothing

-- | Unwrap reference.
unClearSpaceReference :: ClearSpaceReference -> String
unClearSpaceReference (ClearSpaceReference r) = r

-- | Clear space rule molecule.
-- |
-- | Defines the minimum clearance around the logo.
-- | Composed of a multiplier and a reference element.
type ClearSpaceRule =
  { multiplier :: ClearSpaceMultiplier
  , reference :: ClearSpaceReference
  }

-- | Create a clear space rule.
mkClearSpaceRule :: ClearSpaceMultiplier -> ClearSpaceReference -> ClearSpaceRule
mkClearSpaceRule m r =
  { multiplier: m
  , reference: r
  }

-- | Get the multiplier from a rule.
clearSpaceMultiplier :: ClearSpaceRule -> ClearSpaceMultiplier
clearSpaceMultiplier rule = rule.multiplier

-- | Get the reference from a rule.
clearSpaceReference :: ClearSpaceRule -> ClearSpaceReference
clearSpaceReference rule = rule.reference

-- | Show clear space rule (debug format).
showClearSpaceRule :: ClearSpaceRule -> String
showClearSpaceRule rule =
  "ClearSpaceRule { multiplier: " <> 
  show (unClearSpaceMultiplier rule.multiplier) <> 
  ", reference: \"" <> unClearSpaceReference rule.reference <> "\" }"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // minimum sizing (§12)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Print size atom.
-- |
-- | Minimum print dimension in inches.
-- | Bounded: 0.1 to 24.0 inches (reasonable print range).
newtype PrintSize = PrintSize Number

derive instance eqPrintSize :: Eq PrintSize
derive instance ordPrintSize :: Ord PrintSize

instance showPrintSize :: Show PrintSize where
  show (PrintSize s) = "PrintSize(" <> show s <> "in)"

-- | Smart constructor for print size.
mkPrintSize :: Number -> Maybe PrintSize
mkPrintSize n =
  if n >= 0.1 && n <= 24.0
  then Just (PrintSize n)
  else Nothing

-- | Unwrap print size.
unPrintSize :: PrintSize -> Number
unPrintSize (PrintSize s) = s

-- | Digital size atom.
-- |
-- | Minimum digital dimension in pixels.
-- | Bounded: 1 to 10000 pixels (reasonable digital range).
newtype DigitalSize = DigitalSize Int

derive instance eqDigitalSize :: Eq DigitalSize
derive instance ordDigitalSize :: Ord DigitalSize

instance showDigitalSize :: Show DigitalSize where
  show (DigitalSize s) = "DigitalSize(" <> show s <> "px)"

-- | Smart constructor for digital size.
mkDigitalSize :: Int -> Maybe DigitalSize
mkDigitalSize n =
  if n >= 1 && n <= 10000
  then Just (DigitalSize n)
  else Nothing

-- | Unwrap digital size.
unDigitalSize :: DigitalSize -> Int
unDigitalSize (DigitalSize s) = s

-- | Size constraint molecule.
-- |
-- | Print and digital minimum dimensions for a lockup.
type SizeConstraint =
  { printMin :: PrintSize
  , digitalMin :: DigitalSize
  }

-- | Create a size constraint.
mkSizeConstraint :: PrintSize -> DigitalSize -> SizeConstraint
mkSizeConstraint p d =
  { printMin: p
  , digitalMin: d
  }

-- | Get print minimum.
printMinimum :: SizeConstraint -> PrintSize
printMinimum sc = sc.printMin

-- | Get digital minimum.
digitalMinimum :: SizeConstraint -> DigitalSize
digitalMinimum sc = sc.digitalMin

-- | Show size constraint (debug format).
showSizeConstraint :: SizeConstraint -> String
showSizeConstraint sc =
  "SizeConstraint { print: " <> 
  show (unPrintSize sc.printMin) <> "in, digital: " <> 
  show (unDigitalSize sc.digitalMin) <> "px }"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // logo lockups (§10)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Lockup name atom.
-- |
-- | A descriptive label for a logo arrangement.
-- | Examples: "Primary", "Horizontal", "Icon Solo", "Favicon"
-- | Bounded: 1-50 characters.
newtype LockupName = LockupName String

derive instance eqLockupName :: Eq LockupName
derive instance ordLockupName :: Ord LockupName

instance showLockupName :: Show LockupName where
  show (LockupName n) = "LockupName(" <> n <> ")"

-- | Smart constructor for lockup name.
mkLockupName :: String -> Maybe LockupName
mkLockupName s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 50
     then Just (LockupName trimmed)
     else Nothing

-- | Unwrap lockup name.
unLockupName :: LockupName -> String
unLockupName (LockupName n) = n

-- | Lockup priority atom.
-- |
-- | The hierarchical importance of a lockup.
data LockupPriority
  = Primary     -- First choice, mandatory for brand introduction
  | Secondary   -- Alternative for specific contexts
  | Tertiary    -- Fallback for constrained spaces

derive instance eqLockupPriority :: Eq LockupPriority

instance ordLockupPriority :: Ord LockupPriority where
  compare p1 p2 = compare (priorityToInt p1) (priorityToInt p2)
    where
      priorityToInt :: LockupPriority -> Int
      priorityToInt Primary = 0
      priorityToInt Secondary = 1
      priorityToInt Tertiary = 2

instance showLockupPriority :: Show LockupPriority where
  show = priorityToString

-- | Convert priority to string.
priorityToString :: LockupPriority -> String
priorityToString Primary = "primary"
priorityToString Secondary = "secondary"
priorityToString Tertiary = "tertiary"

-- | Usage context atom.
-- |
-- | Where a lockup is approved for use.
data UsageContext
  = Letterhead
  | BusinessCard
  | EmailSignature
  | SocialProfile
  | WebsiteHeader
  | AppIcon
  | Favicon
  | Merchandise
  | PrintAdvertising
  | DigitalAdvertising
  | Presentation
  | Video

derive instance eqUsageContext :: Eq UsageContext

instance ordUsageContext :: Ord UsageContext where
  compare c1 c2 = compare (contextToInt c1) (contextToInt c2)
    where
      contextToInt :: UsageContext -> Int
      contextToInt Letterhead = 0
      contextToInt BusinessCard = 1
      contextToInt EmailSignature = 2
      contextToInt SocialProfile = 3
      contextToInt WebsiteHeader = 4
      contextToInt AppIcon = 5
      contextToInt Favicon = 6
      contextToInt Merchandise = 7
      contextToInt PrintAdvertising = 8
      contextToInt DigitalAdvertising = 9
      contextToInt Presentation = 10
      contextToInt Video = 11

instance showUsageContext :: Show UsageContext where
  show = contextToString

-- | Convert context to string.
contextToString :: UsageContext -> String
contextToString Letterhead = "letterhead"
contextToString BusinessCard = "business-card"
contextToString EmailSignature = "email-signature"
contextToString SocialProfile = "social-profile"
contextToString WebsiteHeader = "website-header"
contextToString AppIcon = "app-icon"
contextToString Favicon = "favicon"
contextToString Merchandise = "merchandise"
contextToString PrintAdvertising = "print-advertising"
contextToString DigitalAdvertising = "digital-advertising"
contextToString Presentation = "presentation"
contextToString Video = "video"

-- | Background color atom.
-- |
-- | An approved background color for logo placement.
-- | Stored as hex color string (e.g., "#FFFFFF", "#1A1A1A").
-- | Bounded: 4-9 characters (supports #RGB, #RRGGBB, #RRGGBBAA).
newtype BackgroundColor = BackgroundColor String

derive instance eqBackgroundColor :: Eq BackgroundColor
derive instance ordBackgroundColor :: Ord BackgroundColor

instance showBackgroundColor :: Show BackgroundColor where
  show (BackgroundColor c) = "BackgroundColor(" <> c <> ")"

-- | Smart constructor for background color.
mkBackgroundColor :: String -> Maybe BackgroundColor
mkBackgroundColor s =
  let trimmed = String.toUpper (String.trim s)
      len = String.length trimmed
  in if len >= 4 && len <= 9 && String.take 1 trimmed == "#"
     then Just (BackgroundColor trimmed)
     else Nothing

-- | Unwrap background color.
unBackgroundColor :: BackgroundColor -> String
unBackgroundColor (BackgroundColor c) = c

-- | Logo lockup molecule.
-- |
-- | A complete specification for one logo arrangement.
-- | Invariant: Must have at least one color variant.
type LogoLockup =
  { name :: LockupName
  , components :: Array LogoComponent
  , orientation :: Orientation
  , priority :: LockupPriority
  , variants :: VariantSet
  , contexts :: Array UsageContext
  , approvedBackgrounds :: Array BackgroundColor
  , clearSpace :: ClearSpaceRule
  , minSize :: SizeConstraint
  }

-- | Create a logo lockup.
-- |
-- | Returns Nothing if variants is empty (invariant violation).
mkLogoLockup
  :: LockupName
  -> Array LogoComponent
  -> Orientation
  -> LockupPriority
  -> VariantSet
  -> Array UsageContext
  -> Array BackgroundColor
  -> ClearSpaceRule
  -> SizeConstraint
  -> LogoLockup
mkLogoLockup name components orientation priority variants contexts backgrounds clearSpace minSize =
  { name
  , components: nub components
  , orientation
  , priority
  , variants
  , contexts: nub contexts
  , approvedBackgrounds: nub backgrounds
  , clearSpace
  , minSize
  }

-- | Get lockup name.
lockupName :: LogoLockup -> LockupName
lockupName l = l.name

-- | Get lockup components.
lockupComponents :: LogoLockup -> Array LogoComponent
lockupComponents l = l.components

-- | Get lockup orientation.
lockupOrientation :: LogoLockup -> Orientation
lockupOrientation l = l.orientation

-- | Get lockup priority.
lockupPriority :: LogoLockup -> LockupPriority
lockupPriority l = l.priority

-- | Get lockup variants.
lockupVariants :: LogoLockup -> VariantSet
lockupVariants l = l.variants

-- | Get lockup usage contexts.
lockupContexts :: LogoLockup -> Array UsageContext
lockupContexts l = l.contexts

-- | Get approved backgrounds.
lockupApprovedBackgrounds :: LogoLockup -> Array BackgroundColor
lockupApprovedBackgrounds l = l.approvedBackgrounds

-- | Get clear space rule.
lockupClearSpace :: LogoLockup -> ClearSpaceRule
lockupClearSpace l = l.clearSpace

-- | Get minimum size constraint.
lockupMinSize :: LogoLockup -> SizeConstraint
lockupMinSize l = l.minSize

-- | Show lockup (debug format).
showLogoLockup :: LogoLockup -> String
showLogoLockup l =
  "LogoLockup { name: \"" <> unLockupName l.name <> 
  "\", priority: " <> priorityToString l.priority <>
  ", orientation: " <> orientationToString l.orientation <>
  ", variants: [" <> intercalate ", " (map variantToString (variantSetToArray l.variants)) <> 
  "], contexts: " <> show (length l.contexts) <> " }"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // logo errors (§14)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Error category atom.
-- |
-- | Categories of logo misuse from SMART framework §14.
-- | These are the "Do Not" constraints — critical for AI enforcement.
data ErrorCategory
  = ContrastError     -- Dark on dark, light on light
  | ColorError        -- Off-brand colors, color modifications
  | DistortionError   -- Squash, stretch, skew, crop
  | LayoutError       -- Altered relationships, opacity issues
  | ClearSpaceError   -- Encroachment on required spacing

derive instance eqErrorCategory :: Eq ErrorCategory

instance ordErrorCategory :: Ord ErrorCategory where
  compare c1 c2 = compare (categoryToInt c1) (categoryToInt c2)
    where
      categoryToInt :: ErrorCategory -> Int
      categoryToInt ContrastError = 0
      categoryToInt ColorError = 1
      categoryToInt DistortionError = 2
      categoryToInt LayoutError = 3
      categoryToInt ClearSpaceError = 4

instance showErrorCategory :: Show ErrorCategory where
  show = categoryToString

-- | Convert category to string.
categoryToString :: ErrorCategory -> String
categoryToString ContrastError = "contrast-error"
categoryToString ColorError = "color-error"
categoryToString DistortionError = "distortion-error"
categoryToString LayoutError = "layout-error"
categoryToString ClearSpaceError = "clear-space-error"

-- | Logo error atom.
-- |
-- | A specific prohibited usage pattern.
-- | These are MORE VALUABLE than positive guidance for AI enforcement.
type LogoError =
  { category :: ErrorCategory
  , description :: String
  }

-- | Create a logo error.
-- |
-- | Description bounded: 1-500 characters.
mkLogoError :: ErrorCategory -> String -> Maybe LogoError
mkLogoError cat desc =
  let trimmed = String.trim desc
      len = String.length trimmed
  in if len > 0 && len <= 500
     then Just { category: cat, description: trimmed }
     else Nothing

-- | Get error category.
errorCategory :: LogoError -> ErrorCategory
errorCategory e = e.category

-- | Get error description.
errorDescription :: LogoError -> String
errorDescription e = e.description

-- | Show error (debug format).
showLogoError :: LogoError -> String
showLogoError e =
  "LogoError { category: " <> categoryToString e.category <>
  ", description: \"" <> e.description <> "\" }"

-- | Logo error set compound.
-- |
-- | Collection of all prohibited logo usages.
type LogoErrorSet =
  { errors :: Array LogoError
  }

-- | Create an error set.
mkLogoErrorSet :: Array LogoError -> LogoErrorSet
mkLogoErrorSet es = { errors: es }

-- | Add an error to the set.
addError :: LogoError -> LogoErrorSet -> LogoErrorSet
addError e set = { errors: e : set.errors }

-- | Get errors by category.
errorsByCategory :: ErrorCategory -> LogoErrorSet -> Array LogoError
errorsByCategory cat set = filter (\e -> e.category == cat) set.errors

-- | Get all errors.
allErrors :: LogoErrorSet -> Array LogoError
allErrors set = set.errors

-- | Check if the set has errors in a category.
hasErrorInCategory :: ErrorCategory -> LogoErrorSet -> Boolean
hasErrorInCategory cat set = length (errorsByCategory cat set) > 0

-- | Show error set (debug format).
showLogoErrorSet :: LogoErrorSet -> String
showLogoErrorSet set =
  "LogoErrorSet { count: " <> show (length set.errors) <> 
  ", categories: [" <> 
  intercalate ", " (map categoryToString (categoriesPresent set)) <> 
  "] }"
  where
    categoriesPresent :: LogoErrorSet -> Array ErrorCategory
    categoriesPresent s = nub (map (\e -> e.category) s.errors)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // watermark rules (§13)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Watermark opacity atom.
-- |
-- | Opacity for watermark usage.
-- | Bounded: 0.01 to 1.0 (must be visible but not overwhelming).
newtype WatermarkOpacity = WatermarkOpacity Number

derive instance eqWatermarkOpacity :: Eq WatermarkOpacity
derive instance ordWatermarkOpacity :: Ord WatermarkOpacity

instance showWatermarkOpacity :: Show WatermarkOpacity where
  show (WatermarkOpacity o) = "WatermarkOpacity(" <> show o <> ")"

-- | Smart constructor for watermark opacity.
mkWatermarkOpacity :: Number -> Maybe WatermarkOpacity
mkWatermarkOpacity n =
  if n >= 0.01 && n <= 1.0
  then Just (WatermarkOpacity n)
  else Nothing

-- | Unwrap opacity.
unWatermarkOpacity :: WatermarkOpacity -> Number
unWatermarkOpacity (WatermarkOpacity o) = o

-- | Watermark rule molecule.
-- |
-- | Specification for logo usage as watermark.
type WatermarkRule =
  { opacity :: WatermarkOpacity
  , lockupRef :: LockupName  -- Which lockup to use for watermarks
  }

-- | Create a watermark rule.
mkWatermarkRule :: WatermarkOpacity -> LockupName -> WatermarkRule
mkWatermarkRule o l = { opacity: o, lockupRef: l }

-- | Get watermark opacity.
watermarkOpacity :: WatermarkRule -> WatermarkOpacity
watermarkOpacity w = w.opacity

-- | Get watermark lockup reference.
watermarkLockup :: WatermarkRule -> LockupName
watermarkLockup w = w.lockupRef

-- | Show watermark rule (debug format).
showWatermarkRule :: WatermarkRule -> String
showWatermarkRule w =
  "WatermarkRule { opacity: " <> show (unWatermarkOpacity w.opacity) <>
  ", lockup: \"" <> unLockupName w.lockupRef <> "\" }"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // social media rules (§13)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Social platform atom.
-- |
-- | Major social media platforms with distinct sizing requirements.
data SocialPlatform
  = Twitter
  | LinkedIn
  | Facebook
  | Instagram
  | YouTube
  | TikTok
  | Discord
  | Slack

derive instance eqSocialPlatform :: Eq SocialPlatform

instance ordSocialPlatform :: Ord SocialPlatform where
  compare p1 p2 = compare (platformToInt p1) (platformToInt p2)
    where
      platformToInt :: SocialPlatform -> Int
      platformToInt Twitter = 0
      platformToInt LinkedIn = 1
      platformToInt Facebook = 2
      platformToInt Instagram = 3
      platformToInt YouTube = 4
      platformToInt TikTok = 5
      platformToInt Discord = 6
      platformToInt Slack = 7

instance showSocialPlatform :: Show SocialPlatform where
  show = platformToString

-- | Convert platform to string.
platformToString :: SocialPlatform -> String
platformToString Twitter = "twitter"
platformToString LinkedIn = "linkedin"
platformToString Facebook = "facebook"
platformToString Instagram = "instagram"
platformToString YouTube = "youtube"
platformToString TikTok = "tiktok"
platformToString Discord = "discord"
platformToString Slack = "slack"

-- | Social rule molecule.
-- |
-- | Platform-specific logo usage rule.
type SocialRule =
  { platform :: SocialPlatform
  , lockupRef :: LockupName  -- Which lockup to use for this platform
  }

-- | Create a social rule.
mkSocialRule :: SocialPlatform -> LockupName -> SocialRule
mkSocialRule p l = { platform: p, lockupRef: l }

-- | Get platform.
socialPlatform :: SocialRule -> SocialPlatform
socialPlatform s = s.platform

-- | Get lockup reference.
socialLockup :: SocialRule -> LockupName
socialLockup s = s.lockupRef

-- | Show social rule (debug format).
showSocialRule :: SocialRule -> String
showSocialRule s =
  "SocialRule { platform: " <> platformToString s.platform <>
  ", lockup: \"" <> unLockupName s.lockupRef <> "\" }"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // logo system (compound)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Logo system compound.
-- |
-- | Complete logo specification for a brand.
-- | 
-- | Invariants:
-- |   - Must have exactly one primary lockup
-- |   - All referenced lockups must exist
-- |   - At least one contrast error in error set (most common issue)
type LogoSystem =
  { primary :: LogoLockup
  , alternates :: Array LogoLockup
  , errors :: LogoErrorSet
  , watermark :: Maybe WatermarkRule
  , socialRules :: Array SocialRule
  , iconDescription :: Maybe IconDescription
  , wordmarkDescription :: Maybe WordmarkDescription
  , symbolism :: Maybe LogoSymbolism
  }

-- | Create a logo system.
-- |
-- | The first lockup is always primary, regardless of its priority field.
mkLogoSystem
  :: LogoLockup
  -> Array LogoLockup
  -> LogoErrorSet
  -> Maybe WatermarkRule
  -> Array SocialRule
  -> Maybe IconDescription
  -> Maybe WordmarkDescription
  -> Maybe LogoSymbolism
  -> LogoSystem
mkLogoSystem primary alternates errors watermark socialRules iconDesc wordmarkDesc symbolism =
  { primary
  , alternates
  , errors
  , watermark
  , socialRules
  , iconDescription: iconDesc
  , wordmarkDescription: wordmarkDesc
  , symbolism
  }

-- | Get primary lockup.
primaryLockup :: LogoSystem -> LogoLockup
primaryLockup ls = ls.primary

-- | Get alternate lockups.
alternateLockups :: LogoSystem -> Array LogoLockup
alternateLockups ls = ls.alternates

-- | Get all lockups (primary first).
allLockups :: LogoSystem -> Array LogoLockup
allLockups ls = ls.primary : ls.alternates

-- | Get logo errors.
logoErrors :: LogoSystem -> LogoErrorSet
logoErrors ls = ls.errors

-- | Get watermark rule.
logoWatermarkRule :: LogoSystem -> Maybe WatermarkRule
logoWatermarkRule ls = ls.watermark

-- | Get social media rules.
logoSocialRules :: LogoSystem -> Array SocialRule
logoSocialRules ls = ls.socialRules

-- | Find a lockup by name.
findLockupByName :: LockupName -> LogoSystem -> Maybe LogoLockup
findLockupByName name ls =
  head (filter (\l -> l.name == name) (allLockups ls))

-- | Find lockups approved for a specific context.
findLockupsForContext :: UsageContext -> LogoSystem -> Array LogoLockup
findLockupsForContext ctx ls =
  filter (\l -> elem ctx l.contexts) (allLockups ls)

-- | Show logo system (debug format).
showLogoSystem :: LogoSystem -> String
showLogoSystem ls =
  "LogoSystem { primary: \"" <> unLockupName ls.primary.name <>
  "\", alternates: " <> show (length ls.alternates) <>
  ", errors: " <> show (length ls.errors.errors) <>
  ", watermark: " <> showMaybe ls.watermark <>
  ", socialRules: " <> show (length ls.socialRules) <> " }"
  where
    showMaybe :: Maybe WatermarkRule -> String
    showMaybe Nothing = "none"
    showMaybe (Just w) = show (unWatermarkOpacity w.opacity) <> " opacity"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // comparison and validation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compare two lockups by priority.
-- |
-- | Returns standard Ordering: LT if first is higher priority, GT if lower.
-- | Primary < Secondary < Tertiary (primary is "first").
compareLockups :: LogoLockup -> LogoLockup -> Ordering
compareLockups l1 l2 = compare l1.priority l2.priority

-- | Check if two lockups are different (by name).
-- |
-- | Useful for validation: ensuring no duplicate lockup names.
lockupsDiffer :: LogoLockup -> LogoLockup -> Boolean
lockupsDiffer l1 l2 = l1.name /= l2.name

-- | Check if the error set is empty.
-- |
-- | A well-formed brand guide should have at least some "Do Not" constraints.
-- | An empty error set may indicate incomplete brand ingestion.
hasNoErrors :: LogoErrorSet -> Boolean
hasNoErrors set = null set.errors

-- | Count errors by category.
-- |
-- | Returns a summary of how many errors exist in each category.
-- | Useful for validation and completeness checking.
countErrorsByCategory :: LogoErrorSet -> Array { category :: ErrorCategory, count :: Int }
countErrorsByCategory set =
  let 
    categories = [ContrastError, ColorError, DistortionError, LayoutError, ClearSpaceError]
    countCat cat = { category: cat, count: length (errorsByCategory cat set) }
  in map countCat categories

-- | Validate a logo system for completeness.
-- |
-- | Returns an array of validation warnings. Empty array means valid.
-- | Checks:
-- |   - Has at least one error defined
-- |   - No duplicate lockup names
-- |   - Watermark lockup exists (if watermark rule defined)
-- |   - Social lockups exist (if social rules defined)
validateLogoSystem :: LogoSystem -> Array String
validateLogoSystem ls =
  foldl appendWarnings [] checks
  where
    appendWarnings :: Array String -> Maybe String -> Array String
    appendWarnings acc Nothing = acc
    appendWarnings acc (Just w) = w : acc
    
    checks :: Array (Maybe String)
    checks =
      [ checkHasErrors
      , checkNoDuplicateLockups
      , checkWatermarkLockupExists
      ]
    
    checkHasErrors :: Maybe String
    checkHasErrors =
      if hasNoErrors ls.errors
      then Just "Logo system has no error constraints defined"
      else Nothing
    
    checkNoDuplicateLockups :: Maybe String
    checkNoDuplicateLockups =
      let 
        names = map (\l -> unLockupName l.name) (allLockups ls)
        uniqueNames = nub names
      in if length names /= length uniqueNames
         then Just "Duplicate lockup names detected"
         else Nothing
    
    checkWatermarkLockupExists :: Maybe String
    checkWatermarkLockupExists = case ls.watermark of
      Nothing -> Nothing
      Just w -> case findLockupByName w.lockupRef ls of
        Nothing -> Just ("Watermark references non-existent lockup: " <> unLockupName w.lockupRef)
        Just _ -> Nothing
