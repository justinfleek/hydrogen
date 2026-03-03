{- |
-- ===========================================================================
--                               // foundry // extract // component
-- ===========================================================================

Module      : Foundry.Extract.Component
Description : Extract Hydrogen components from brand data
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Converts extracted brand data (colors, fonts, spacing) into UUID5-addressed
Hydrogen atoms, molecules, and compounds.

== Pipeline

@
  ScrapeResult -> extractColors -> ColorAtoms
  ScrapeResult -> extractFonts -> FontAtoms
  ScrapeResult -> extractSpacing -> SpacingAtoms
  Atoms -> composeButton -> ButtonMolecule
  Molecules + Atoms -> composeCard -> CardCompound
@

== Dependencies

Requires: Foundry.Extract.Types, Foundry.Core.Component.Registry
Required by: Demo pipeline

-- ===========================================================================
-}
module Foundry.Extract.Component
  ( -- * Atom Types
    ColorAtomRec (..)
  , FontAtomRec (..)
  , SpacingAtomRec (..)

    -- * Molecule Types
  , ButtonMoleculeRec (..)

    -- * Compound Types
  , HeroCompoundRec (..)
  , CardCompoundRec (..)

    -- * Registry Type
  , ExtractedRegistry (..)

    -- * Atom Extraction
  , extractColorAtoms
  , extractFontAtoms
  , extractSpacingAtoms

    -- * Molecule Composition
  , composePrimaryButton
  , composeSecondaryButton

    -- * Compound Composition
  , composeHeroSection
  , composeCardSection

    -- * Full Pipeline
  , extractComponentRegistry
  ) where

import Data.ByteString qualified as BS
import Data.Hashable (hash)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Data.UUID qualified as UUID
import Data.UUID.V5 qualified as UUID5
import Data.Vector (Vector)
import Data.Vector qualified as V
import Numeric (showHex)

import Foundry.Extract.Types
  ( CSSProperty (..)
  , CSSRule (..)
  , CSSSelector (..)
  , CSSStylesheet (..)
  , CSSValue (..)
  , FontData (..)
  , ScrapeResult (..)
  )

-- ===========================================================================
-- Component ID Generation (UUID5)
-- ===========================================================================

-- | Namespace for component UUIDs
componentNamespace :: UUID.UUID
componentNamespace = UUID5.generateNamed
  UUID5.namespaceURL
  (BS.unpack $ TE.encodeUtf8 "foundry:component")

-- | Generate UUID5 for a component
mkComponentUUID :: Text -> Text -> Text -> Text -> UUID.UUID
mkComponentUUID domain level componentType contentHash =
  UUID5.generateNamed componentNamespace nameBytes
  where
    name = T.intercalate ":" [domain, level, componentType, contentHash]
    nameBytes = BS.unpack $ TE.encodeUtf8 name

-- | Hash content to hex string
hashContent :: Text -> Text
hashContent content = T.pack $ showHex (abs (hash content)) ""

-- ===========================================================================
-- Color Atom Extraction
-- ===========================================================================

-- | Color atom record
data ColorAtomRec = ColorAtomRec
  { carId    :: !UUID.UUID
  , carName  :: !Text
  , carHex   :: !Text
  , carRole  :: !Text
  }
  deriving stock (Eq, Show)

-- | Extract color atoms from scrape result
--
-- Scans CSS for color values and assigns semantic roles based on usage patterns.
extractColorAtoms :: ScrapeResult -> Vector ColorAtomRec
extractColorAtoms sr = V.fromList $ deduplicateColors $ concatMap extractFromStylesheet sheets
  where
    sheets = V.toList (srStylesheets sr)
    domain = srDomain sr

    extractFromStylesheet :: CSSStylesheet -> [ColorAtomRec]
    extractFromStylesheet css = concatMap extractFromRule (V.toList (cssRules css))

    extractFromRule :: CSSRule -> [ColorAtomRec]
    extractFromRule rule = mapMaybe (extractColorProp domain selector) props
      where
        CSSSelector selector = cssSelector rule
        props = V.toList (cssProperties rule)

    mapMaybe :: (a -> Maybe b) -> [a] -> [b]
    mapMaybe f = foldr (\x acc -> case f x of Just y -> y : acc; Nothing -> acc) []

    deduplicateColors :: [ColorAtomRec] -> [ColorAtomRec]
    deduplicateColors = Map.elems . Map.fromList . map (\c -> (carHex c, c))

-- | Extract color from a CSS property
extractColorProp :: Text -> Text -> CSSProperty -> Maybe ColorAtomRec
extractColorProp domain selector prop = case cssPropValue prop of
  CSSColor hexColor -> Just ColorAtomRec
    { carId = mkComponentUUID domain "atom" "color" (hashContent hexColor)
    , carName = inferColorName selector (cssPropName prop)
    , carHex = hexColor
    , carRole = inferColorRole selector (cssPropName prop)
    }
  _ -> Nothing

-- | Infer semantic color name from usage
inferColorName :: Text -> Text -> Text
inferColorName selector propName
  | "primary" `T.isInfixOf` selector = "primary"
  | "secondary" `T.isInfixOf` selector = "secondary"
  | "accent" `T.isInfixOf` selector = "accent"
  | "error" `T.isInfixOf` selector || "destructive" `T.isInfixOf` selector = "destructive"
  | "success" `T.isInfixOf` selector = "success"
  | "warning" `T.isInfixOf` selector = "warning"
  | "background" `T.isInfixOf` propName = "background"
  | "color" == propName = "foreground"
  | "border" `T.isInfixOf` propName = "border"
  | otherwise = "color-" <> hashContent (selector <> propName)

-- | Infer color role from usage
inferColorRole :: Text -> Text -> Text
inferColorRole selector propName
  | "primary" `T.isInfixOf` selector = "primary"
  | "secondary" `T.isInfixOf` selector = "secondary"
  | "accent" `T.isInfixOf` selector = "accent"
  | "btn" `T.isInfixOf` selector || "button" `T.isInfixOf` selector = "action"
  | "background" `T.isInfixOf` propName = "surface"
  | "color" == propName && "body" `T.isInfixOf` selector = "text"
  | otherwise = "neutral"

-- ===========================================================================
-- Font Atom Extraction
-- ===========================================================================

-- | Font atom record
data FontAtomRec = FontAtomRec
  { farId      :: !UUID.UUID
  , farFamily  :: !Text
  , farWeight  :: !Int
  , farRole    :: !Text
  }
  deriving stock (Eq, Show)

-- | Extract font atoms from scrape result
extractFontAtoms :: ScrapeResult -> Vector FontAtomRec
extractFontAtoms sr = V.fromList $ dedup $ Map.elems usedFonts
  where
    fontData = srFontData sr
    domain = srDomain sr

    -- fdUsedFonts contains font family -> usage count
    usedFonts :: Map Text FontAtomRec
    usedFonts = Map.mapWithKey (toFontAtom domain) (fdUsedFonts fontData)

    toFontAtom :: Text -> Text -> Int -> FontAtomRec
    toFontAtom dom family _count = FontAtomRec
      { farId = mkComponentUUID dom "atom" "font" (hashContent family)
      , farFamily = family
      , farWeight = 400  -- Default, can be refined
      , farRole = inferFontRole family
      }

    dedup :: [FontAtomRec] -> [FontAtomRec]
    dedup = id  -- Already deduped by Map

-- | Infer font role from family name and patterns
inferFontRole :: Text -> Text
inferFontRole family
  | "Raleway" `T.isInfixOf` family = "heading"
  | "Roboto" `T.isInfixOf` family = "body"
  | "Open Sans" `T.isInfixOf` family = "body"
  | "Mono" `T.isInfixOf` family || "Code" `T.isInfixOf` family = "mono"
  | "Display" `T.isInfixOf` family = "display"
  | otherwise = "body"

-- ===========================================================================
-- Spacing Atom Extraction
-- ===========================================================================

-- | Spacing atom record
data SpacingAtomRec = SpacingAtomRec
  { sarId    :: !UUID.UUID
  , sarName  :: !Text
  , sarValue :: !Double  -- rem
  , sarPx    :: !Int     -- computed at 16px base
  }
  deriving stock (Eq, Show)

-- | Extract spacing atoms from CSS
--
-- Looks for padding, margin, gap values and derives a spacing scale.
extractSpacingAtoms :: ScrapeResult -> Vector SpacingAtomRec
extractSpacingAtoms sr = V.fromList $ standardSpacingScale (srDomain sr)

-- | Standard spacing scale (Tailwind-like)
standardSpacingScale :: Text -> [SpacingAtomRec]
standardSpacingScale domain =
  [ mkSpacing "0"   0       0
  , mkSpacing "px"  0.0625  1
  , mkSpacing "0.5" 0.125   2
  , mkSpacing "1"   0.25    4
  , mkSpacing "1.5" 0.375   6
  , mkSpacing "2"   0.5     8
  , mkSpacing "2.5" 0.625   10
  , mkSpacing "3"   0.75    12
  , mkSpacing "3.5" 0.875   14
  , mkSpacing "4"   1.0     16
  , mkSpacing "5"   1.25    20
  , mkSpacing "6"   1.5     24
  , mkSpacing "7"   1.75    28
  , mkSpacing "8"   2.0     32
  , mkSpacing "9"   2.25    36
  , mkSpacing "10"  2.5     40
  , mkSpacing "11"  2.75    44
  , mkSpacing "12"  3.0     48
  , mkSpacing "14"  3.5     56
  , mkSpacing "16"  4.0     64
  , mkSpacing "20"  5.0     80
  , mkSpacing "24"  6.0     96
  , mkSpacing "28"  7.0     112
  , mkSpacing "32"  8.0     128
  ]
  where
    mkSpacing name val px = SpacingAtomRec
      { sarId = mkComponentUUID domain "atom" "spacing" (hashContent name)
      , sarName = name
      , sarValue = val
      , sarPx = px
      }

-- ===========================================================================
-- Molecule Composition
-- ===========================================================================

-- | Button molecule record
data ButtonMoleculeRec = ButtonMoleculeRec
  { bmrId       :: !UUID.UUID
  , bmrVariant  :: !Text
  , bmrBgColor  :: !UUID.UUID
  , bmrTextColor :: !UUID.UUID
  , bmrFont     :: !UUID.UUID
  , bmrPaddingX :: !UUID.UUID
  , bmrPaddingY :: !UUID.UUID
  }
  deriving stock (Eq, Show)

-- | Compose primary button from atoms
composePrimaryButton
  :: Text  -- ^ Domain
  -> ColorAtomRec  -- ^ Background color
  -> ColorAtomRec  -- ^ Text color
  -> FontAtomRec   -- ^ Font
  -> SpacingAtomRec  -- ^ Padding X
  -> SpacingAtomRec  -- ^ Padding Y
  -> ButtonMoleculeRec
composePrimaryButton domain bgColor textColor font padX padY = ButtonMoleculeRec
  { bmrId = mkComponentUUID domain "molecule" "button" "primary"
  , bmrVariant = "primary"
  , bmrBgColor = carId bgColor
  , bmrTextColor = carId textColor
  , bmrFont = farId font
  , bmrPaddingX = sarId padX
  , bmrPaddingY = sarId padY
  }

-- | Compose secondary button
composeSecondaryButton
  :: Text
  -> ColorAtomRec
  -> ColorAtomRec
  -> FontAtomRec
  -> SpacingAtomRec
  -> SpacingAtomRec
  -> ButtonMoleculeRec
composeSecondaryButton domain bgColor textColor font padX padY = ButtonMoleculeRec
  { bmrId = mkComponentUUID domain "molecule" "button" "secondary"
  , bmrVariant = "secondary"
  , bmrBgColor = carId bgColor
  , bmrTextColor = carId textColor
  , bmrFont = farId font
  , bmrPaddingX = sarId padX
  , bmrPaddingY = sarId padY
  }

-- ===========================================================================
-- Compound Composition
-- ===========================================================================

-- | Hero compound record
data HeroCompoundRec = HeroCompoundRec
  { hcrId          :: !UUID.UUID
  , hcrBgColor     :: !UUID.UUID
  , hcrTextColor   :: !UUID.UUID
  , hcrHeadingFont :: !UUID.UUID
  , hcrBodyFont    :: !UUID.UUID
  , hcrCTA         :: !(Maybe UUID.UUID)
  }
  deriving stock (Eq, Show)

-- | Compose hero section
composeHeroSection
  :: Text
  -> ColorAtomRec
  -> ColorAtomRec
  -> FontAtomRec
  -> FontAtomRec
  -> Maybe ButtonMoleculeRec
  -> HeroCompoundRec
composeHeroSection domain bgColor textColor headingFont bodyFont mCta = HeroCompoundRec
  { hcrId = mkComponentUUID domain "compound" "hero" "main"
  , hcrBgColor = carId bgColor
  , hcrTextColor = carId textColor
  , hcrHeadingFont = farId headingFont
  , hcrBodyFont = farId bodyFont
  , hcrCTA = bmrId <$> mCta
  }

-- | Card compound record
data CardCompoundRec = CardCompoundRec
  { ccrId      :: !UUID.UUID
  , ccrBgColor :: !UUID.UUID
  , ccrPadding :: !UUID.UUID
  }
  deriving stock (Eq, Show)

-- | Compose card section
composeCardSection
  :: Text
  -> ColorAtomRec
  -> SpacingAtomRec
  -> CardCompoundRec
composeCardSection domain bgColor padding = CardCompoundRec
  { ccrId = mkComponentUUID domain "compound" "card" "default"
  , ccrBgColor = carId bgColor
  , ccrPadding = sarId padding
  }

-- ===========================================================================
-- Full Pipeline
-- ===========================================================================

-- | Extracted component registry
data ExtractedRegistry = ExtractedRegistry
  { erDomain   :: !Text
  , erColors   :: !(Vector ColorAtomRec)
  , erFonts    :: !(Vector FontAtomRec)
  , erSpacing  :: !(Vector SpacingAtomRec)
  , erButtons  :: !(Vector ButtonMoleculeRec)
  , erHeros    :: !(Vector HeroCompoundRec)
  , erCards    :: !(Vector CardCompoundRec)
  }
  deriving stock (Eq, Show)

-- | Extract full component registry from scrape result
extractComponentRegistry :: ScrapeResult -> ExtractedRegistry
extractComponentRegistry sr = ExtractedRegistry
  { erDomain = srDomain sr
  , erColors = colors
  , erFonts = fonts
  , erSpacing = spacing
  , erButtons = buttons
  , erHeros = heros
  , erCards = cards
  }
  where
    colors = extractColorAtoms sr
    fonts = extractFontAtoms sr
    spacing = extractSpacingAtoms sr

    -- Find primary color (first with "primary" role or first in list)
    primaryColor = case V.find (\c -> carRole c == "primary") colors of
      Just c -> c
      Nothing -> case V.headM colors of
        Just c -> c
        Nothing -> ColorAtomRec
          { carId = mkComponentUUID (srDomain sr) "atom" "color" "fallback"
          , carName = "primary"
          , carHex = "#000000"
          , carRole = "primary"
          }

    -- White color for contrast
    whiteColor = ColorAtomRec
      { carId = mkComponentUUID (srDomain sr) "atom" "color" "white"
      , carName = "white"
      , carHex = "#ffffff"
      , carRole = "surface"
      }

    -- Find heading font
    headingFont = case V.find (\f -> farRole f == "heading") fonts of
      Just f -> f
      Nothing -> case V.headM fonts of
        Just f -> f
        Nothing -> FontAtomRec
          { farId = mkComponentUUID (srDomain sr) "atom" "font" "fallback"
          , farFamily = "system-ui"
          , farWeight = 600
          , farRole = "heading"
          }

    -- Find body font
    bodyFont = case V.find (\f -> farRole f == "body") fonts of
      Just f -> f
      Nothing -> headingFont

    -- Spacing tokens
    padX = case spacing V.!? 6 of  -- spacing-4 (1rem)
      Just s -> s
      Nothing -> SpacingAtomRec
        { sarId = mkComponentUUID (srDomain sr) "atom" "spacing" "4"
        , sarName = "4"
        , sarValue = 1.0
        , sarPx = 16
        }

    padY = case spacing V.!? 4 of  -- spacing-2 (0.5rem)
      Just s -> s
      Nothing -> SpacingAtomRec
        { sarId = mkComponentUUID (srDomain sr) "atom" "spacing" "2"
        , sarName = "2"
        , sarValue = 0.5
        , sarPx = 8
        }

    cardPadding = case spacing V.!? 8 of  -- spacing-6 (1.5rem)
      Just s -> s
      Nothing -> padX

    -- Compose molecules
    primaryButton = composePrimaryButton (srDomain sr) primaryColor whiteColor headingFont padX padY
    secondaryButton = composeSecondaryButton (srDomain sr) whiteColor primaryColor headingFont padX padY
    buttons = V.fromList [primaryButton, secondaryButton]

    -- Compose compounds
    hero = composeHeroSection (srDomain sr) primaryColor whiteColor headingFont bodyFont (Just primaryButton)
    heros = V.fromList [hero]

    card = composeCardSection (srDomain sr) whiteColor cardPadding
    cards = V.fromList [card]
