{- |
-- ===========================================================================
--                               // foundry // core // component // registry
-- ===========================================================================

Module      : Foundry.Core.Component.Registry
Description : UUID5-addressed component registry (Atoms, Molecules, Compounds)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Atomic design component registry with deterministic UUID5 addressing.

== Design Philosophy

Components follow Atomic Design methodology:

  Atoms     - Basic building blocks (colors, fonts, spacing values)
  Molecules - Simple combinations (button = color + font + spacing)
  Compounds - Complex assemblies (card = multiple molecules + layout)

All components are addressed by UUID5 derived from:
  1. Brand domain (namespace)
  2. Component type + canonical representation (name)

This ensures:
  - Determinism: Same brand + component = same UUID
  - Deduplication: Identical components across brands share analysis
  - Versioning: Content changes produce new UUIDs

== Dependencies

Requires: uuid, text, vector
Required by: Foundry.Storage.DuckDB, Foundry.Extract.Hydrogen

-- ===========================================================================
-}
module Foundry.Core.Component.Registry
  ( -- * Component Levels
    ComponentLevel (..)
  , levelToText
  , parseLevel

    -- * Component Types (by level)
  , AtomType (..)
  , MoleculeType (..)
  , CompoundType (..)
  , atomTypeToText
  , moleculeTypeToText
  , compoundTypeToText

    -- * Component Identity
  , ComponentId (..)
  , mkComponentId
  , componentIdToUUID

    -- * Atoms
  , ColorAtom (..)
  , FontAtom (..)
  , SpacingAtom (..)
  , RadiusAtom (..)
  , ShadowAtom (..)
  , Atom (..)

    -- * Molecules
  , ButtonMolecule (..)
  , InputMolecule (..)
  , LinkMolecule (..)
  , Molecule (..)

    -- * Compounds
  , CardCompound (..)
  , NavCompound (..)
  , HeroCompound (..)
  , Compound (..)

    -- * Registry
  , ComponentRegistry (..)
  , emptyRegistry
  , registerAtom
  , registerMolecule
  , registerCompound
  , lookupAtom
  , lookupMolecule
  , lookupCompound

    -- * Hydrogen Generation
  , atomToPureScript
  , moleculeToPureScript
  ) where

import Data.ByteString qualified as BS
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Data.UUID (UUID)
import Data.UUID qualified as UUID
import Data.UUID.V5 qualified as UUID5
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

-- ===========================================================================
-- Component Levels
-- ===========================================================================

-- | Atomic design levels
data ComponentLevel
  = LevelAtom       -- ^ Fundamental building blocks
  | LevelMolecule   -- ^ Simple combinations of atoms
  | LevelCompound   -- ^ Complex assemblies
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

levelToText :: ComponentLevel -> Text
levelToText LevelAtom     = "atom"
levelToText LevelMolecule = "molecule"
levelToText LevelCompound = "compound"

parseLevel :: Text -> Maybe ComponentLevel
parseLevel t = case T.toLower t of
  "atom"     -> Just LevelAtom
  "molecule" -> Just LevelMolecule
  "compound" -> Just LevelCompound
  _          -> Nothing

-- ===========================================================================
-- Component Types
-- ===========================================================================

-- | Atom types
data AtomType
  = ATColor
  | ATFont
  | ATSpacing
  | ATRadius
  | ATShadow
  | ATIcon
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

atomTypeToText :: AtomType -> Text
atomTypeToText ATColor   = "color"
atomTypeToText ATFont    = "font"
atomTypeToText ATSpacing = "spacing"
atomTypeToText ATRadius  = "radius"
atomTypeToText ATShadow  = "shadow"
atomTypeToText ATIcon    = "icon"

-- | Molecule types
data MoleculeType
  = MTButton
  | MTInput
  | MTLink
  | MTBadge
  | MTAvatar
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

moleculeTypeToText :: MoleculeType -> Text
moleculeTypeToText MTButton = "button"
moleculeTypeToText MTInput  = "input"
moleculeTypeToText MTLink   = "link"
moleculeTypeToText MTBadge  = "badge"
moleculeTypeToText MTAvatar = "avatar"

-- | Compound types
data CompoundType
  = CTCard
  | CTNav
  | CTHero
  | CTFooter
  | CTForm
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

compoundTypeToText :: CompoundType -> Text
compoundTypeToText CTCard   = "card"
compoundTypeToText CTNav    = "nav"
compoundTypeToText CTHero   = "hero"
compoundTypeToText CTFooter = "footer"
compoundTypeToText CTForm   = "form"

-- ===========================================================================
-- Component Identity (UUID5)
-- ===========================================================================

-- | Component identifier - deterministic UUID5
newtype ComponentId = ComponentId { unComponentId :: UUID }
  deriving stock (Eq, Ord, Show, Generic)

-- | Extract UUID from ComponentId
componentIdToUUID :: ComponentId -> UUID
componentIdToUUID = unComponentId

-- | UUID5 namespace for components (derived from foundry:component)
componentNamespace :: UUID
componentNamespace = UUID5.generateNamed 
  UUID5.namespaceURL 
  (BS.unpack $ TE.encodeUtf8 "foundry:component")

-- | Generate deterministic component ID from domain + type + content hash
--
-- The name is formed as: "domain:level:type:content"
-- This ensures same component across brands can be compared.
mkComponentId :: Text -> ComponentLevel -> Text -> Text -> ComponentId
mkComponentId domain level componentType contentHash = 
  ComponentId $ UUID5.generateNamed componentNamespace nameBytes
  where
    name = T.intercalate ":" [domain, levelToText level, componentType, contentHash]
    nameBytes = BS.unpack $ TE.encodeUtf8 name

-- ===========================================================================
-- Atoms
-- ===========================================================================

-- | Color atom - fundamental color value
data ColorAtom = ColorAtom
  { caId      :: !ComponentId
  , caName    :: !Text           -- ^ Semantic name (e.g., "primary", "background")
  , caHex     :: !Text           -- ^ Hex value (#RRGGBB)
  , caOklch   :: !(Maybe Text)   -- ^ OKLCH value for perceptual consistency
  , caRole    :: !Text           -- ^ Role in palette (primary, secondary, accent, neutral)
  }
  deriving stock (Eq, Show, Generic)

-- | Font atom - typography specification
data FontAtom = FontAtom
  { faId      :: !ComponentId
  , faFamily  :: !Text           -- ^ Font family name
  , faWeight  :: !Int            -- ^ Weight (100-900)
  , faRole    :: !Text           -- ^ Role (heading, body, mono, display)
  , faFallback :: !(Vector Text) -- ^ Fallback stack
  }
  deriving stock (Eq, Show, Generic)

-- | Spacing atom - spacing value
data SpacingAtom = SpacingAtom
  { saId    :: !ComponentId
  , saName  :: !Text      -- ^ Token name (xs, sm, md, lg, xl)
  , saValue :: !Double    -- ^ Value in rem
  , saPx    :: !Int       -- ^ Computed px (at 16px base)
  }
  deriving stock (Eq, Show, Generic)

-- | Radius atom - border radius
data RadiusAtom = RadiusAtom
  { raId    :: !ComponentId
  , raName  :: !Text      -- ^ Token name (none, sm, md, lg, full)
  , raValue :: !Text      -- ^ CSS value
  }
  deriving stock (Eq, Show, Generic)

-- | Shadow atom - box shadow
data ShadowAtom = ShadowAtom
  { shId    :: !ComponentId
  , shName  :: !Text      -- ^ Token name (sm, md, lg, xl)
  , shValue :: !Text      -- ^ CSS box-shadow value
  }
  deriving stock (Eq, Show, Generic)

-- | Union of all atom types
data Atom
  = AtomColor   !ColorAtom
  | AtomFont    !FontAtom
  | AtomSpacing !SpacingAtom
  | AtomRadius  !RadiusAtom
  | AtomShadow  !ShadowAtom
  deriving stock (Eq, Show, Generic)

-- ===========================================================================
-- Molecules
-- ===========================================================================

-- | Button molecule - combination of color + font + spacing + radius atoms
data ButtonMolecule = ButtonMolecule
  { bmId          :: !ComponentId
  , bmVariant     :: !Text           -- ^ primary, secondary, ghost, destructive
  , bmBgColor     :: !ComponentId    -- ^ Reference to color atom
  , bmTextColor   :: !ComponentId    -- ^ Reference to color atom
  , bmFont        :: !ComponentId    -- ^ Reference to font atom
  , bmPaddingX    :: !ComponentId    -- ^ Reference to spacing atom
  , bmPaddingY    :: !ComponentId    -- ^ Reference to spacing atom
  , bmRadius      :: !ComponentId    -- ^ Reference to radius atom
  , bmShadow      :: !(Maybe ComponentId) -- ^ Optional shadow atom
  }
  deriving stock (Eq, Show, Generic)

-- | Input molecule
data InputMolecule = InputMolecule
  { imId          :: !ComponentId
  , imBgColor     :: !ComponentId
  , imTextColor   :: !ComponentId
  , imBorderColor :: !ComponentId
  , imFont        :: !ComponentId
  , imPadding     :: !ComponentId
  , imRadius      :: !ComponentId
  }
  deriving stock (Eq, Show, Generic)

-- | Link molecule
data LinkMolecule = LinkMolecule
  { lmId        :: !ComponentId
  , lmColor     :: !ComponentId
  , lmHoverColor :: !ComponentId
  , lmFont      :: !ComponentId
  , lmUnderline :: !Bool
  }
  deriving stock (Eq, Show, Generic)

-- | Union of all molecule types
data Molecule
  = MoleculeButton !ButtonMolecule
  | MoleculeInput  !InputMolecule
  | MoleculeLink   !LinkMolecule
  deriving stock (Eq, Show, Generic)

-- ===========================================================================
-- Compounds
-- ===========================================================================

-- | Card compound
data CardCompound = CardCompound
  { ccId       :: !ComponentId
  , ccBgColor  :: !ComponentId
  , ccShadow   :: !(Maybe ComponentId)
  , ccRadius   :: !ComponentId
  , ccPadding  :: !ComponentId
  , ccHeader   :: !(Maybe ComponentId)  -- ^ Optional header molecule
  , ccFooter   :: !(Maybe ComponentId)  -- ^ Optional footer molecule
  }
  deriving stock (Eq, Show, Generic)

-- | Navigation compound
data NavCompound = NavCompound
  { ncId       :: !ComponentId
  , ncBgColor  :: !ComponentId
  , ncLinks    :: !(Vector ComponentId)  -- ^ Link molecules
  , ncLogo     :: !(Maybe Text)          -- ^ Logo URL
  , ncSticky   :: !Bool
  }
  deriving stock (Eq, Show, Generic)

-- | Hero compound
data HeroCompound = HeroCompound
  { hcId          :: !ComponentId
  , hcBgColor     :: !ComponentId
  , hcTextColor   :: !ComponentId
  , hcHeadingFont :: !ComponentId
  , hcBodyFont    :: !ComponentId
  , hcCTA         :: !(Maybe ComponentId)  -- ^ Button molecule
  , hcBgImage     :: !(Maybe Text)
  }
  deriving stock (Eq, Show, Generic)

-- | Union of all compound types
data Compound
  = CompoundCard !CardCompound
  | CompoundNav  !NavCompound
  | CompoundHero !HeroCompound
  deriving stock (Eq, Show, Generic)

-- ===========================================================================
-- Registry
-- ===========================================================================

-- | Component registry holding all atoms, molecules, and compounds
data ComponentRegistry = ComponentRegistry
  { crAtoms     :: !(Map ComponentId Atom)
  , crMolecules :: !(Map ComponentId Molecule)
  , crCompounds :: !(Map ComponentId Compound)
  , crDomain    :: !Text
  }
  deriving stock (Eq, Show, Generic)

-- | Empty registry for a domain
emptyRegistry :: Text -> ComponentRegistry
emptyRegistry domain = ComponentRegistry
  { crAtoms     = Map.empty
  , crMolecules = Map.empty
  , crCompounds = Map.empty
  , crDomain    = domain
  }

-- | Register an atom
registerAtom :: ComponentId -> Atom -> ComponentRegistry -> ComponentRegistry
registerAtom cid atom reg = reg { crAtoms = Map.insert cid atom (crAtoms reg) }

-- | Register a molecule
registerMolecule :: ComponentId -> Molecule -> ComponentRegistry -> ComponentRegistry
registerMolecule cid mol reg = reg { crMolecules = Map.insert cid mol (crMolecules reg) }

-- | Register a compound
registerCompound :: ComponentId -> Compound -> ComponentRegistry -> ComponentRegistry
registerCompound cid comp reg = reg { crCompounds = Map.insert cid comp (crCompounds reg) }

-- | Lookup an atom
lookupAtom :: ComponentId -> ComponentRegistry -> Maybe Atom
lookupAtom cid reg = Map.lookup cid (crAtoms reg)

-- | Lookup a molecule
lookupMolecule :: ComponentId -> ComponentRegistry -> Maybe Molecule
lookupMolecule cid reg = Map.lookup cid (crMolecules reg)

-- | Lookup a compound
lookupCompound :: ComponentId -> ComponentRegistry -> Maybe Compound
lookupCompound cid reg = Map.lookup cid (crCompounds reg)

-- ===========================================================================
-- Hydrogen Code Generation
-- ===========================================================================

-- | Generate PureScript code for a color atom
atomToPureScript :: Atom -> Text
atomToPureScript (AtomColor ca) = T.unlines
  [ "-- | Color: " <> caName ca
  , "-- | UUID5: " <> UUID.toText (componentIdToUUID (caId ca))
  , caName ca <> " :: String"
  , caName ca <> " = \"" <> caHex ca <> "\""
  ]
atomToPureScript (AtomFont fa) = T.unlines
  [ "-- | Font: " <> faFamily fa
  , "-- | UUID5: " <> UUID.toText (componentIdToUUID (faId fa))
  , "font" <> T.toTitle (faRole fa) <> " :: String"
  , "font" <> T.toTitle (faRole fa) <> " = \"" <> faFamily fa <> ", " <> fallbackStack <> "\""
  ]
  where
    fallbackStack = T.intercalate ", " (V.toList (faFallback fa))
atomToPureScript (AtomSpacing sa) = T.unlines
  [ "-- | Spacing: " <> saName sa
  , "-- | UUID5: " <> UUID.toText (componentIdToUUID (saId sa))
  , "spacing" <> T.toTitle (saName sa) <> " :: String"
  , "spacing" <> T.toTitle (saName sa) <> " = \"" <> T.pack (show (saValue sa)) <> "rem\""
  ]
atomToPureScript (AtomRadius ra) = T.unlines
  [ "-- | Radius: " <> raName ra
  , "-- | UUID5: " <> UUID.toText (componentIdToUUID (raId ra))
  , "radius" <> T.toTitle (raName ra) <> " :: String"
  , "radius" <> T.toTitle (raName ra) <> " = \"" <> raValue ra <> "\""
  ]
atomToPureScript (AtomShadow sh) = T.unlines
  [ "-- | Shadow: " <> shName sh
  , "-- | UUID5: " <> UUID.toText (componentIdToUUID (shId sh))
  , "shadow" <> T.toTitle (shName sh) <> " :: String"
  , "shadow" <> T.toTitle (shName sh) <> " = \"" <> shValue sh <> "\""
  ]

-- | Generate PureScript component for a button molecule
moleculeToPureScript :: ComponentRegistry -> Molecule -> Text
moleculeToPureScript _reg (MoleculeButton bm) = T.unlines
  [ "-- | Button: " <> bmVariant bm
  , "-- | UUID5: " <> UUID.toText (componentIdToUUID (bmId bm))
  , "button" <> T.toTitle (bmVariant bm) <> " :: forall w i. Array (HH.HTML w i) -> HH.HTML w i"
  , "button" <> T.toTitle (bmVariant bm) <> " children ="
  , "  HH.button"
  , "    [ cls"
  , "        [ \"px-4 py-2\""
  , "        , \"rounded-md\""
  , "        , \"font-medium\""
  , "        , \"transition-colors\""
  , "        ]"
  , "    ]"
  , "    children"
  ]
moleculeToPureScript _reg (MoleculeInput im) = T.unlines
  [ "-- | Input"
  , "-- | UUID5: " <> UUID.toText (componentIdToUUID (imId im))
  , "inputField :: forall w i. HH.HTML w i"
  , "inputField = HH.input []"
  ]
moleculeToPureScript _reg (MoleculeLink lm) = T.unlines
  [ "-- | Link"
  , "-- | UUID5: " <> UUID.toText (componentIdToUUID (lmId lm))
  , "link :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i"
  , "link href children = HH.a [ HP.href href ] children"
  ]
