-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // icon // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Icon Type System — Core type definitions for the Hydrogen icon system.
-- |
-- | Icons are path-based primitives that can render to SVG, Canvas, or WebGL.
-- | The type system supports:
-- |
-- | - **Multi-path icons**: Icons composed of multiple paths (e.g., duotone)
-- | - **Semantic parts**: Named path regions for brand color assignment
-- | - **Size variants**: Bounded size system (Xs through Xxl)
-- | - **Style variants**: Outline, Solid, Duotone, Filled rendering modes
-- |
-- | ## Architecture
-- |
-- | ```
-- | IconDefinition (source of truth)
-- |       │
-- |       ├──► SVG Element (DOM rendering)
-- |       ├──► Canvas commands (2D rendering)
-- |       ├──► WebGL geometry (3D rendering)
-- |       └──► Mesh3D (extruded 3D icon)
-- | ```
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Icons are deterministic data. Same IconDefinition = same pixels, always.
-- | Path data uses bounded coordinates. No NaN, no Infinity, no escape hatches.

module Hydrogen.Icon.Types
  ( -- * Core Types
    IconDefinition(..)
  , IconPath(..)
  , IconPart(..)
  , IconPartName(..)
  , mkIconPartName
  , unIconPartName
  , partNameEq
  
  -- * Icon Identification
  , IconName(..)
  , mkIconName
  , unIconName
  , IconCategory(..)
  , allCategories
  , categoryToString
  
  -- * Size System
  , IconSize(..)
  , allSizes
  , sizeToPixels
  , sizeFromPixels
  
  -- * Style System
  , IconStyle(..)
  , allStyles
  , styleToString
  
  -- * Rendering Properties
  , IconProps
  , defaultIconProps
  , StrokeWidth
  , clampStrokeWidth
  
  -- * Accessibility
  , IconAccessibility
  , defaultAccessibility
  , decorativeAccessibility
  
  -- * ViewBox
  , IconViewBox
  , defaultViewBox
  , viewBox24
  , viewBox16
  
  -- * Fill Rules
  , FillRule(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (<=)
  , (>=)
  , (<>)
  , (&&)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String

import Hydrogen.Schema.Geometry.Path.Types (Path)
import Hydrogen.Schema.Brand.Token.Color (ColorRole(RoleOnSurface))
import Hydrogen.Schema.Accessibility.Property (AriaLabel)
import Hydrogen.Schema.Accessibility.State (AriaHidden(AriaHidden))
import Hydrogen.Schema.Accessibility.Role (StructureRole(RoleImg))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // icon name
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validated icon name.
-- |
-- | Icon names follow kebab-case convention: "arrow-left", "check-circle".
-- | Names are bounded: minimum 1 character, maximum 64 characters.
newtype IconName = IconName String

derive instance eqIconName :: Eq IconName
derive instance ordIconName :: Ord IconName

instance showIconName :: Show IconName where
  show (IconName n) = "(IconName " <> show n <> ")"

-- | Create a validated icon name.
-- |
-- | Returns Nothing if name is empty or exceeds 64 characters.
mkIconName :: String -> Maybe IconName
mkIconName s
  | String.length s >= 1 && String.length s <= 64 = Just (IconName s)
  | true = Nothing

-- | Extract the raw string from an icon name.
unIconName :: IconName -> String
unIconName (IconName s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // icon category
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icon categories for organization and discovery.
-- |
-- | Categories help agents find appropriate icons by semantic domain.
data IconCategory
  = CategoryActions      -- ^ User actions: check, x, plus, minus, edit, delete
  | CategoryArrows       -- ^ Directional: arrows, chevrons, carets
  | CategoryStatus       -- ^ Feedback: success, warning, error, info, loading
  | CategoryObjects      -- ^ Things: file, folder, user, settings, home
  | CategoryMedia        -- ^ Playback: play, pause, stop, volume, camera
  | CategoryLayout       -- ^ Structure: menu, grid, sidebar, columns
  | CategoryData         -- ^ Visualization: chart, graph, trending, database
  | CategoryCommunication -- ^ Messaging: mail, chat, phone, share
  | CategoryCommerce     -- ^ Shopping: cart, bag, credit-card, receipt
  | CategoryBrand        -- ^ Logos and brand marks
  | CategoryCustom       -- ^ User-defined icons

derive instance eqIconCategory :: Eq IconCategory
derive instance ordIconCategory :: Ord IconCategory

instance showIconCategory :: Show IconCategory where
  show = categoryToString

-- | Convert category to string for serialization.
categoryToString :: IconCategory -> String
categoryToString = case _ of
  CategoryActions -> "actions"
  CategoryArrows -> "arrows"
  CategoryStatus -> "status"
  CategoryObjects -> "objects"
  CategoryMedia -> "media"
  CategoryLayout -> "layout"
  CategoryData -> "data"
  CategoryCommunication -> "communication"
  CategoryCommerce -> "commerce"
  CategoryBrand -> "brand"
  CategoryCustom -> "custom"

-- | All available categories.
allCategories :: Array IconCategory
allCategories =
  [ CategoryActions
  , CategoryArrows
  , CategoryStatus
  , CategoryObjects
  , CategoryMedia
  , CategoryLayout
  , CategoryData
  , CategoryCommunication
  , CategoryCommerce
  , CategoryBrand
  , CategoryCustom
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // icon size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounded icon size variants.
-- |
-- | Sizes are discrete to ensure consistent rendering across the system.
-- | No arbitrary sizes — agents must choose from this bounded set.
data IconSize
  = SizeXs    -- ^ 12px — Inline text, badges
  | SizeSm    -- ^ 16px — Compact UI, form fields
  | SizeMd    -- ^ 20px — Default, buttons
  | SizeLg    -- ^ 24px — Navigation, headers
  | SizeXl    -- ^ 32px — Feature icons, empty states
  | SizeXxl   -- ^ 48px — Hero icons, illustrations

derive instance eqIconSize :: Eq IconSize
derive instance ordIconSize :: Ord IconSize

instance showIconSize :: Show IconSize where
  show = case _ of
    SizeXs -> "xs"
    SizeSm -> "sm"
    SizeMd -> "md"
    SizeLg -> "lg"
    SizeXl -> "xl"
    SizeXxl -> "xxl"

-- | Convert size to pixel value.
sizeToPixels :: IconSize -> Int
sizeToPixels = case _ of
  SizeXs -> 12
  SizeSm -> 16
  SizeMd -> 20
  SizeLg -> 24
  SizeXl -> 32
  SizeXxl -> 48

-- | Find nearest size for a pixel value.
-- |
-- | Values are clamped to the nearest valid size.
sizeFromPixels :: Int -> IconSize
sizeFromPixels px
  | px <= 14 = SizeXs
  | px <= 18 = SizeSm
  | px <= 22 = SizeMd
  | px <= 28 = SizeLg
  | px <= 40 = SizeXl
  | true = SizeXxl

-- | All available sizes.
allSizes :: Array IconSize
allSizes = [ SizeXs, SizeSm, SizeMd, SizeLg, SizeXl, SizeXxl ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // icon style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icon rendering style.
-- |
-- | Different styles suit different contexts:
-- | - **Outline**: Stroke-based, minimal visual weight
-- | - **Solid**: Filled shapes, higher visual weight
-- | - **Duotone**: Two-tone with primary/secondary colors
-- | - **Filled**: Solid with background shape
data IconStyle
  = StyleOutline   -- ^ Stroke-based rendering (Feather, Lucide style)
  | StyleSolid     -- ^ Filled shapes (Font Awesome solid style)
  | StyleDuotone   -- ^ Two-color rendering with opacity
  | StyleFilled    -- ^ Solid with background container

derive instance eqIconStyle :: Eq IconStyle
derive instance ordIconStyle :: Ord IconStyle

instance showIconStyle :: Show IconStyle where
  show = styleToString

-- | Convert style to string.
styleToString :: IconStyle -> String
styleToString = case _ of
  StyleOutline -> "outline"
  StyleSolid -> "solid"
  StyleDuotone -> "duotone"
  StyleFilled -> "filled"

-- | All available styles.
allStyles :: Array IconStyle
allStyles = [ StyleOutline, StyleSolid, StyleDuotone, StyleFilled ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // icon viewbox
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icon viewBox dimensions.
-- |
-- | Defines the coordinate space for icon paths.
type IconViewBox =
  { minX :: Number
  , minY :: Number
  , width :: Number
  , height :: Number
  }

-- | Default 24x24 viewBox (most common).
defaultViewBox :: IconViewBox
defaultViewBox = viewBox24

-- | Standard 24x24 viewBox.
viewBox24 :: IconViewBox
viewBox24 = { minX: 0.0, minY: 0.0, width: 24.0, height: 24.0 }

-- | Compact 16x16 viewBox.
viewBox16 :: IconViewBox
viewBox16 = { minX: 0.0, minY: 0.0, width: 16.0, height: 16.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // icon parts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Named part of an icon for selective coloring.
-- |
-- | Parts allow brand color assignment to specific regions of an icon.
-- | For example, a "user-badge" icon might have "body" and "badge" parts
-- | that can receive different brand colors.
newtype IconPartName = IconPartName String

derive instance eqIconPartName :: Eq IconPartName
derive instance ordIconPartName :: Ord IconPartName

instance showIconPartName :: Show IconPartName where
  show (IconPartName n) = "(IconPartName " <> show n <> ")"

-- | Create a part name (bounded: 1-32 chars).
mkIconPartName :: String -> Maybe IconPartName
mkIconPartName s
  | String.length s >= 1 && String.length s <= 32 = Just (IconPartName s)
  | true = Nothing

-- | Extract raw string from part name.
unIconPartName :: IconPartName -> String
unIconPartName (IconPartName s) = s

-- | Check if two part names are equal.
-- |
-- | Used for uniqueness validation in PartedIcon.
partNameEq :: IconPartName -> IconPartName -> Boolean
partNameEq (IconPartName a) (IconPartName b) = a == b

-- | A single part of an icon with its path data.
-- |
-- | Each part can have its own path and default color role.
-- | During rendering, parts can be recolored based on brand tokens.
type IconPart =
  { name :: IconPartName
  , path :: Path
  , defaultRole :: ColorRole    -- ^ Default color role if not overridden
  , fillRule :: FillRule        -- ^ SVG fill-rule for complex paths
  }

-- | SVG fill rule for path rendering.
data FillRule
  = FillNonZero   -- ^ Non-zero winding rule (default)
  | FillEvenOdd   -- ^ Even-odd rule (for complex shapes with holes)

derive instance eqFillRule :: Eq FillRule
derive instance ordFillRule :: Ord FillRule

instance showFillRule :: Show FillRule where
  show FillNonZero = "nonzero"
  show FillEvenOdd = "evenodd"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // icon paths
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icon path representation.
-- |
-- | Icons can be:
-- | - **Single**: One path (most icons)
-- | - **Multi**: Multiple paths composited together
-- | - **Parted**: Named parts for selective coloring
data IconPath
  = SinglePath Path                    -- ^ Single path icon
  | MultiPath (Array Path)             -- ^ Multiple paths composited
  | PartedIcon (Array IconPart)        -- ^ Named parts for brand coloring

derive instance eqIconPath :: Eq IconPath

instance showIconPath :: Show IconPath where
  show (SinglePath p) = "(SinglePath " <> show p <> ")"
  show (MultiPath _) = "(MultiPath)"
  show (PartedIcon _) = "(PartedIcon)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // icon definition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete icon definition — the source of truth.
-- |
-- | An IconDefinition contains all data needed to render an icon in any
-- | format (SVG, Canvas, WebGL, 3D mesh).
-- |
-- | ## Invariants
-- |
-- | - Name is unique within a category
-- | - ViewBox defines coordinate bounds
-- | - Paths use coordinates within viewBox
-- | - All parts (if PartedIcon) have unique names
type IconDefinition =
  { name :: IconName
  , category :: IconCategory
  , viewBox :: IconViewBox
  , paths :: IconPath
  , tags :: Array String          -- ^ Search tags for discovery
  , style :: IconStyle            -- ^ Intended rendering style
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // icon props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rendering properties for an icon.
-- |
-- | These properties are applied at render time to customize appearance.
-- | All properties use Schema atoms — no CSS, no string-based styling.
type IconProps =
  { size :: IconSize
  , style :: IconStyle
  , strokeWidth :: StrokeWidth              -- ^ Bounded stroke width for outline style
  , colorRole :: ColorRole                  -- ^ Primary color role (resolved to OKLCH)
  , secondaryRole :: Maybe ColorRole        -- ^ Secondary role for duotone icons
  , accessibility :: IconAccessibility      -- ^ WAI-ARIA accessibility properties
  }

-- | Bounded stroke width for icon rendering.
-- |
-- | Stroke width is bounded to [0.5, 4.0] to ensure legibility.
-- | Values outside this range are clamped.
type StrokeWidth = Number  -- Bounded: 0.5 <= w <= 4.0

-- | Clamp stroke width to valid bounds.
clampStrokeWidth :: Number -> StrokeWidth
clampStrokeWidth w
  | w <= 0.5 = 0.5
  | w >= 4.0 = 4.0
  | true = w

-- | Accessibility properties for icons.
-- |
-- | Icons are either:
-- | - **Semantic**: Have meaning, need aria-label (e.g., "Delete" button icon)
-- | - **Decorative**: Pure visual, hidden from assistive tech (aria-hidden=true)
-- |
-- | Uses proper Schema/Accessibility atoms, not strings.
type IconAccessibility =
  { role :: StructureRole          -- ^ ARIA role (typically RoleImg)
  , label :: Maybe AriaLabel       -- ^ Accessible name for semantic icons
  , hidden :: AriaHidden           -- ^ Whether to hide from assistive technology
  }

-- | Default accessibility for semantic icons.
-- |
-- | Icons default to visible (not hidden) with RoleImg.
-- | Agents must provide aria-label for semantic icons.
defaultAccessibility :: IconAccessibility
defaultAccessibility =
  { role: RoleImg
  , label: Nothing
  , hidden: AriaHidden false
  }

-- | Accessibility for decorative icons.
-- |
-- | Decorative icons are hidden from assistive technology.
decorativeAccessibility :: IconAccessibility
decorativeAccessibility =
  { role: RoleImg
  , label: Nothing
  , hidden: AriaHidden true
  }

-- | Default icon properties.
-- |
-- | - Medium size (20px)
-- | - Outline style
-- | - 2.0 stroke width
-- | - OnSurface color role
-- | - Visible to assistive technology (semantic by default)
defaultIconProps :: IconProps
defaultIconProps =
  { size: SizeMd
  , style: StyleOutline
  , strokeWidth: 2.0
  , colorRole: RoleOnSurface
  , secondaryRole: Nothing
  , accessibility: defaultAccessibility
  }
