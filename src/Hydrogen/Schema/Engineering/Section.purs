-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // engineering // section
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Section view and hatching primitives for engineering drawings.
-- |
-- | ## What are Section Views?
-- |
-- | Section views show internal features by "cutting" through an object:
-- |
-- | - **Full section**: Cut completely through
-- | - **Half section**: Cut halfway (symmetrical parts)
-- | - **Offset section**: Cut plane changes direction
-- | - **Broken-out section**: Local cutaway
-- | - **Revolved section**: Cross-section rotated into view
-- |
-- | ## Hatching
-- |
-- | Cross-hatching indicates cut surfaces:
-- |
-- | - **Material hatching**: Different patterns for different materials
-- | - **Part hatching**: Adjacent parts have different angles
-- | - **Assembly hatching**: Components distinguished by pattern
-- |
-- | ## Standards
-- |
-- | - **ASME Y14.3**: Multi-view and sectional view drawings
-- | - **ISO 128**: Technical drawings — general principles

module Hydrogen.Schema.Engineering.Section
  ( -- * Section Type
    SectionType(FullSection, HalfSection, OffsetSection, BrokenOutSection, RevolvedSection, RemovedSection, AlignedSection)
  , allSectionTypes
  , sectionTypeDescription
  
  -- * Cut Plane
  , CutPlane(SimplePlane, OffsetPlane, BentPlane)
  , cutPlane
  , offsetCutPlane
  , bentCutPlane
  
  -- * Section Line
  , SectionLine(SectionLine)
  , sectionLine
  , sectionLineWithArrows
  
  -- * Hatch Pattern
  , HatchPattern(SolidFill, GeneralPurpose, Steel, CastIron, Bronze, Brass, Aluminum, Rubber, Plastic, Glass, Concrete, Brick, Stone, Wood, Earth, Water, Insulation, CustomPattern)
  , allHatchPatterns
  , patternDescription
  , patternForMaterial
  
  -- * Hatch Style
  , HatchStyle(HatchStyle)
  , hatchStyle
  , defaultHatch
  , steelHatch
  , brassHatch
  , castIronHatch
  
  -- * Hatched Region
  , HatchedRegion(HatchedRegion)
  , hatchedRegion
  , hatchWithBoundary
  
  -- * Section View
  , SectionView(SectionView)
  , fullSection
  , halfSection
  , offsetSection
  , brokenOutSection
  
  -- * Operations
  , rotateHatch
  , scaleHatch
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
  , (<=)
  , (>=)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (<>)
  )

import Data.Array (length, snoc, foldl) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, sin, cos) as Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // section // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types of section views.
data SectionType
  = FullSection      -- ^ Complete cut through object
  | HalfSection      -- ^ Half cut (for symmetrical parts)
  | OffsetSection    -- ^ Cut plane changes direction
  | BrokenOutSection -- ^ Local cutaway area
  | RevolvedSection  -- ^ Cross-section rotated into view
  | RemovedSection   -- ^ Section shown separately
  | AlignedSection   -- ^ Features rotated to cutting plane

derive instance eqSectionType :: Eq SectionType

instance showSectionType :: Show SectionType where
  show FullSection = "FullSection"
  show HalfSection = "HalfSection"
  show OffsetSection = "OffsetSection"
  show BrokenOutSection = "BrokenOutSection"
  show RevolvedSection = "RevolvedSection"
  show RemovedSection = "RemovedSection"
  show AlignedSection = "AlignedSection"

-- | All section types for enumeration.
allSectionTypes :: Array SectionType
allSectionTypes = 
  [ FullSection, HalfSection, OffsetSection, BrokenOutSection
  , RevolvedSection, RemovedSection, AlignedSection
  ]

-- | Description of section type.
sectionTypeDescription :: SectionType -> String
sectionTypeDescription FullSection = "Complete cut through entire object"
sectionTypeDescription HalfSection = "Half cut for symmetrical parts"
sectionTypeDescription OffsetSection = "Cut plane with one or more bends"
sectionTypeDescription BrokenOutSection = "Local cutaway to show internal feature"
sectionTypeDescription RevolvedSection = "Cross-section rotated 90° into view"
sectionTypeDescription RemovedSection = "Section shown separate from main view"
sectionTypeDescription AlignedSection = "Features rotated to align with cut plane"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cut // plane
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cut plane definition.
data CutPlane
  = SimplePlane
      { startX :: Number
      , startY :: Number
      , endX :: Number
      , endY :: Number
      }
  | OffsetPlane
      { points :: Array { x :: Number, y :: Number }
      }
  | BentPlane
      { points :: Array { x :: Number, y :: Number }
      , bendAngles :: Array Number
      }

derive instance eqCutPlane :: Eq CutPlane

instance showCutPlane :: Show CutPlane where
  show (SimplePlane _) = "SimplePlane"
  show (OffsetPlane p) = "OffsetPlane [" <> show (Array.length p.points) <> " points]"
  show (BentPlane p) = "BentPlane [" <> show (Array.length p.points) <> " points]"

-- | Create simple straight cut plane.
cutPlane :: Number -> Number -> Number -> Number -> CutPlane
cutPlane startX startY endX endY = SimplePlane { startX, startY, endX, endY }

-- | Create offset cut plane with multiple segments.
offsetCutPlane :: Array { x :: Number, y :: Number } -> CutPlane
offsetCutPlane points = OffsetPlane { points }

-- | Create bent cut plane.
bentCutPlane :: Array { x :: Number, y :: Number } -> Array Number -> CutPlane
bentCutPlane points bendAngles = BentPlane { points, bendAngles }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // section // line
-- ═════════════════════════════════════════════════════════════════════════════

-- | Section line (cutting plane indicator on view).
data SectionLine = SectionLine
  { plane :: CutPlane
  , label :: String              -- Section identifier (A-A, B-B, etc.)
  , showArrows :: Boolean
  , arrowDirection :: Number     -- Viewing direction in degrees
  }

derive instance eqSectionLine :: Eq SectionLine

instance showSectionLine :: Show SectionLine where
  show (SectionLine s) = "Section " <> s.label

-- | Create section line.
sectionLine :: CutPlane -> String -> SectionLine
sectionLine plane label = 
  SectionLine { plane, label, showArrows: true, arrowDirection: 0.0 }

-- | Create section line with explicit arrow direction.
sectionLineWithArrows :: CutPlane -> String -> Number -> SectionLine
sectionLineWithArrows plane label arrowDirection =
  SectionLine { plane, label, showArrows: true, arrowDirection }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // hatch // pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard hatching patterns for different materials.
data HatchPattern
  = SolidFill           -- ^ Solid black fill
  | GeneralPurpose      -- ^ 45° parallel lines (general use)
  | Steel               -- ^ 45° parallel lines
  | CastIron            -- ^ Cross-hatch pattern
  | Bronze              -- ^ Diagonal with dots
  | Brass               -- ^ Diagonal lines, different spacing
  | Aluminum            -- ^ Wide-spaced diagonal
  | Rubber              -- ^ Dense diagonal with curves
  | Plastic             -- ^ Stippled pattern
  | Glass               -- ^ Very fine diagonal
  | Concrete            -- ^ Random aggregate pattern
  | Brick               -- ^ Brick pattern
  | Stone               -- ^ Irregular stone pattern
  | Wood                -- ^ Grain pattern
  | Earth               -- ^ Dotted/irregular pattern
  | Water               -- ^ Wavy lines
  | Insulation          -- ^ Zig-zag pattern
  | CustomPattern String -- ^ Named custom pattern

derive instance eqHatchPattern :: Eq HatchPattern

instance showHatchPattern :: Show HatchPattern where
  show SolidFill = "SolidFill"
  show GeneralPurpose = "GeneralPurpose"
  show Steel = "Steel"
  show CastIron = "CastIron"
  show Bronze = "Bronze"
  show Brass = "Brass"
  show Aluminum = "Aluminum"
  show Rubber = "Rubber"
  show Plastic = "Plastic"
  show Glass = "Glass"
  show Concrete = "Concrete"
  show Brick = "Brick"
  show Stone = "Stone"
  show Wood = "Wood"
  show Earth = "Earth"
  show Water = "Water"
  show Insulation = "Insulation"
  show (CustomPattern name) = "Custom(" <> name <> ")"

-- | All standard hatch patterns for enumeration.
allHatchPatterns :: Array HatchPattern
allHatchPatterns = 
  [ SolidFill, GeneralPurpose, Steel, CastIron, Bronze, Brass
  , Aluminum, Rubber, Plastic, Glass, Concrete, Brick
  , Stone, Wood, Earth, Water, Insulation
  ]

-- | Description of hatch pattern.
patternDescription :: HatchPattern -> String
patternDescription SolidFill = "Solid black fill"
patternDescription GeneralPurpose = "45° parallel lines for general use"
patternDescription Steel = "Standard steel section pattern"
patternDescription CastIron = "Cross-hatched cast iron pattern"
patternDescription Bronze = "Bronze alloy pattern with dots"
patternDescription Brass = "Brass alloy diagonal pattern"
patternDescription Aluminum = "Wide-spaced aluminum pattern"
patternDescription Rubber = "Dense rubber/elastomer pattern"
patternDescription Plastic = "Stippled plastic pattern"
patternDescription Glass = "Fine diagonal glass pattern"
patternDescription Concrete = "Aggregate concrete pattern"
patternDescription Brick = "Standard brick pattern"
patternDescription Stone = "Irregular stone pattern"
patternDescription Wood = "Wood grain pattern"
patternDescription Earth = "Earth/soil fill pattern"
patternDescription Water = "Wavy water/liquid pattern"
patternDescription Insulation = "Zig-zag insulation pattern"
patternDescription (CustomPattern name) = "Custom pattern: " <> name

-- | Get standard pattern for a material name.
patternForMaterial :: String -> HatchPattern
patternForMaterial "steel" = Steel
patternForMaterial "iron" = CastIron
patternForMaterial "cast iron" = CastIron
patternForMaterial "bronze" = Bronze
patternForMaterial "brass" = Brass
patternForMaterial "aluminum" = Aluminum
patternForMaterial "aluminium" = Aluminum
patternForMaterial "rubber" = Rubber
patternForMaterial "plastic" = Plastic
patternForMaterial "glass" = Glass
patternForMaterial "concrete" = Concrete
patternForMaterial "brick" = Brick
patternForMaterial "stone" = Stone
patternForMaterial "wood" = Wood
patternForMaterial "earth" = Earth
patternForMaterial "water" = Water
patternForMaterial "insulation" = Insulation
patternForMaterial _ = GeneralPurpose

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // hatch // style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hatch style parameters.
data HatchStyle = HatchStyle
  { pattern :: HatchPattern
  , angle :: Number      -- Rotation angle in degrees
  , scale :: Number      -- Scale factor (1.0 = standard)
  , lineWeight :: Number -- Line thickness in mm
  }

derive instance eqHatchStyle :: Eq HatchStyle

instance showHatchStyle :: Show HatchStyle where
  show (HatchStyle h) = show h.pattern <> " @ " <> show h.angle <> "°"

-- | Create hatch style.
hatchStyle :: HatchPattern -> Number -> Number -> Number -> HatchStyle
hatchStyle pattern angle scale lineWeight =
  HatchStyle { pattern, angle, scale, lineWeight }

-- | Default general-purpose hatch.
defaultHatch :: HatchStyle
defaultHatch = HatchStyle
  { pattern: GeneralPurpose
  , angle: 45.0
  , scale: 1.0
  , lineWeight: 0.18
  }

-- | Steel hatch style.
steelHatch :: HatchStyle
steelHatch = HatchStyle
  { pattern: Steel
  , angle: 45.0
  , scale: 1.0
  , lineWeight: 0.18
  }

-- | Brass hatch style.
brassHatch :: HatchStyle
brassHatch = HatchStyle
  { pattern: Brass
  , angle: 45.0
  , scale: 1.0
  , lineWeight: 0.18
  }

-- | Cast iron hatch style.
castIronHatch :: HatchStyle
castIronHatch = HatchStyle
  { pattern: CastIron
  , angle: 45.0
  , scale: 1.0
  , lineWeight: 0.18
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // hatched // region
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hatched region with boundary.
data HatchedRegion = HatchedRegion
  { style :: HatchStyle
  , boundary :: Maybe (Array { x :: Number, y :: Number })
  , origin :: { x :: Number, y :: Number }
  }

derive instance eqHatchedRegion :: Eq HatchedRegion

instance showHatchedRegion :: Show HatchedRegion where
  show (HatchedRegion h) = "HatchedRegion " <> show h.style

-- | Create hatched region.
hatchedRegion :: HatchStyle -> Number -> Number -> HatchedRegion
hatchedRegion style originX originY =
  HatchedRegion { style, boundary: Nothing, origin: { x: originX, y: originY } }

-- | Create hatched region with explicit boundary.
hatchWithBoundary :: HatchStyle -> Array { x :: Number, y :: Number } -> HatchedRegion
hatchWithBoundary style boundary =
  HatchedRegion { style, boundary: Just boundary, origin: { x: 0.0, y: 0.0 } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // section // view
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete section view definition.
data SectionView = SectionView
  { sectionType :: SectionType
  , sectionLine_ :: SectionLine
  , hatchedRegions :: Array HatchedRegion
  , viewLabel :: String
  }

derive instance eqSectionView :: Eq SectionView

instance showSectionView :: Show SectionView where
  show (SectionView s) = "SectionView " <> s.viewLabel

-- | Create full section view.
fullSection :: SectionLine -> Array HatchedRegion -> String -> SectionView
fullSection sectionLine_ hatchedRegions viewLabel =
  SectionView { sectionType: FullSection, sectionLine_, hatchedRegions, viewLabel }

-- | Create half section view.
halfSection :: SectionLine -> Array HatchedRegion -> String -> SectionView
halfSection sectionLine_ hatchedRegions viewLabel =
  SectionView { sectionType: HalfSection, sectionLine_, hatchedRegions, viewLabel }

-- | Create offset section view.
offsetSection :: SectionLine -> Array HatchedRegion -> String -> SectionView
offsetSection sectionLine_ hatchedRegions viewLabel =
  SectionView { sectionType: OffsetSection, sectionLine_, hatchedRegions, viewLabel }

-- | Create broken-out section view.
brokenOutSection :: SectionLine -> Array HatchedRegion -> String -> SectionView
brokenOutSection sectionLine_ hatchedRegions viewLabel =
  SectionView { sectionType: BrokenOutSection, sectionLine_, hatchedRegions, viewLabel }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate hatch pattern.
rotateHatch :: Number -> HatchStyle -> HatchStyle
rotateHatch angle (HatchStyle h) =
  HatchStyle { pattern: h.pattern, angle: h.angle + angle, scale: h.scale, lineWeight: h.lineWeight }

-- | Scale hatch pattern.
scaleHatch :: Number -> HatchStyle -> HatchStyle
scaleHatch factor (HatchStyle h) =
  HatchStyle { pattern: h.pattern, angle: h.angle, scale: h.scale * factor, lineWeight: h.lineWeight }
