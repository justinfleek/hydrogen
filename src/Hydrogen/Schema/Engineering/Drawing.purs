-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // engineering // drawing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Engineering drawing primitives — sheets, title blocks, scales, views.
-- |
-- | ## What is an Engineering Drawing?
-- |
-- | An engineering drawing is a technical document containing:
-- |
-- | - **Sheet**: Standard paper size and orientation
-- | - **Title block**: Drawing metadata and approvals
-- | - **Views**: Orthographic, isometric, section views
-- | - **Scale**: Relationship between drawing and actual size
-- | - **Revision history**: Change tracking
-- |
-- | ## Standards
-- |
-- | - **ANSI Y14**: US drawing standards
-- | - **ISO 5457**: Technical drawings — sizes and layout
-- | - **ISO 7200**: Title blocks
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, drawing primitives enable:
-- | - Automated drawing generation
-- | - Standard template application
-- | - Version control integration
-- | - Manufacturing documentation

module Hydrogen.Schema.Engineering.Drawing
  ( -- * Sheet Size
    SheetSize(..)
  , allSheetSizes
  , sheetDimensions
  , sheetDescription
  
  -- * Sheet Orientation
  , SheetOrientation(..)
  , allSheetOrientations
  
  -- * Drawing Scale
  , DrawingScale(..)
  , scaleRatio
  , fullScale
  , halfScale
  , doubleScale
  , customScale
  , scaleToText
  
  -- * Standard Scales
  , scale1to1
  , scale1to2
  , scale1to5
  , scale1to10
  , scale1to20
  , scale1to50
  , scale1to100
  , scale2to1
  , scale5to1
  , scale10to1
  
  -- * Title Block
  , TitleBlock(..)
  , titleBlock
  , minimalTitleBlock
  
  -- * Revision
  , Revision(..)
  , revision
  , initialRevision
  
  -- * Bill of Materials Entry
  , BomEntry(..)
  , bomEntry
  
  -- * Bill of Materials
  , BillOfMaterials(..)
  , billOfMaterials
  , addBomEntry
  , bomTotal
  
  -- * View Type
  , ViewType(..)
  , allViewTypes
  , viewTypeDescription
  
  -- * Drawing View
  , DrawingView(..)
  , orthographicView
  , isometricView
  , detailView
  
  -- * Drawing Sheet
  , DrawingSheet(..)
  , drawingSheet
  , addView
  
  -- * Operations
  , actualToDrawing
  , drawingToActual
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

import Data.Array (snoc, foldl, length, filter, concat) as Array
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, abs) as Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // sheet // size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard sheet sizes.
data SheetSize
  -- ISO A Series
  = A0 | A1 | A2 | A3 | A4
  -- ANSI Series
  | ANSI_A | ANSI_B | ANSI_C | ANSI_D | ANSI_E
  -- Architectural
  | Arch_A | Arch_B | Arch_C | Arch_D | Arch_E
  -- Custom
  | CustomSize Number Number  -- Width × Height in mm

derive instance eqSheetSize :: Eq SheetSize

instance showSheetSize :: Show SheetSize where
  show A0 = "A0"
  show A1 = "A1"
  show A2 = "A2"
  show A3 = "A3"
  show A4 = "A4"
  show ANSI_A = "ANSI A"
  show ANSI_B = "ANSI B"
  show ANSI_C = "ANSI C"
  show ANSI_D = "ANSI D"
  show ANSI_E = "ANSI E"
  show Arch_A = "Arch A"
  show Arch_B = "Arch B"
  show Arch_C = "Arch C"
  show Arch_D = "Arch D"
  show Arch_E = "Arch E"
  show (CustomSize w h) = show w <> "×" <> show h <> " mm"

-- | All standard sheet sizes for enumeration.
allSheetSizes :: Array SheetSize
allSheetSizes = 
  [ A0, A1, A2, A3, A4
  , ANSI_A, ANSI_B, ANSI_C, ANSI_D, ANSI_E
  , Arch_A, Arch_B, Arch_C, Arch_D, Arch_E
  ]

-- | Get sheet dimensions in mm { width, height }.
sheetDimensions :: SheetSize -> { width :: Number, height :: Number }
sheetDimensions A0 = { width: 841.0, height: 1189.0 }
sheetDimensions A1 = { width: 594.0, height: 841.0 }
sheetDimensions A2 = { width: 420.0, height: 594.0 }
sheetDimensions A3 = { width: 297.0, height: 420.0 }
sheetDimensions A4 = { width: 210.0, height: 297.0 }
sheetDimensions ANSI_A = { width: 216.0, height: 279.0 }   -- 8.5 × 11 in
sheetDimensions ANSI_B = { width: 279.0, height: 432.0 }   -- 11 × 17 in
sheetDimensions ANSI_C = { width: 432.0, height: 559.0 }   -- 17 × 22 in
sheetDimensions ANSI_D = { width: 559.0, height: 864.0 }   -- 22 × 34 in
sheetDimensions ANSI_E = { width: 864.0, height: 1118.0 }  -- 34 × 44 in
sheetDimensions Arch_A = { width: 229.0, height: 305.0 }   -- 9 × 12 in
sheetDimensions Arch_B = { width: 305.0, height: 457.0 }   -- 12 × 18 in
sheetDimensions Arch_C = { width: 457.0, height: 610.0 }   -- 18 × 24 in
sheetDimensions Arch_D = { width: 610.0, height: 914.0 }   -- 24 × 36 in
sheetDimensions Arch_E = { width: 914.0, height: 1219.0 }  -- 36 × 48 in
sheetDimensions (CustomSize w h) = { width: w, height: h }

-- | Description of sheet size.
sheetDescription :: SheetSize -> String
sheetDescription A0 = "ISO A0 (841×1189 mm)"
sheetDescription A1 = "ISO A1 (594×841 mm)"
sheetDescription A2 = "ISO A2 (420×594 mm)"
sheetDescription A3 = "ISO A3 (297×420 mm)"
sheetDescription A4 = "ISO A4 (210×297 mm)"
sheetDescription ANSI_A = "ANSI A / Letter (8.5×11 in)"
sheetDescription ANSI_B = "ANSI B / Tabloid (11×17 in)"
sheetDescription ANSI_C = "ANSI C (17×22 in)"
sheetDescription ANSI_D = "ANSI D (22×34 in)"
sheetDescription ANSI_E = "ANSI E (34×44 in)"
sheetDescription Arch_A = "Architectural A (9×12 in)"
sheetDescription Arch_B = "Architectural B (12×18 in)"
sheetDescription Arch_C = "Architectural C (18×24 in)"
sheetDescription Arch_D = "Architectural D (24×36 in)"
sheetDescription Arch_E = "Architectural E (36×48 in)"
sheetDescription (CustomSize w h) = "Custom (" <> show w <> "×" <> show h <> " mm)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // sheet // orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sheet orientation.
data SheetOrientation
  = Portrait   -- ^ Taller than wide
  | Landscape  -- ^ Wider than tall

derive instance eqSheetOrientation :: Eq SheetOrientation

instance showSheetOrientation :: Show SheetOrientation where
  show Portrait = "Portrait"
  show Landscape = "Landscape"

-- | All orientations for enumeration.
allSheetOrientations :: Array SheetOrientation
allSheetOrientations = [Portrait, Landscape]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // drawing // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drawing scale as ratio.
data DrawingScale = DrawingScale
  { drawing :: Int  -- Drawing units
  , actual :: Int   -- Actual units
  }

derive instance eqDrawingScale :: Eq DrawingScale
derive instance ordDrawingScale :: Ord DrawingScale

instance showDrawingScale :: Show DrawingScale where
  show (DrawingScale s) = show s.drawing <> ":" <> show s.actual

-- | Get scale as decimal ratio.
scaleRatio :: DrawingScale -> Number
scaleRatio (DrawingScale s) = Int.toNumber s.drawing / Int.toNumber s.actual

-- | Full scale (1:1).
fullScale :: DrawingScale
fullScale = DrawingScale { drawing: 1, actual: 1 }

-- | Half scale (1:2).
halfScale :: DrawingScale
halfScale = DrawingScale { drawing: 1, actual: 2 }

-- | Double scale (2:1).
doubleScale :: DrawingScale
doubleScale = DrawingScale { drawing: 2, actual: 1 }

-- | Custom scale.
customScale :: Int -> Int -> DrawingScale
customScale drawing actual = DrawingScale { drawing, actual }

-- | Format scale as text.
scaleToText :: DrawingScale -> String
scaleToText (DrawingScale s) = show s.drawing <> ":" <> show s.actual

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // standard // scales
-- ═════════════════════════════════════════════════════════════════════════════

-- | 1:1 scale.
scale1to1 :: DrawingScale
scale1to1 = fullScale

-- | 1:2 scale.
scale1to2 :: DrawingScale
scale1to2 = halfScale

-- | 1:5 scale.
scale1to5 :: DrawingScale
scale1to5 = DrawingScale { drawing: 1, actual: 5 }

-- | 1:10 scale.
scale1to10 :: DrawingScale
scale1to10 = DrawingScale { drawing: 1, actual: 10 }

-- | 1:20 scale.
scale1to20 :: DrawingScale
scale1to20 = DrawingScale { drawing: 1, actual: 20 }

-- | 1:50 scale.
scale1to50 :: DrawingScale
scale1to50 = DrawingScale { drawing: 1, actual: 50 }

-- | 1:100 scale.
scale1to100 :: DrawingScale
scale1to100 = DrawingScale { drawing: 1, actual: 100 }

-- | 2:1 scale (enlarged).
scale2to1 :: DrawingScale
scale2to1 = doubleScale

-- | 5:1 scale (enlarged).
scale5to1 :: DrawingScale
scale5to1 = DrawingScale { drawing: 5, actual: 1 }

-- | 10:1 scale (enlarged).
scale10to1 :: DrawingScale
scale10to1 = DrawingScale { drawing: 10, actual: 1 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // title // block
-- ═════════════════════════════════════════════════════════════════════════════

-- | Title block with drawing metadata.
data TitleBlock = TitleBlock
  { title :: String
  , drawingNumber :: String
  , revision_ :: Revision
  , scale_ :: DrawingScale
  , date :: String
  , drawnBy :: String
  , checkedBy :: Maybe String
  , approvedBy :: Maybe String
  , company :: String
  , material :: Maybe String
  , finish :: Maybe String
  , weight :: Maybe String
  , sheet :: String  -- "1 of 3" etc.
  }

derive instance eqTitleBlock :: Eq TitleBlock

instance showTitleBlock :: Show TitleBlock where
  show (TitleBlock t) = 
    "TitleBlock { " <> t.drawingNumber <> " - " <> t.title <> " }"

-- | Create full title block.
titleBlock 
  :: String -> String -> Revision -> DrawingScale -> String 
  -> String -> String -> TitleBlock
titleBlock title drawingNumber rev scale_ date drawnBy company =
  TitleBlock
    { title, drawingNumber, revision_: rev, scale_, date, drawnBy
    , checkedBy: Nothing, approvedBy: Nothing, company
    , material: Nothing, finish: Nothing, weight: Nothing
    , sheet: "1 of 1"
    }

-- | Create minimal title block.
minimalTitleBlock :: String -> String -> DrawingScale -> TitleBlock
minimalTitleBlock title drawingNumber scale_ =
  TitleBlock
    { title, drawingNumber, revision_: initialRevision, scale_, date: ""
    , drawnBy: "", checkedBy: Nothing, approvedBy: Nothing, company: ""
    , material: Nothing, finish: Nothing, weight: Nothing
    , sheet: "1 of 1"
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // revision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drawing revision.
data Revision = Revision
  { letter :: String     -- A, B, C... or 1, 2, 3...
  , description :: String
  , date :: String
  , approvedBy :: String
  }

derive instance eqRevision :: Eq Revision

instance showRevision :: Show Revision where
  show (Revision r) = "Rev " <> r.letter

-- | Create revision.
revision :: String -> String -> String -> String -> Revision
revision letter description date approvedBy =
  Revision { letter, description, date, approvedBy }

-- | Initial revision (dash or 0).
initialRevision :: Revision
initialRevision = Revision 
  { letter: "-", description: "Initial release", date: "", approvedBy: "" }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // bom // entry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bill of Materials entry.
data BomEntry = BomEntry
  { itemNumber :: Int
  , partNumber :: String
  , description :: String
  , quantity :: Int
  , material :: Maybe String
  , unitOfMeasure :: String
  }

derive instance eqBomEntry :: Eq BomEntry

instance showBomEntry :: Show BomEntry where
  show (BomEntry b) = 
    show b.itemNumber <> ". " <> b.partNumber <> " ×" <> show b.quantity

-- | Create BOM entry.
bomEntry :: Int -> String -> String -> Int -> BomEntry
bomEntry itemNumber partNumber description quantity =
  BomEntry 
    { itemNumber, partNumber, description, quantity
    , material: Nothing, unitOfMeasure: "EA"
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // bill // of // materials
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bill of Materials.
data BillOfMaterials = BillOfMaterials
  { entries :: Array BomEntry
  , title_ :: String
  }

derive instance eqBillOfMaterials :: Eq BillOfMaterials

instance showBillOfMaterials :: Show BillOfMaterials where
  show (BillOfMaterials b) = 
    "BOM [" <> show (Array.length b.entries) <> " items]"

-- | Create BOM.
billOfMaterials :: String -> BillOfMaterials
billOfMaterials title_ = BillOfMaterials { entries: [], title_ }

-- | Add entry to BOM.
addBomEntry :: BomEntry -> BillOfMaterials -> BillOfMaterials
addBomEntry entry (BillOfMaterials b) =
  BillOfMaterials { entries: Array.snoc b.entries entry, title_: b.title_ }

-- | Total quantity of all items.
bomTotal :: BillOfMaterials -> Int
bomTotal (BillOfMaterials b) =
  Array.foldl (\acc (BomEntry e) -> acc + e.quantity) 0 b.entries

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // view // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types of drawing views.
data ViewType
  = FrontView
  | RearView
  | TopView
  | BottomView
  | LeftView
  | RightView
  | IsometricView_
  | DiametricView
  | TrimetricView
  | DetailView_
  | AuxiliaryView
  | SectionView_

derive instance eqViewType :: Eq ViewType

instance showViewType :: Show ViewType where
  show FrontView = "Front"
  show RearView = "Rear"
  show TopView = "Top"
  show BottomView = "Bottom"
  show LeftView = "Left"
  show RightView = "Right"
  show IsometricView_ = "Isometric"
  show DiametricView = "Diametric"
  show TrimetricView = "Trimetric"
  show DetailView_ = "Detail"
  show AuxiliaryView = "Auxiliary"
  show SectionView_ = "Section"

-- | All view types for enumeration.
allViewTypes :: Array ViewType
allViewTypes = 
  [ FrontView, RearView, TopView, BottomView, LeftView, RightView
  , IsometricView_, DiametricView, TrimetricView
  , DetailView_, AuxiliaryView, SectionView_
  ]

-- | Description of view type.
viewTypeDescription :: ViewType -> String
viewTypeDescription FrontView = "Primary orthographic view"
viewTypeDescription RearView = "View from behind"
viewTypeDescription TopView = "View from above (plan view)"
viewTypeDescription BottomView = "View from below"
viewTypeDescription LeftView = "View from left side"
viewTypeDescription RightView = "View from right side"
viewTypeDescription IsometricView_ = "3D view with equal foreshortening"
viewTypeDescription DiametricView = "3D view with two equal angles"
viewTypeDescription TrimetricView = "3D view with three different angles"
viewTypeDescription DetailView_ = "Enlarged view of specific area"
viewTypeDescription AuxiliaryView = "View perpendicular to inclined surface"
viewTypeDescription SectionView_ = "Cut-away view showing internal features"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // drawing // view
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drawing view with position and scale.
data DrawingView = DrawingView
  { viewType :: ViewType
  , label :: String
  , scale_ :: DrawingScale
  , positionX :: Number
  , positionY :: Number
  , width :: Number
  , height :: Number
  }

derive instance eqDrawingView :: Eq DrawingView

instance showDrawingView :: Show DrawingView where
  show (DrawingView v) = show v.viewType <> " - " <> v.label

-- | Create orthographic view.
orthographicView :: ViewType -> String -> DrawingScale -> Number -> Number -> DrawingView
orthographicView viewType label scale_ positionX positionY =
  DrawingView { viewType, label, scale_, positionX, positionY, width: 100.0, height: 100.0 }

-- | Create isometric view.
isometricView :: String -> DrawingScale -> Number -> Number -> DrawingView
isometricView label scale_ positionX positionY =
  DrawingView 
    { viewType: IsometricView_, label, scale_, positionX, positionY
    , width: 100.0, height: 100.0 
    }

-- | Create detail view.
detailView :: String -> DrawingScale -> Number -> Number -> Number -> DrawingView
detailView label scale_ positionX positionY radius =
  DrawingView 
    { viewType: DetailView_, label, scale_, positionX, positionY
    , width: radius * 2.0, height: radius * 2.0 
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // drawing // sheet
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete drawing sheet.
data DrawingSheet = DrawingSheet
  { size :: SheetSize
  , orientation :: SheetOrientation
  , titleBlock_ :: TitleBlock
  , views :: Array DrawingView
  , bom :: Maybe BillOfMaterials
  }

derive instance eqDrawingSheet :: Eq DrawingSheet

instance showDrawingSheet :: Show DrawingSheet where
  show (DrawingSheet s) = 
    "DrawingSheet " <> show s.size <> " [" <> show (Array.length s.views) <> " views]"

-- | Create drawing sheet.
drawingSheet :: SheetSize -> SheetOrientation -> TitleBlock -> DrawingSheet
drawingSheet size orientation titleBlock_ =
  DrawingSheet { size, orientation, titleBlock_, views: [], bom: Nothing }

-- | Add view to sheet.
addView :: DrawingView -> DrawingSheet -> DrawingSheet
addView view (DrawingSheet s) =
  DrawingSheet 
    { size: s.size, orientation: s.orientation, titleBlock_: s.titleBlock_
    , views: Array.snoc s.views view, bom: s.bom
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert actual dimension to drawing dimension.
actualToDrawing :: DrawingScale -> Number -> Number
actualToDrawing scale actual = actual * scaleRatio scale

-- | Convert drawing dimension to actual dimension.
drawingToActual :: DrawingScale -> Number -> Number
drawingToActual scale drawing = drawing / scaleRatio scale
