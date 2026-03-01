-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // canvas // types // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Core Types — Identity, tools, and selection primitives.
-- |
-- | ## Scope
-- |
-- | This module defines the foundational types for canvas operations:
-- |
-- | - **CanvasId**: Unique identifier for canvas instances
-- | - **CanvasTool**: Available interaction tools
-- | - **SelectionMode**: How selections are combined
-- | - **SelectionState**: Current selection tracking
-- |
-- | ## Dependencies
-- |
-- | - Prelude (basic operations)
-- | - Data.Array (selection manipulation)
-- | - Data.Maybe (optional values)

module Hydrogen.Element.Compound.Canvas.Types.Core
  ( -- * Canvas ID
    CanvasId(CanvasId)
  , canvasId
  
  -- * Tool Types
  , CanvasTool
    ( ToolSelect
    , ToolDirectSelect
    , ToolPan
    , ToolZoom
    , ToolMarquee
    , ToolLasso
    , ToolPen
    , ToolPencil
    , ToolRectangle
    , ToolEllipse
    , ToolLine
    , ToolText
    , ToolEyedropper
    , ToolMove
    , ToolRotate
    , ToolScale
    , ToolCustom
    )
  , isSelectionTool
  , isPanTool
  , isZoomTool
  , isDrawingTool
  
  -- * Selection Types
  , SelectionMode
    ( SelectReplace
    , SelectAdd
    , SelectSubtract
    , SelectToggle
    , SelectIntersect
    )
  , SelectionState
  , emptySelection
  , singleSelection
  , multiSelection
  , addToSelection
  , removeFromSelection
  , clearSelection
  , isSelected
  , selectionCount
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  , (/=)
  , (>)
  )

import Data.Array (length, filter, snoc, elem, index)
import Data.Maybe (Maybe(Just, Nothing))

-- Forward import for ObjectId (needed for selection)
import Hydrogen.Element.Compound.Canvas.Types.ObjectId (CanvasObjectId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // canvas id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a canvas instance.
newtype CanvasId = CanvasId String

derive instance eqCanvasId :: Eq CanvasId
derive instance ordCanvasId :: Ord CanvasId

instance showCanvasId :: Show CanvasId where
  show (CanvasId id) = "CanvasId(" <> id <> ")"

-- | Create a canvas ID.
canvasId :: String -> CanvasId
canvasId = CanvasId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // tool types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Available canvas tools.
-- |
-- | Tools determine how mouse/touch interactions are interpreted.
data CanvasTool
  = ToolSelect           -- ^ Select and transform objects
  | ToolDirectSelect     -- ^ Select individual points/vertices
  | ToolPan              -- ^ Pan the viewport (hand tool)
  | ToolZoom             -- ^ Zoom in/out
  | ToolMarquee          -- ^ Rectangular selection
  | ToolLasso            -- ^ Freeform selection
  | ToolPen              -- ^ Draw bezier paths
  | ToolPencil           -- ^ Freehand drawing
  | ToolRectangle        -- ^ Draw rectangles
  | ToolEllipse          -- ^ Draw ellipses
  | ToolLine             -- ^ Draw lines
  | ToolText             -- ^ Add/edit text
  | ToolEyedropper       -- ^ Sample colors
  | ToolMove             -- ^ Move objects (without selection handles)
  | ToolRotate           -- ^ Rotate objects
  | ToolScale            -- ^ Scale objects
  | ToolCustom String    -- ^ Custom tool with identifier

derive instance eqCanvasTool :: Eq CanvasTool
derive instance ordCanvasTool :: Ord CanvasTool

instance showCanvasTool :: Show CanvasTool where
  show ToolSelect = "select"
  show ToolDirectSelect = "direct-select"
  show ToolPan = "pan"
  show ToolZoom = "zoom"
  show ToolMarquee = "marquee"
  show ToolLasso = "lasso"
  show ToolPen = "pen"
  show ToolPencil = "pencil"
  show ToolRectangle = "rectangle"
  show ToolEllipse = "ellipse"
  show ToolLine = "line"
  show ToolText = "text"
  show ToolEyedropper = "eyedropper"
  show ToolMove = "move"
  show ToolRotate = "rotate"
  show ToolScale = "scale"
  show (ToolCustom name) = "custom:" <> name

-- | Is this a selection tool?
isSelectionTool :: CanvasTool -> Boolean
isSelectionTool ToolSelect = true
isSelectionTool ToolDirectSelect = true
isSelectionTool ToolMarquee = true
isSelectionTool ToolLasso = true
isSelectionTool _ = false

-- | Is this a pan tool?
isPanTool :: CanvasTool -> Boolean
isPanTool ToolPan = true
isPanTool _ = false

-- | Is this a zoom tool?
isZoomTool :: CanvasTool -> Boolean
isZoomTool ToolZoom = true
isZoomTool _ = false

-- | Is this a drawing tool?
isDrawingTool :: CanvasTool -> Boolean
isDrawingTool ToolPen = true
isDrawingTool ToolPencil = true
isDrawingTool ToolRectangle = true
isDrawingTool ToolEllipse = true
isDrawingTool ToolLine = true
isDrawingTool ToolText = true
isDrawingTool _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // selection types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection behavior mode.
data SelectionMode
  = SelectReplace      -- ^ New selection replaces existing
  | SelectAdd          -- ^ Add to existing selection (Shift)
  | SelectSubtract     -- ^ Remove from selection (Alt)
  | SelectToggle       -- ^ Toggle selection state (Ctrl)
  | SelectIntersect    -- ^ Keep only intersection

derive instance eqSelectionMode :: Eq SelectionMode

instance showSelectionMode :: Show SelectionMode where
  show SelectReplace = "replace"
  show SelectAdd = "add"
  show SelectSubtract = "subtract"
  show SelectToggle = "toggle"
  show SelectIntersect = "intersect"

-- | Current selection state.
-- |
-- | Tracks which objects are selected and selection metadata.
type SelectionState =
  { selectedIds :: Array CanvasObjectId
  , primaryId :: Maybe CanvasObjectId    -- The "main" selected object
  , anchorPoint :: Maybe { x :: Number, y :: Number }  -- Transform anchor
  }

-- | Empty selection.
emptySelection :: SelectionState
emptySelection =
  { selectedIds: []
  , primaryId: Nothing
  , anchorPoint: Nothing
  }

-- | Select a single object.
singleSelection :: CanvasObjectId -> SelectionState
singleSelection objId =
  { selectedIds: [objId]
  , primaryId: Just objId
  , anchorPoint: Nothing
  }

-- | Select multiple objects.
multiSelection :: Array CanvasObjectId -> SelectionState
multiSelection ids =
  { selectedIds: ids
  , primaryId: if length ids > 0 then arrayIndex ids 0 else Nothing
  , anchorPoint: Nothing
  }

-- | Add an object to selection.
addToSelection :: CanvasObjectId -> SelectionState -> SelectionState
addToSelection objId state =
  if elem objId state.selectedIds
    then state
    else state { selectedIds = snoc state.selectedIds objId }

-- | Remove an object from selection.
removeFromSelection :: CanvasObjectId -> SelectionState -> SelectionState
removeFromSelection objId state =
  let newIds = filter (\id -> id /= objId) state.selectedIds
      newPrimary = if state.primaryId == Just objId 
                     then arrayIndex newIds 0 
                     else state.primaryId
  in state 
       { selectedIds = newIds
       , primaryId = newPrimary
       }

-- | Clear all selection.
clearSelection :: SelectionState -> SelectionState
clearSelection _ = emptySelection

-- | Check if object is selected.
isSelected :: CanvasObjectId -> SelectionState -> Boolean
isSelected objId state = elem objId state.selectedIds

-- | Get number of selected objects.
selectionCount :: SelectionState -> Int
selectionCount state = length state.selectedIds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safe array indexing using Data.Array.index
arrayIndex :: forall a. Array a -> Int -> Maybe a
arrayIndex = index
