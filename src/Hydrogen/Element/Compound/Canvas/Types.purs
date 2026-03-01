-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // compound // canvas // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Types — Leader module re-exporting all canvas type submodules.
-- |
-- | ## Design Philosophy
-- |
-- | The Canvas is the foundational surface for all design tools. It provides:
-- |
-- | - **Infinite space**: Pan in any direction, zoom from 0.1% to 6400%
-- | - **Layer composition**: N-deep stacking with occlusion culling
-- | - **Material backgrounds**: Each component can have diffusion-ready noise
-- | - **Shape masking**: Clip paths, mattes, effects on every layer
-- | - **Hyper-interactivity**: Touch, gesture, haptic, mobile-first
-- |
-- | ## Architecture
-- |
-- | Canvas wraps Schema.Graph.Viewport for viewport math and adds:
-- |
-- | - Tool state (select, pan, zoom, marquee, etc.)
-- | - Selection management (single, multi, group)
-- | - Grid/guide rendering
-- | - Snap behavior
-- | - History (undo/redo stack)
-- |
-- | ## Coordinate Systems
-- |
-- | - **Screen space**: Pixels on device (0,0 = top-left of canvas element)
-- | - **Canvas space**: Infinite coordinate system (can be negative)
-- | - **Object space**: Local to each object (0,0 = object origin)
-- |
-- | Conversion: screen → canvas requires viewport transform.
-- |
-- | ## Module Structure
-- |
-- | - Types.ObjectId — Object identifier (dependency-free)
-- | - Types.Core — CanvasId, tools, selection state
-- | - Types.Object — CanvasObject with compositing
-- | - Types.Grid — Grid and snap configuration
-- | - Types.Guide — Guides, canvas config, bounds
-- | - Types.Selection — Selection operations requiring Object
-- |
-- | ## Compositing
-- |
-- | For compositing types (BlendMode, Mask, ClipPath), import directly:
-- |
-- | - Hydrogen.Schema.Color.Blend (BlendMode, CompositeOp)
-- | - Hydrogen.Schema.Geometry.Mask (Mask)
-- | - Hydrogen.Schema.Geometry.ClipPath (ClipPath)

module Hydrogen.Element.Compound.Canvas.Types
  ( -- * Re-export all submodules
    module ReexportObjectId
  , module ReexportCore
  , module ReexportObject
  , module ReexportGrid
  , module ReexportGuide
  , module ReexportSelection
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // module re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Object ID (must be first - no dependencies)
import Hydrogen.Element.Compound.Canvas.Types.ObjectId 
  ( CanvasObjectId(CanvasObjectId)
  ) as ReexportObjectId

-- Core types (depends on ObjectId)
import Hydrogen.Element.Compound.Canvas.Types.Core
  ( CanvasId(CanvasId)
  , canvasId
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
  ) as ReexportCore

-- Object types (depends on ObjectId, compositing modules)
import Hydrogen.Element.Compound.Canvas.Types.Object
  ( CanvasObject
  , defaultCanvasObject
  , objectId
  , objectBounds
  , objectTransform
  , objectVisible
  , objectLocked
  , objectName
  , objectZIndex
  , objectBlendMode
  , objectOpacity
  , objectClipPath
  , objectMask
  , objectTrackMatteMode
  , objectMatteLayerId
  ) as ReexportObject

-- Grid and snap types (no dependencies on other Types submodules)
import Hydrogen.Element.Compound.Canvas.Types.Grid
  ( GridStyle
    ( GridDots
    , GridLines
    , GridCrosshairs
    , GridIsometric
    , GridPerspective
    )
  , GridConfig
  , defaultGridConfig
  , gridEnabled
  , gridVisible
  , gridSnap
  , withGridSize
  , withGridStyle
  , withGridColor
  , withGridOpacity
  , SnapTarget
    ( SnapGrid
    , SnapObjects
    , SnapGuides
    , SnapPixels
    , SnapKeyObjects
    )
  , SnapConfig
  , defaultSnapConfig
  , snapEnabled
  , snapDistance
  , snapToGrid
  , snapToObjects
  , snapToGuides
  ) as ReexportGrid

-- Guide, config, bounds (depends on Grid)
import Hydrogen.Element.Compound.Canvas.Types.Guide
  ( Guide(Guide)
  , GuideOrientation
    ( GuideHorizontal
    , GuideVertical
    )
  , guideHorizontal
  , guideVertical
  , guidePosition
  , guideId
  , CanvasConfig
  , defaultCanvasConfig
  , withMinZoom
  , withMaxZoom
  , withGridConfig
  , withSnapConfig
  , withBackgroundColor
  , CanvasBounds
    ( Infinite
    , Finite
    )
  , infiniteBounds
  , finiteBounds
  , boundsContains
  ) as ReexportGuide

-- Selection operations (depends on Core and Object)
import Hydrogen.Element.Compound.Canvas.Types.Selection 
  ( selectionBounds
  ) as ReexportSelection
