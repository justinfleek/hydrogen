-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // element // compound // canvas // selection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Selection — Hit testing, marquee, lasso, and selection handles.
-- |
-- | ## Design Philosophy
-- |
-- | Professional design tools provide multiple selection methods:
-- |
-- | 1. **Click selection**: Point hit test against objects
-- | 2. **Marquee selection**: Rectangular drag selection
-- | 3. **Lasso selection**: Freeform polygon selection
-- | 4. **Selection handles**: Visual transform affordances
-- |
-- | ## Hit Testing
-- |
-- | Hit testing is hierarchical:
-- | 1. Check handles first (if selection exists)
-- | 2. Check objects from front to back (highest zIndex first)
-- | 3. Return first hit, or Nothing
-- |
-- | ## Selection Handles
-- |
-- | Handles provide direct manipulation:
-- | - **Corner handles**: Scale from corner
-- | - **Edge handles**: Scale from edge
-- | - **Rotation handle**: Rotate around center
-- | - **Center handle**: Move object
-- |
-- | ## Coordinate System
-- |
-- | All hit testing operates in canvas space. Screen coordinates must be
-- | converted using viewport transform before testing.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - Selection.Types: Core type definitions
-- | - Selection.HitTest: Hit testing operations
-- | - Selection.Lasso: Lasso path operations
-- | - Selection.Handle: Handle and frame operations
-- | - Selection.Marquee: Marquee state management
-- | - Selection.Operations: High-level selection operations
-- | - Selection.Drag: Handle drag operations
-- | - Selection.Internal: Internal helpers (not re-exported)

module Hydrogen.Element.Compound.Canvas.Selection
  ( module Types
  , module HitTest
  , module Lasso
  , module Handle
  , module Marquee
  , module Operations
  , module Drag
  , module Internal
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- Types
import Hydrogen.Element.Compound.Canvas.Selection.Types
  ( HitTestResult(HitObject, HitHandle, HitGuide, HitNothing)
  , HandleType
      ( HandleTopLeft
      , HandleTopCenter
      , HandleTopRight
      , HandleMiddleLeft
      , HandleMiddleRight
      , HandleBottomLeft
      , HandleBottomCenter
      , HandleBottomRight
      , HandleRotation
      , HandleCenter
      )
  , LassoPath(LassoPath)
  , SelectionHandle
  , SelectionFrame
  , MarqueeState
  , HandleDragState
  ) as Types

-- Hit Testing
import Hydrogen.Element.Compound.Canvas.Selection.HitTest
  ( hitTestPoint
  , hitTestRect
  , hitTestLasso
  , objectContainsPoint
  , objectIntersectsRect
  ) as HitTest

-- Lasso
import Hydrogen.Element.Compound.Canvas.Selection.Lasso
  ( emptyLasso
  , addLassoPoint
  , closeLasso
  , lassoPoints
  , lassoContainsPoint
  , lassoIntersectsRect
  , lassoArea
  ) as Lasso

-- Handle
import Hydrogen.Element.Compound.Canvas.Selection.Handle
  ( handleType
  , handlePosition
  , handleSize
  , handleContainsPoint
  , computeSelectionFrame
  , frameHandles
  , frameBounds
  , frameRotation
  , hitTestHandle
  ) as Handle

-- Marquee
import Hydrogen.Element.Compound.Canvas.Selection.Marquee
  ( startMarquee
  , updateMarquee
  , endMarquee
  , marqueeRect
  , marqueeActive
  ) as Marquee

-- Operations
import Hydrogen.Element.Compound.Canvas.Selection.Operations
  ( selectObjectsInRect
  , selectObjectsInLasso
  , selectTopObjectAtPoint
  , selectAllObjectsAtPoint
  ) as Operations

-- Drag
import Hydrogen.Element.Compound.Canvas.Selection.Drag
  ( startHandleDrag
  , updateHandleDrag
  , endHandleDrag
  , computeTransformFromDrag
  ) as Drag

-- Internal (selectionHandle constructor)
import Hydrogen.Element.Compound.Canvas.Selection.Internal
  ( selectionHandle
  ) as Internal
