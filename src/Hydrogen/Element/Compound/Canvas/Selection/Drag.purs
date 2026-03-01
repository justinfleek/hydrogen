-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // selection // drag
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Handle drag operations for selection transforms.
-- |
-- | ## Handle Dragging
-- |
-- | When a user drags a selection handle:
-- | 1. Start drag captures handle type and initial position
-- | 2. Update drag tracks current mouse position
-- | 3. End drag finalizes the transform
-- | 4. computeTransformFromDrag calculates new bounds
-- |
-- | ## Transform Types
-- |
-- | Different handles produce different transforms:
-- | - **Corner handles**: Scale width AND height
-- | - **Edge handles**: Scale only width OR height
-- | - **Rotation handle**: Rotate (bounds unchanged)
-- | - **Center handle**: Move (translate)
-- |
-- | ## Dependencies
-- |
-- | - Selection.Types (HandleType, HandleDragState)

module Hydrogen.Element.Compound.Canvas.Selection.Drag
  ( -- * Lifecycle
    startHandleDrag
  , updateHandleDrag
  , endHandleDrag
  
  -- * Transform Computation
  , computeTransformFromDrag
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  )

import Hydrogen.Element.Compound.Canvas.Selection.Types
  ( HandleType
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
  , HandleDragState
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // lifecycle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start dragging a handle.
startHandleDrag :: HandleType
                -> { x :: Number, y :: Number }
                -> { x :: Number, y :: Number, width :: Number, height :: Number }
                -> HandleDragState
startHandleDrag handle point bounds =
  { handle
  , startPoint: point
  , currentPoint: point
  , originalBounds: bounds
  }

-- | Update handle drag position.
updateHandleDrag :: { x :: Number, y :: Number } -> HandleDragState -> HandleDragState
updateHandleDrag point state = state { currentPoint = point }

-- | End handle drag.
endHandleDrag :: HandleDragState -> HandleDragState
endHandleDrag state = state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // transform computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute transform from handle drag.
-- |
-- | Returns new bounds based on which handle was dragged and how far.
computeTransformFromDrag :: HandleDragState 
                         -> { x :: Number, y :: Number, width :: Number, height :: Number }
computeTransformFromDrag state =
  let
    dx = state.currentPoint.x - state.startPoint.x
    dy = state.currentPoint.y - state.startPoint.y
    ob = state.originalBounds
  in case state.handle of
    HandleTopLeft ->
      { x: ob.x + dx
      , y: ob.y + dy
      , width: ob.width - dx
      , height: ob.height - dy
      }
    HandleTopCenter ->
      { x: ob.x
      , y: ob.y + dy
      , width: ob.width
      , height: ob.height - dy
      }
    HandleTopRight ->
      { x: ob.x
      , y: ob.y + dy
      , width: ob.width + dx
      , height: ob.height - dy
      }
    HandleMiddleLeft ->
      { x: ob.x + dx
      , y: ob.y
      , width: ob.width - dx
      , height: ob.height
      }
    HandleMiddleRight ->
      { x: ob.x
      , y: ob.y
      , width: ob.width + dx
      , height: ob.height
      }
    HandleBottomLeft ->
      { x: ob.x + dx
      , y: ob.y
      , width: ob.width - dx
      , height: ob.height + dy
      }
    HandleBottomCenter ->
      { x: ob.x
      , y: ob.y
      , width: ob.width
      , height: ob.height + dy
      }
    HandleBottomRight ->
      { x: ob.x
      , y: ob.y
      , width: ob.width + dx
      , height: ob.height + dy
      }
    HandleRotation ->
      -- Rotation doesn't change bounds directly
      ob
    HandleCenter ->
      -- Move entire selection
      { x: ob.x + dx
      , y: ob.y + dy
      , width: ob.width
      , height: ob.height
      }
