-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // selection // handle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Selection handle operations and frame management.
-- |
-- | ## Selection Handles
-- |
-- | Handles provide direct manipulation:
-- | - **Corner handles**: Scale from corner
-- | - **Edge handles**: Scale from edge
-- | - **Rotation handle**: Rotate around center
-- | - **Center handle**: Move object
-- |
-- | ## Selection Frame
-- |
-- | The frame is the visual bounding box around selected objects,
-- | with handles positioned at corners, edges, and center.
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasObject)
-- | - Selection.Types (HandleType, SelectionHandle, SelectionFrame)
-- | - Selection.Internal (computeBounds, generateHandles)

module Hydrogen.Element.Compound.Canvas.Selection.Handle
  ( -- * Handle Accessors
    handleType
  , handlePosition
  , handleSize
  , handleContainsPoint
  
  -- * Selection Frame
  , computeSelectionFrame
  , frameHandles
  , frameBounds
  , frameRotation
  , hitTestHandle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (==)
  , (&&)
  , (>=)
  , (<=)
  , (+)
  , (-)
  , (/)
  , ($)
  )

import Data.Array (length, filter)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Element.Compound.Canvas.Selection.Types
  ( HandleType
  , SelectionHandle
  , SelectionFrame
  )
import Hydrogen.Element.Compound.Canvas.Selection.Internal
  ( computeBounds
  , generateHandles
  , arrayHead
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // handle accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get handle type.
handleType :: SelectionHandle -> HandleType
handleType h = h.handleType

-- | Get handle position.
handlePosition :: SelectionHandle -> { x :: Number, y :: Number }
handlePosition h = { x: h.x, y: h.y }

-- | Get handle size.
handleSize :: SelectionHandle -> Number
handleSize h = h.size

-- | Check if handle contains a point.
handleContainsPoint :: { x :: Number, y :: Number } -> SelectionHandle -> Boolean
handleContainsPoint point h =
  let halfSize = h.size / 2.0
  in point.x >= h.x - halfSize && point.x <= h.x + halfSize
     && point.y >= h.y - halfSize && point.y <= h.y + halfSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // selection frame
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute selection frame from selected objects.
computeSelectionFrame :: Number -> Array Types.CanvasObject -> Maybe SelectionFrame
computeSelectionFrame hSize objects =
  if length objects == 0
    then Nothing
    else 
      let 
        bounds = computeBounds objects
        handles = generateHandles bounds hSize
      in Just
        { bounds
        , rotation: 0.0  -- Combined rotation is complex; default to 0
        , handles
        , handleSize: hSize
        }

-- | Get frame handles.
frameHandles :: SelectionFrame -> Array SelectionHandle
frameHandles frame = frame.handles

-- | Get frame bounds.
frameBounds :: SelectionFrame -> { x :: Number, y :: Number, width :: Number, height :: Number }
frameBounds frame = frame.bounds

-- | Get frame rotation.
frameRotation :: SelectionFrame -> Number
frameRotation frame = frame.rotation

-- | Hit test selection handles.
-- |
-- | Returns the handle hit, or Nothing if no handle was hit.
hitTestHandle :: { x :: Number, y :: Number } -> SelectionFrame -> Maybe HandleType
hitTestHandle point frame =
  case filter (handleContainsPoint point) frame.handles of
    [] -> Nothing
    hs -> case arrayHead hs of
      Nothing -> Nothing
      Just h -> Just (handleType h)
