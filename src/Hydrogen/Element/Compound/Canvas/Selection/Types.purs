-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // selection // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for canvas selection system.
-- |
-- | ## Types Defined
-- |
-- | - HitTestResult: Result of hit testing operations
-- | - HandleType: Types of selection handles
-- | - LassoPath: Freeform polygon selection path
-- | - SelectionHandle: Individual handle record
-- | - SelectionFrame: Visual frame around selection
-- | - MarqueeState: Rectangular drag selection state
-- | - HandleDragState: Handle manipulation state
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasObjectId)

module Hydrogen.Element.Compound.Canvas.Selection.Types
  ( -- * Hit Test Result
    HitTestResult(..)
    
  -- * Handle Type
  , HandleType(..)
  
  -- * Lasso Path
  , LassoPath(..)
  
  -- * Selection Handle
  , SelectionHandle
  
  -- * Selection Frame
  , SelectionFrame
  
  -- * Marquee State
  , MarqueeState
  
  -- * Handle Drag State
  , HandleDragState
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
  )

import Data.Array (length)

import Hydrogen.Element.Compound.Canvas.Types as Types

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hit test result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of a hit test.
data HitTestResult
  = HitObject Types.CanvasObjectId     -- ^ Hit a canvas object
  | HitHandle HandleType               -- ^ Hit a selection handle
  | HitGuide String                    -- ^ Hit a guide (guide ID)
  | HitNothing                         -- ^ No hit

derive instance eqHitTestResult :: Eq HitTestResult

instance showHitTestResult :: Show HitTestResult where
  show (HitObject id) = "HitObject(" <> show id <> ")"
  show (HitHandle h) = "HitHandle(" <> show h <> ")"
  show (HitGuide id) = "HitGuide(" <> id <> ")"
  show HitNothing = "HitNothing"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // handle type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of selection handle.
data HandleType
  = HandleTopLeft        -- ^ Top-left corner (scale)
  | HandleTopCenter      -- ^ Top edge center (scale height)
  | HandleTopRight       -- ^ Top-right corner (scale)
  | HandleMiddleLeft     -- ^ Left edge center (scale width)
  | HandleMiddleRight    -- ^ Right edge center (scale width)
  | HandleBottomLeft     -- ^ Bottom-left corner (scale)
  | HandleBottomCenter   -- ^ Bottom edge center (scale height)
  | HandleBottomRight    -- ^ Bottom-right corner (scale)
  | HandleRotation       -- ^ Rotation handle (above selection)
  | HandleCenter         -- ^ Center handle (move)

derive instance eqHandleType :: Eq HandleType
derive instance ordHandleType :: Ord HandleType

instance showHandleType :: Show HandleType where
  show HandleTopLeft = "top-left"
  show HandleTopCenter = "top-center"
  show HandleTopRight = "top-right"
  show HandleMiddleLeft = "middle-left"
  show HandleMiddleRight = "middle-right"
  show HandleBottomLeft = "bottom-left"
  show HandleBottomCenter = "bottom-center"
  show HandleBottomRight = "bottom-right"
  show HandleRotation = "rotation"
  show HandleCenter = "center"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // lasso path
-- ═════════════════════════════════════════════════════════════════════════════

-- | A freeform lasso selection path.
-- |
-- | The path is a sequence of points forming a polygon.
-- | The polygon is implicitly closed between last and first point.
newtype LassoPath = LassoPath
  { points :: Array { x :: Number, y :: Number }
  , closed :: Boolean
  }

derive instance eqLassoPath :: Eq LassoPath

instance showLassoPath :: Show LassoPath where
  show (LassoPath lp) = 
    "Lasso(" <> show (length lp.points) <> " points, " <>
    (if lp.closed then "closed" else "open") <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // selection handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | A selection handle.
type SelectionHandle =
  { handleType :: HandleType
  , x :: Number                  -- Handle center X
  , y :: Number                  -- Handle center Y
  , size :: Number               -- Handle size (width/height)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // selection frame
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual frame around selection with handles.
type SelectionFrame =
  { bounds :: { x :: Number, y :: Number, width :: Number, height :: Number }
  , rotation :: Number           -- Rotation in degrees
  , handles :: Array SelectionHandle
  , handleSize :: Number         -- Size of handles in screen pixels
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // marquee state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of marquee (rectangular drag) selection.
type MarqueeState =
  { active :: Boolean
  , startPoint :: { x :: Number, y :: Number }
  , currentPoint :: { x :: Number, y :: Number }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // handle drag state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of a handle drag operation.
type HandleDragState =
  { handle :: HandleType
  , startPoint :: { x :: Number, y :: Number }
  , currentPoint :: { x :: Number, y :: Number }
  , originalBounds :: { x :: Number, y :: Number, width :: Number, height :: Number }
  }
