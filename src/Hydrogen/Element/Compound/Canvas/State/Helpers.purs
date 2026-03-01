-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // element // compound // canvas // state // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State Helpers — Internal helper functions.
-- |
-- | ## Contents
-- |
-- | - Object ID extraction
-- | - Object lookup
-- | - Bounds intersection tests
-- | - Bounds calculation
-- | - Fold utilities
-- |
-- | ## Note
-- |
-- | These are internal helpers used by other State submodules.
-- | They are exported for composition but are not part of the
-- | primary public API.
-- |
-- | ## Dependencies
-- |
-- | - Schema.Graph.Viewport (ViewportBounds)
-- | - Canvas.Types (CanvasObject, CanvasObjectId)

module Hydrogen.Element.Compound.Canvas.State.Helpers
  ( -- * Object Helpers
    getAllObjectIds
  , findObject
  
  -- * Bounds Helpers
  , objectIntersectsRect
  , objectInViewportBounds
  , calculateObjectsBounds
  
  -- * Fold Utilities
  , foldMin
  , foldMax
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (==)
  , (<)
  , (||)
  , not
  , min
  , max
  )

import Data.Array (filter, null, head, foldl)
import Data.Functor (map)
import Data.Maybe (Maybe(Just, Nothing))

-- Viewport state from Schema
import Hydrogen.Schema.Graph.Viewport as VP

-- Canvas-specific types
import Hydrogen.Element.Compound.Canvas.Types as Types

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // object helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all object IDs.
getAllObjectIds :: Array Types.CanvasObject -> Array Types.CanvasObjectId
getAllObjectIds objects = map Types.objectId objects

-- | Find object by ID.
findObject :: Types.CanvasObjectId -> Array Types.CanvasObject -> Maybe Types.CanvasObject
findObject targetId objects =
  head (filter (\obj -> Types.objectId obj == targetId) objects)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // bounds helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if object intersects a rectangle.
objectIntersectsRect :: { x :: Number, y :: Number, width :: Number, height :: Number } -> Types.CanvasObject -> Boolean
objectIntersectsRect rect obj =
  let b = Types.objectBounds obj
  in not (b.x + b.width < rect.x || 
          rect.x + rect.width < b.x ||
          b.y + b.height < rect.y ||
          rect.y + rect.height < b.y)

-- | Check if object is within viewport bounds.
objectInViewportBounds :: VP.ViewportBounds -> Types.CanvasObject -> Boolean
objectInViewportBounds vp obj =
  let b = Types.objectBounds obj
  in VP.boundsIntersect vp 
       { left: b.x
       , top: b.y
       , right: b.x + b.width
       , bottom: b.y + b.height
       }

-- | Calculate bounding box of all objects.
calculateObjectsBounds :: Array Types.CanvasObject -> Maybe VP.ViewportBounds
calculateObjectsBounds objects =
  if null objects
    then Nothing
    else 
      let 
        getBounds = Types.objectBounds
        minX = foldMin (\obj -> (getBounds obj).x) objects
        minY = foldMin (\obj -> (getBounds obj).y) objects
        maxX = foldMax (\obj -> (getBounds obj).x + (getBounds obj).width) objects
        maxY = foldMax (\obj -> (getBounds obj).y + (getBounds obj).height) objects
      in Just { left: minX, top: minY, right: maxX, bottom: maxY }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // fold utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fold to find minimum.
foldMin :: forall a. (a -> Number) -> Array a -> Number
foldMin f arr = case head arr of
  Nothing -> 0.0
  Just first -> foldl (\acc x -> min acc (f x)) (f first) arr

-- | Fold to find maximum.
foldMax :: forall a. (a -> Number) -> Array a -> Number
foldMax f arr = case head arr of
  Nothing -> 0.0
  Just first -> foldl (\acc x -> max acc (f x)) (f first) arr
