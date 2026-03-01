-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // element // compound // canvas // state // objects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State Objects — Object and layer management operations.
-- |
-- | ## Contents
-- |
-- | - Add/remove/update objects
-- | - Z-index manipulation
-- | - Layer ordering: bringToFront, sendToBack, moveUp, moveDown
-- | - Config and guides access
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasObject, CanvasObjectId)
-- | - State.Core (CanvasState type)
-- | - State.Helpers (findObject)

module Hydrogen.Element.Compound.Canvas.State.Objects
  ( -- * Config Operations
    getConfig
  , getGridConfig
  , getGuides
  
  -- * Object Operations
  , addObject
  , removeObject
  , updateObject
  , getObjects
  
  -- * Layer Operations
  , setObjectZIndex
  , bringToFront
  , sendToBack
  , moveLayerUp
  , moveLayerDown
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (/=)
  , (==)
  , max
  , min
  )

import Data.Array (filter, snoc, foldl, head)
import Data.Functor (map)
import Data.Maybe (Maybe(Nothing, Just))

-- Canvas-specific types
import Hydrogen.Element.Compound.Canvas.Types as Types

-- Local imports
import Hydrogen.Element.Compound.Canvas.State.Core (CanvasState)
import Hydrogen.Element.Compound.Canvas.State.Helpers (findObject)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // config operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get canvas configuration.
getConfig :: CanvasState -> Types.CanvasConfig
getConfig state = state.config

-- | Get grid configuration.
getGridConfig :: CanvasState -> Types.GridConfig
getGridConfig state = state.config.gridConfig

-- | Get all guides.
getGuides :: CanvasState -> Array Types.Guide
getGuides state = state.guides

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // object/layer operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add an object to the canvas.
-- |
-- | New objects are added at the end (highest z-index by array position).
addObject :: Types.CanvasObject -> CanvasState -> CanvasState
addObject obj state = state { objects = snoc state.objects obj }

-- | Remove an object from the canvas by ID.
removeObject :: Types.CanvasObjectId -> CanvasState -> CanvasState
removeObject objId state = 
  state { objects = filter (\obj -> Types.objectId obj /= objId) state.objects }

-- | Update an object by ID.
-- |
-- | If the object doesn't exist, state is unchanged.
updateObject :: Types.CanvasObjectId -> (Types.CanvasObject -> Types.CanvasObject) -> CanvasState -> CanvasState
updateObject objId updateFn state =
  state { objects = map (\obj -> 
    if Types.objectId obj == objId 
      then updateFn obj 
      else obj
  ) state.objects }

-- | Get all objects.
getObjects :: CanvasState -> Array Types.CanvasObject
getObjects state = state.objects

-- | Set z-index for an object.
setObjectZIndex :: Types.CanvasObjectId -> Int -> CanvasState -> CanvasState
setObjectZIndex objId newZ state =
  updateObject objId (\obj -> obj { zIndex = newZ }) state

-- | Find maximum z-index in canvas.
maxZIndex :: CanvasState -> Int
maxZIndex state = 
  case head state.objects of
    Nothing -> 0
    Just first -> foldl (\acc obj -> max acc (Types.objectZIndex obj)) (Types.objectZIndex first) state.objects

-- | Find minimum z-index in canvas.
minZIndex :: CanvasState -> Int
minZIndex state = 
  case head state.objects of
    Nothing -> 0
    Just first -> foldl (\acc obj -> min acc (Types.objectZIndex obj)) (Types.objectZIndex first) state.objects

-- | Bring object to front (highest z-index).
bringToFront :: Types.CanvasObjectId -> CanvasState -> CanvasState
bringToFront objId state =
  let newZ = maxZIndex state + 1
  in setObjectZIndex objId newZ state

-- | Send object to back (lowest z-index).
sendToBack :: Types.CanvasObjectId -> CanvasState -> CanvasState
sendToBack objId state =
  let newZ = minZIndex state - 1
  in setObjectZIndex objId newZ state

-- | Move layer up (increase z-index by 1).
moveLayerUp :: Types.CanvasObjectId -> CanvasState -> CanvasState
moveLayerUp objId state =
  case findObject objId state.objects of
    Nothing -> state
    Just obj -> setObjectZIndex objId (Types.objectZIndex obj + 1) state

-- | Move layer down (decrease z-index by 1).
moveLayerDown :: Types.CanvasObjectId -> CanvasState -> CanvasState
moveLayerDown objId state =
  case findObject objId state.objects of
    Nothing -> state
    Just obj -> setObjectZIndex objId (Types.objectZIndex obj - 1) state
