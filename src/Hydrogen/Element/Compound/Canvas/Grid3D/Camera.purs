-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // grid3d // camera
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera integration for 3D grid.
-- |
-- | ## Features
-- |
-- | - Frustum visibility checking
-- | - Grid-to-screen projection (orthographic)

module Hydrogen.Element.Compound.Canvas.Grid3D.Camera
  ( -- * Visibility
    gridVisibleInFrustum
  
  -- * Projection
  , projectGridToScreen
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (&&)
  )

import Data.Array (snoc, index)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Compound.Canvas.Grid3D.Types
  ( extentValue
  )

import Hydrogen.Element.Compound.Canvas.Grid3D.Config
  ( Grid3DConfig
  )

import Hydrogen.Element.Compound.Canvas.Grid3D.Lines
  ( GridLine3D
  , line3DStart
  , line3DEnd
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // camera integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if grid is visible in camera frustum.
-- |
-- | Simple check: is the grid extent within the camera's view?
-- | Full frustum culling would require the Frustum schema type.
gridVisibleInFrustum :: Grid3DConfig 
                     -> { cameraPos :: { x :: Number, y :: Number, z :: Number }
                        , farPlane :: Number 
                        }
                     -> Boolean
gridVisibleInFrustum config camera =
  let 
    extent' = extentValue config.extent
    -- Simple distance check: is camera within 2x grid extent?
    dist = sqrtCam (camera.cameraPos.x * camera.cameraPos.x +
                    camera.cameraPos.y * camera.cameraPos.y +
                    camera.cameraPos.z * camera.cameraPos.z)
  in dist < extent' * 2.0 && camera.farPlane > 1.0

-- | Project 3D grid lines to 2D screen space.
-- |
-- | This is a simplified projection — full projection requires
-- | the camera's view/projection matrices.
projectGridToScreen :: Array GridLine3D 
                    -> { width :: Number, height :: Number }
                    -> Array { x1 :: Number, y1 :: Number, x2 :: Number, y2 :: Number }
projectGridToScreen lines viewport =
  mapCam (projectLine viewport) lines

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Project a 3D line to 2D (simple orthographic for now).
projectLine :: { width :: Number, height :: Number } 
            -> GridLine3D 
            -> { x1 :: Number, y1 :: Number, x2 :: Number, y2 :: Number }
projectLine viewport line =
  let
    start = line3DStart line
    end = line3DEnd line
    -- Simple orthographic: X maps to screen X, Y maps to screen Y
    cx = viewport.width / 2.0
    cy = viewport.height / 2.0
  in { x1: start.x + cx
     , y1: cy - start.y  -- Flip Y for screen coordinates
     , x2: end.x + cx
     , y2: cy - end.y
     }

-- | Square root using Newton's method.
sqrtCam :: Number -> Number
sqrtCam n =
  if n < 0.0 then 0.0
  else newtonCam n (n / 2.0) 0

newtonCam :: Number -> Number -> Int -> Number
newtonCam n guess iterations =
  if iterations > 10 then guess
  else
    let nextGuess = (guess + n / guess) / 2.0
    in if absCam (nextGuess - guess) < 0.0001
       then nextGuess
       else newtonCam n nextGuess (iterations + 1)

absCam :: Number -> Number
absCam n = if n < 0.0 then negCam n else n
  where
  negCam x = 0.0 - x

-- | Map for camera arrays.
mapCam :: forall a b. (a -> b) -> Array a -> Array b
mapCam f arr = mapCamHelper f arr 0 []

mapCamHelper :: forall a b. (a -> b) -> Array a -> Int -> Array b -> Array b
mapCamHelper f arr idx acc =
  case index arr idx of
    Nothing -> acc
    Just x -> mapCamHelper f arr (idx + 1) (snoc acc (f x))
