-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // gpu // limits // texture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture Dimension Limits — Bounded types for WebGPU texture constraints.
-- |
-- | ## Security Model
-- |
-- | Texture dimensions must be bounded to prevent:
-- | - Memory exhaustion attacks via oversized textures
-- | - Invalid negative dimensions
-- | - Exceeding hardware capabilities
-- |
-- | ## WebGPU Specification Bounds
-- |
-- | These bounds come from the WebGPU spec's guaranteed minimum limits.
-- | Real hardware often supports larger values.
-- |
-- | Reference: https://www.w3.org/TR/webgpu/#limits
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded

module Hydrogen.Schema.GPU.Limits.Texture
  ( -- * 1D Texture Dimension
    TextureDimension1D
  , textureDimension1D
  , clampTextureDimension1D
  , unwrapTextureDimension1D
  , textureDimension1DBounds
  
  -- * 2D Texture Dimension  
  , TextureDimension2D
  , textureDimension2D
  , clampTextureDimension2D
  , unwrapTextureDimension2D
  , textureDimension2DBounds
  
  -- * 3D Texture Dimension
  , TextureDimension3D
  , textureDimension3D
  , clampTextureDimension3D
  , unwrapTextureDimension3D
  , textureDimension3DBounds
  
  -- * Array Layers
  , TextureArrayLayers
  , textureArrayLayers
  , clampTextureArrayLayers
  , unwrapTextureArrayLayers
  , textureArrayLayersBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , IntBounds
  , intBounds
  , clampInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // 1D texture dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum 1D texture dimension.
-- |
-- | Bounds: 1 to 8192 (WebGPU guaranteed minimum)
-- |
-- | Used for 1D texture maps, lookup tables, and gradient textures.
newtype TextureDimension1D = TextureDimension1D Int

derive instance eqTextureDimension1D :: Eq TextureDimension1D
derive instance ordTextureDimension1D :: Ord TextureDimension1D

instance showTextureDimension1D :: Show TextureDimension1D where
  show (TextureDimension1D n) = "TextureDim1D(" <> show n <> ")"

-- | Bounds specification for 1D texture dimension.
textureDimension1DBounds :: IntBounds
textureDimension1DBounds = intBounds 1 8192 Clamps "textureDimension1D" "1D texture dimension (1-8192)"

-- | Smart constructor with validation.
-- |
-- | Returns Nothing for values outside [1, 8192].
textureDimension1D :: Int -> Maybe TextureDimension1D
textureDimension1D n
  | n >= 1 && n <= 8192 = Just (TextureDimension1D n)
  | otherwise = Nothing

-- | Clamping constructor.
-- |
-- | Values below 1 become 1, values above 8192 become 8192.
clampTextureDimension1D :: Int -> TextureDimension1D
clampTextureDimension1D n = TextureDimension1D (clampInt 1 8192 n)

-- | Extract the underlying Int value.
unwrapTextureDimension1D :: TextureDimension1D -> Int
unwrapTextureDimension1D (TextureDimension1D n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // 2D texture dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum 2D texture dimension.
-- |
-- | Bounds: 1 to 8192 (WebGPU guaranteed minimum)
-- |
-- | Real hardware often supports 16384 or higher, but we bound to the
-- | guaranteed minimum for cross-platform safety.
-- |
-- | Used for most textures: diffuse maps, normal maps, sprites, UI elements.
newtype TextureDimension2D = TextureDimension2D Int

derive instance eqTextureDimension2D :: Eq TextureDimension2D
derive instance ordTextureDimension2D :: Ord TextureDimension2D

instance showTextureDimension2D :: Show TextureDimension2D where
  show (TextureDimension2D n) = "TextureDim2D(" <> show n <> ")"

-- | Bounds specification for 2D texture dimension.
textureDimension2DBounds :: IntBounds
textureDimension2DBounds = intBounds 1 8192 Clamps "textureDimension2D" "2D texture dimension (1-8192)"

-- | Smart constructor with validation.
textureDimension2D :: Int -> Maybe TextureDimension2D
textureDimension2D n
  | n >= 1 && n <= 8192 = Just (TextureDimension2D n)
  | otherwise = Nothing

-- | Clamping constructor.
clampTextureDimension2D :: Int -> TextureDimension2D
clampTextureDimension2D n = TextureDimension2D (clampInt 1 8192 n)

-- | Extract the underlying Int value.
unwrapTextureDimension2D :: TextureDimension2D -> Int
unwrapTextureDimension2D (TextureDimension2D n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // 3D texture dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum 3D texture dimension.
-- |
-- | Bounds: 1 to 2048 (WebGPU guaranteed minimum)
-- |
-- | 3D textures are more memory-intensive (dimension^3 scaling), so the
-- | guaranteed minimum is smaller than 2D textures.
-- |
-- | Used for volumetric effects, 3D noise, medical imaging, voxel data.
newtype TextureDimension3D = TextureDimension3D Int

derive instance eqTextureDimension3D :: Eq TextureDimension3D
derive instance ordTextureDimension3D :: Ord TextureDimension3D

instance showTextureDimension3D :: Show TextureDimension3D where
  show (TextureDimension3D n) = "TextureDim3D(" <> show n <> ")"

-- | Bounds specification for 3D texture dimension.
textureDimension3DBounds :: IntBounds
textureDimension3DBounds = intBounds 1 2048 Clamps "textureDimension3D" "3D texture dimension (1-2048)"

-- | Smart constructor with validation.
textureDimension3D :: Int -> Maybe TextureDimension3D
textureDimension3D n
  | n >= 1 && n <= 2048 = Just (TextureDimension3D n)
  | otherwise = Nothing

-- | Clamping constructor.
clampTextureDimension3D :: Int -> TextureDimension3D
clampTextureDimension3D n = TextureDimension3D (clampInt 1 2048 n)

-- | Extract the underlying Int value.
unwrapTextureDimension3D :: TextureDimension3D -> Int
unwrapTextureDimension3D (TextureDimension3D n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // texture array layers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture array layers.
-- |
-- | Bounds: 1 to 256 (WebGPU guaranteed minimum)
-- |
-- | Used for texture arrays (2D array textures, cubemap arrays).
-- | Each layer is a separate 2D slice that can be sampled by index.
-- |
-- | Common uses:
-- | - Sprite atlases with indexed frames
-- | - Terrain texture blending
-- | - Shadow map cascades
newtype TextureArrayLayers = TextureArrayLayers Int

derive instance eqTextureArrayLayers :: Eq TextureArrayLayers
derive instance ordTextureArrayLayers :: Ord TextureArrayLayers

instance showTextureArrayLayers :: Show TextureArrayLayers where
  show (TextureArrayLayers n) = "ArrayLayers(" <> show n <> ")"

-- | Bounds specification for texture array layers.
textureArrayLayersBounds :: IntBounds
textureArrayLayersBounds = intBounds 1 256 Clamps "textureArrayLayers" "Texture array layers (1-256)"

-- | Smart constructor with validation.
textureArrayLayers :: Int -> Maybe TextureArrayLayers
textureArrayLayers n
  | n >= 1 && n <= 256 = Just (TextureArrayLayers n)
  | otherwise = Nothing

-- | Clamping constructor.
clampTextureArrayLayers :: Int -> TextureArrayLayers
clampTextureArrayLayers n = TextureArrayLayers (clampInt 1 256 n)

-- | Extract the underlying Int value.
unwrapTextureArrayLayers :: TextureArrayLayers -> Int
unwrapTextureArrayLayers (TextureArrayLayers n) = n
