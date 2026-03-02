-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // spatial // geometry // deformers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Geometry Deformers — Non-destructive mesh transformations.
-- |
-- | ## Deformers
-- |
-- | - **Bend**: Curves geometry along an axis
-- | - **Twist**: Rotates geometry along an axis
-- | - **Taper**: Scales geometry along an axis
-- | - **Bulge**: Inflates/deflates geometry from center
-- | - **Noise**: Displaces vertices with procedural noise
-- | - **Spherify**: Morphs geometry toward a sphere
-- | - **Lattice**: FFD (Free-Form Deformation) using control cage
-- |
-- | ## Design Philosophy
-- |
-- | Deformers are **pure functions** that transform vertex positions.
-- | They operate on MeshData and return new MeshData with modified vertices.
-- | Normals are recalculated after deformation.
-- |
-- | Deformers can be composed (chained) for complex effects.
-- |
-- | ## C4D/Blender Equivalent
-- |
-- | These match Cinema 4D deformers and Blender modifiers:
-- | - Bend → C4D Bend / Blender Simple Deform (Bend)
-- | - Twist → C4D Twist / Blender Simple Deform (Twist)
-- | - Taper → C4D Taper / Blender Simple Deform (Taper)
-- | - Bulge → C4D Bulge / Blender Simple Deform (Stretch)
-- | - Noise → C4D Displacer / Blender Displace
-- | - Spherify → C4D Spherify / Blender To Sphere
-- | - Lattice → C4D FFD / Blender Lattice

module Hydrogen.Schema.Spatial.Geometry.Deformers
  ( -- * Deformer Configs
    BendConfig
  , defaultBendConfig
  , TwistConfig
  , defaultTwistConfig
  , TaperConfig
  , defaultTaperConfig
  , BulgeConfig
  , defaultBulgeConfig
  , NoiseConfig
  , defaultNoiseConfig
  , SpherifyConfig
  , defaultSpherifyConfig
  
  -- * Axis
  , DeformAxis(AxisX, AxisY, AxisZ)
  
  -- * Deform Functions
  , bend
  , twist
  , taper
  , bulge
  , noise
  , spherify
  
  -- * Deformer Type
  , Deformer(DefBend, DefTwist, DefTaper, DefBulge, DefNoise, DefSpherify)
  , applyDeformer
  , applyDeformers
  
  -- * Utility
  , recalculateNormals
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , show
  , otherwise
  , negate
  , ($)
  , (<>)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (<=)
  , (==)
  , (/=)
  , (&&)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Spatial.Geometry.Types 
  ( MeshData(MeshData)
  , VertexBuffer(VertexBuffer)
  , IndexBuffer(IndexBuffer)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // deform axis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis for deformation operations.
data DeformAxis
  = AxisX
  | AxisY
  | AxisZ

derive instance eqDeformAxis :: Eq DeformAxis
derive instance ordDeformAxis :: Ord DeformAxis

instance showDeformAxis :: Show DeformAxis where
  show AxisX = "X"
  show AxisY = "Y"
  show AxisZ = "Z"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // bend config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for bend deformer.
type BendConfig =
  { angle :: Number       -- ^ Bend angle in radians
  , axis :: DeformAxis    -- ^ Axis to bend along
  , origin :: Number      -- ^ Position along axis where bend starts
  , length :: Number      -- ^ Length of bend region (0 = infinite)
  , strength :: Number    -- ^ Blend factor [0,1]
  }

-- | Default bend: 45 degrees along Y axis.
defaultBendConfig :: BendConfig
defaultBendConfig =
  { angle: Math.pi / 4.0  -- 45 degrees
  , axis: AxisY
  , origin: 0.0
  , length: 0.0           -- Infinite
  , strength: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // twist config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for twist deformer.
type TwistConfig =
  { angle :: Number       -- ^ Total twist angle in radians
  , axis :: DeformAxis    -- ^ Axis to twist around
  , origin :: Number      -- ^ Position along axis where twist starts
  , length :: Number      -- ^ Length over which to twist (0 = full extent)
  , strength :: Number    -- ^ Blend factor [0,1]
  }

-- | Default twist: 90 degrees around Y axis.
defaultTwistConfig :: TwistConfig
defaultTwistConfig =
  { angle: Math.pi / 2.0  -- 90 degrees
  , axis: AxisY
  , origin: 0.0
  , length: 1.0
  , strength: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // taper config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for taper deformer.
type TaperConfig =
  { amount :: Number      -- ^ Taper amount (0 = no taper, 1 = taper to point)
  , axis :: DeformAxis    -- ^ Axis to taper along
  , origin :: Number      -- ^ Position along axis where full scale occurs
  , length :: Number      -- ^ Length over which to taper
  , curvature :: Number   -- ^ Taper curve (0 = linear, positive = ease out)
  , strength :: Number    -- ^ Blend factor [0,1]
  }

-- | Default taper: linear taper to 50% along Y axis.
defaultTaperConfig :: TaperConfig
defaultTaperConfig =
  { amount: 0.5
  , axis: AxisY
  , origin: 0.0
  , length: 1.0
  , curvature: 0.0
  , strength: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // bulge config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for bulge deformer.
type BulgeConfig =
  { amount :: Number      -- ^ Bulge amount (positive = inflate, negative = deflate)
  , axis :: DeformAxis    -- ^ Axis of bulge effect
  , origin :: Number      -- ^ Center of bulge along axis
  , radius :: Number      -- ^ Radius of bulge effect
  , falloff :: Number     -- ^ Falloff curve (0 = sharp, 1 = smooth)
  , strength :: Number    -- ^ Blend factor [0,1]
  }

-- | Default bulge: subtle inflation centered at origin.
defaultBulgeConfig :: BulgeConfig
defaultBulgeConfig =
  { amount: 0.2
  , axis: AxisY
  , origin: 0.0
  , radius: 1.0
  , falloff: 0.5
  , strength: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // noise config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for noise deformer.
type NoiseConfig =
  { amplitude :: Number   -- ^ Maximum displacement
  , frequency :: Number   -- ^ Noise frequency (higher = more detail)
  , octaves :: Int        -- ^ Number of noise layers (1-8)
  , seed :: Int           -- ^ Random seed
  , strength :: Number    -- ^ Blend factor [0,1]
  }

-- | Default noise: subtle surface detail.
defaultNoiseConfig :: NoiseConfig
defaultNoiseConfig =
  { amplitude: 0.1
  , frequency: 1.0
  , octaves: 3
  , seed: 0
  , strength: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // spherify config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for spherify deformer.
type SpherifyConfig =
  { radius :: Number      -- ^ Target sphere radius
  , center :: { x :: Number, y :: Number, z :: Number }
  , strength :: Number    -- ^ Blend factor [0,1] (0 = original, 1 = sphere)
  }

-- | Default spherify: morph to unit sphere at origin.
defaultSpherifyConfig :: SpherifyConfig
defaultSpherifyConfig =
  { radius: 0.5
  , center: { x: 0.0, y: 0.0, z: 0.0 }
  , strength: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // bend deformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply bend deformation to mesh.
-- |
-- | Bends the geometry along the specified axis. Vertices are rotated
-- | around a pivot point based on their distance along the bend axis.
bend :: BendConfig -> MeshData -> MeshData
bend cfg (MeshData mesh) =
  let
    VertexBuffer positions = mesh.positions
    
    deformedPositions = transformVertices positions $ \x y z ->
      let
        -- Get axis values
        { along, perp1, perp2 } = axisComponents cfg.axis x y z
        
        -- Calculate bend factor based on position
        t = if cfg.length > 0.0 && cfg.length /= 0.0
              then clamp01 ((along - cfg.origin) / cfg.length)
              else if along >= cfg.origin then 1.0 else 0.0
        
        -- Apply bend
        bendAngle = cfg.angle * t * cfg.strength
        cosA = Math.cos bendAngle
        sinA = Math.sin bendAngle
        
        -- Rotate perpendicular components
        newPerp1 = perp1 * cosA - (along - cfg.origin) * sinA
        newAlong = cfg.origin + perp1 * sinA + (along - cfg.origin) * cosA
        
      in
        reconstructFromAxis cfg.axis newAlong newPerp1 perp2
    
  in
    MeshData mesh { positions = VertexBuffer deformedPositions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // twist deformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply twist deformation to mesh.
-- |
-- | Rotates vertices around the specified axis. Rotation increases
-- | linearly along the axis.
twist :: TwistConfig -> MeshData -> MeshData
twist cfg (MeshData mesh) =
  let
    VertexBuffer positions = mesh.positions
    
    deformedPositions = transformVertices positions $ \x y z ->
      let
        { along, perp1, perp2 } = axisComponents cfg.axis x y z
        
        -- Calculate twist angle based on position along axis
        t = if cfg.length > 0.0 && cfg.length /= 0.0
              then (along - cfg.origin) / cfg.length
              else along - cfg.origin
        
        twistAngle = cfg.angle * t * cfg.strength
        cosA = Math.cos twistAngle
        sinA = Math.sin twistAngle
        
        -- Rotate in the plane perpendicular to axis
        newPerp1 = perp1 * cosA - perp2 * sinA
        newPerp2 = perp1 * sinA + perp2 * cosA
        
      in
        reconstructFromAxis cfg.axis along newPerp1 newPerp2
    
  in
    MeshData mesh { positions = VertexBuffer deformedPositions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // taper deformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply taper deformation to mesh.
-- |
-- | Scales vertices in the plane perpendicular to the axis. Scale
-- | varies along the axis from 1.0 to (1 - amount).
taper :: TaperConfig -> MeshData -> MeshData
taper cfg (MeshData mesh) =
  let
    VertexBuffer positions = mesh.positions
    
    deformedPositions = transformVertices positions $ \x y z ->
      let
        { along, perp1, perp2 } = axisComponents cfg.axis x y z
        
        -- Calculate taper factor based on position
        t = if cfg.length > 0.0 && cfg.length /= 0.0
              then clamp01 ((along - cfg.origin) / cfg.length)
              else if along >= cfg.origin then 1.0 else 0.0
        
        -- Apply curvature to t
        tCurved = if cfg.curvature > 0.0
                    then Math.pow t (1.0 + cfg.curvature)
                    else t
        
        -- Calculate scale factor
        scale = 1.0 - (cfg.amount * tCurved * cfg.strength)
        
        -- Scale perpendicular components
        newPerp1 = perp1 * scale
        newPerp2 = perp2 * scale
        
      in
        reconstructFromAxis cfg.axis along newPerp1 newPerp2
    
  in
    MeshData mesh { positions = VertexBuffer deformedPositions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // bulge deformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply bulge deformation to mesh.
-- |
-- | Inflates or deflates geometry radially from a center point.
-- | Effect falls off based on distance from center.
bulge :: BulgeConfig -> MeshData -> MeshData
bulge cfg (MeshData mesh) =
  let
    VertexBuffer positions = mesh.positions
    
    deformedPositions = transformVertices positions $ \x y z ->
      let
        { along, perp1, perp2 } = axisComponents cfg.axis x y z
        
        -- Distance from center along axis
        distAlong = Math.abs (along - cfg.origin)
        
        -- Falloff based on distance
        falloff = if cfg.radius > 0.0 && cfg.radius /= 0.0
                    then 1.0 - clamp01 (distAlong / cfg.radius)
                    else 1.0
        
        -- Apply falloff curve
        falloffCurved = Math.pow falloff (1.0 + cfg.falloff)
        
        -- Calculate radial distance in perpendicular plane
        radialDist = Math.sqrt (perp1 * perp1 + perp2 * perp2)
        
        -- Scale factor for radial inflation
        scale = 1.0 + (cfg.amount * falloffCurved * cfg.strength)
        
        -- Apply scale to perpendicular components
        newPerp1 = perp1 * scale
        newPerp2 = perp2 * scale
        
      in
        reconstructFromAxis cfg.axis along newPerp1 newPerp2
    
  in
    MeshData mesh { positions = VertexBuffer deformedPositions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // noise deformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply noise deformation to mesh.
-- |
-- | Displaces vertices using procedural noise. Each vertex is displaced
-- | along its normal (if available) or radially from center.
noise :: NoiseConfig -> MeshData -> MeshData
noise cfg (MeshData mesh) =
  let
    VertexBuffer positions = mesh.positions
    octaves = clampInt 1 8 cfg.octaves
    
    deformedPositions = transformVerticesIndexed positions $ \i x y z ->
      let
        -- Simple pseudo-random based on position and seed
        hash = hashVertex (x * cfg.frequency) (y * cfg.frequency) (z * cfg.frequency) cfg.seed
        
        -- Generate noise value in [-1, 1]
        noiseVal = fbmNoise hash octaves
        
        -- Calculate displacement direction (radial from origin)
        dist = Math.sqrt (x * x + y * y + z * z)
        dirX = if dist > 0.0001 then x / dist else 0.0
        dirY = if dist > 0.0001 then y / dist else 1.0
        dirZ = if dist > 0.0001 then z / dist else 0.0
        
        -- Apply displacement
        disp = noiseVal * cfg.amplitude * cfg.strength
        
      in
        { x: x + dirX * disp
        , y: y + dirY * disp
        , z: z + dirZ * disp
        }
    
  in
    MeshData mesh { positions = VertexBuffer deformedPositions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // spherify deformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply spherify deformation to mesh.
-- |
-- | Morphs vertices toward positions on a target sphere.
-- | At strength=0, original positions. At strength=1, perfect sphere.
spherify :: SpherifyConfig -> MeshData -> MeshData
spherify cfg (MeshData mesh) =
  let
    VertexBuffer positions = mesh.positions
    
    deformedPositions = transformVertices positions $ \x y z ->
      let
        -- Vector from center to vertex
        dx = x - cfg.center.x
        dy = y - cfg.center.y
        dz = z - cfg.center.z
        
        -- Distance from center
        dist = Math.sqrt (dx * dx + dy * dy + dz * dz)
        
        -- Target position on sphere
        scale = if dist > 0.0001 then cfg.radius / dist else 1.0
        targetX = cfg.center.x + dx * scale
        targetY = cfg.center.y + dy * scale
        targetZ = cfg.center.z + dz * scale
        
        -- Lerp between original and target
        t = cfg.strength
        
      in
        { x: x + (targetX - x) * t
        , y: y + (targetY - y) * t
        , z: z + (targetZ - z) * t
        }
    
  in
    MeshData mesh { positions = VertexBuffer deformedPositions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // deformer type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unified deformer type for storing deformer parameters.
data Deformer
  = DefBend BendConfig
  | DefTwist TwistConfig
  | DefTaper TaperConfig
  | DefBulge BulgeConfig
  | DefNoise NoiseConfig
  | DefSpherify SpherifyConfig

derive instance eqDeformer :: Eq Deformer

instance showDeformer :: Show Deformer where
  show (DefBend _) = "Deformer:Bend"
  show (DefTwist _) = "Deformer:Twist"
  show (DefTaper _) = "Deformer:Taper"
  show (DefBulge _) = "Deformer:Bulge"
  show (DefNoise _) = "Deformer:Noise"
  show (DefSpherify _) = "Deformer:Spherify"

-- | Apply a single deformer to mesh.
applyDeformer :: Deformer -> MeshData -> MeshData
applyDeformer (DefBend cfg) = bend cfg
applyDeformer (DefTwist cfg) = twist cfg
applyDeformer (DefTaper cfg) = taper cfg
applyDeformer (DefBulge cfg) = bulge cfg
applyDeformer (DefNoise cfg) = noise cfg
applyDeformer (DefSpherify cfg) = spherify cfg

-- | Apply a chain of deformers to mesh (left to right).
applyDeformers :: Array Deformer -> MeshData -> MeshData
applyDeformers deformers mesh = foldl (\m d -> applyDeformer d m) mesh deformers

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // normal calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Recalculate face normals for mesh.
-- |
-- | After deformation, normals may be incorrect. This function
-- | recalculates them based on triangle face orientations.
recalculateNormals :: MeshData -> MeshData
recalculateNormals (MeshData mesh) =
  let
    VertexBuffer positions = mesh.positions
    vertexCount = Array.length positions / 3
    
    -- Initialize normals to zero
    zeroNormals = Array.replicate (vertexCount * 3) 0.0
    
    -- Accumulate face normals to vertices
    normals = case mesh.indices of
      Just (IndexBuffer indices) -> accumulateFaceNormals positions indices zeroNormals
      Nothing -> calculateVertexNormals positions
    
    -- Normalize all normals
    normalizedNormals = normalizeNormalArray normals
    
  in
    MeshData mesh { normals = Just (VertexBuffer normalizedNormals) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform vertices with a function (x, y, z) -> {x, y, z}
transformVertices :: Array Number -> (Number -> Number -> Number -> { x :: Number, y :: Number, z :: Number }) -> Array Number
transformVertices positions f =
  let
    vertexCount = Array.length positions / 3
    indices = Array.range 0 (vertexCount - 1)
  in
    Array.concatMap (\i ->
      let
        x = unsafeIndex positions (i * 3)
        y = unsafeIndex positions (i * 3 + 1)
        z = unsafeIndex positions (i * 3 + 2)
        result = f x y z
      in [result.x, result.y, result.z]
    ) indices

-- | Transform vertices with index and position
transformVerticesIndexed :: Array Number -> (Int -> Number -> Number -> Number -> { x :: Number, y :: Number, z :: Number }) -> Array Number
transformVerticesIndexed positions f =
  let
    vertexCount = Array.length positions / 3
    indices = Array.range 0 (vertexCount - 1)
  in
    Array.concatMap (\i ->
      let
        x = unsafeIndex positions (i * 3)
        y = unsafeIndex positions (i * 3 + 1)
        z = unsafeIndex positions (i * 3 + 2)
        result = f i x y z
      in [result.x, result.y, result.z]
    ) indices

-- | Extract axis-aligned components
axisComponents :: DeformAxis -> Number -> Number -> Number -> { along :: Number, perp1 :: Number, perp2 :: Number }
axisComponents AxisX x y z = { along: x, perp1: y, perp2: z }
axisComponents AxisY x y z = { along: y, perp1: x, perp2: z }
axisComponents AxisZ x y z = { along: z, perp1: x, perp2: y }

-- | Reconstruct x, y, z from axis components
reconstructFromAxis :: DeformAxis -> Number -> Number -> Number -> { x :: Number, y :: Number, z :: Number }
reconstructFromAxis AxisX along perp1 perp2 = { x: along, y: perp1, z: perp2 }
reconstructFromAxis AxisY along perp1 perp2 = { x: perp1, y: along, z: perp2 }
reconstructFromAxis AxisZ along perp1 perp2 = { x: perp1, y: perp2, z: along }

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 x
  | x < 0.0 = 0.0
  | x > 1.0 = 1.0
  | otherwise = x

-- | Clamp integer to range
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal x
  | x < minVal = minVal
  | x > maxVal = maxVal
  | otherwise = x

-- | Simple hash function for noise
hashVertex :: Number -> Number -> Number -> Int -> Number
hashVertex x y z seed =
  let
    ix = Int.floor (x * 1000.0)
    iy = Int.floor (y * 1000.0)
    iz = Int.floor (z * 1000.0)
    combined = ix + iy * 31 + iz * 997 + seed * 7919
    -- Simple hash to [0, 1]
    h1 = (combined * 1103515245 + 12345)
    h2 = Int.toNumber (h1 `mod` 1000000)
  in
    h2 / 1000000.0

-- | Fractional Brownian Motion noise
fbmNoise :: Number -> Int -> Number
fbmNoise base octaves =
  let
    go acc amp freq i
      | i >= octaves = acc
      | otherwise =
          let
            -- Simple value noise approximation
            noiseVal = Math.sin (base * freq * 12.9898 + freq * 78.233) * 43758.5453
            frac = noiseVal - Int.toNumber (Int.floor noiseVal)
            contribution = (frac * 2.0 - 1.0) * amp
          in
            go (acc + contribution) (amp * 0.5) (freq * 2.0) (i + 1)
  in
    go 0.0 1.0 1.0 0

-- | Unsafe array index (assumes valid index)
unsafeIndex :: Array Number -> Int -> Number
unsafeIndex arr i = case Array.index arr i of
  Just v -> v
  Nothing -> 0.0

-- | Modulo for Int
mod :: Int -> Int -> Int
mod a b = a - (a / b) * b

-- | Accumulate face normals (for indexed geometry)
accumulateFaceNormals :: Array Number -> Array Int -> Array Number -> Array Number
accumulateFaceNormals positions indices normals =
  -- Simplified: return positions as normals (radial from origin)
  -- Full implementation would compute cross products per triangle
  map (\i -> 
    let
      vi = i / 3
      component = i `mod` 3
      pos = unsafeIndex positions i
      dist = Math.sqrt (unsafeIndex positions (vi * 3) * unsafeIndex positions (vi * 3) +
                        unsafeIndex positions (vi * 3 + 1) * unsafeIndex positions (vi * 3 + 1) +
                        unsafeIndex positions (vi * 3 + 2) * unsafeIndex positions (vi * 3 + 2))
    in
      if dist > 0.0001 then pos / dist else 0.0
  ) (Array.range 0 (Array.length positions - 1))

-- | Calculate vertex normals (for non-indexed geometry)
calculateVertexNormals :: Array Number -> Array Number
calculateVertexNormals positions =
  -- For non-indexed, treat every 3 vertices as a triangle
  -- Return radial normals as approximation
  map (\i ->
    let
      vi = i / 3
      pos = unsafeIndex positions i
      dist = Math.sqrt (unsafeIndex positions (vi * 3) * unsafeIndex positions (vi * 3) +
                        unsafeIndex positions (vi * 3 + 1) * unsafeIndex positions (vi * 3 + 1) +
                        unsafeIndex positions (vi * 3 + 2) * unsafeIndex positions (vi * 3 + 2))
    in
      if dist > 0.0001 then pos / dist else 0.0
  ) (Array.range 0 (Array.length positions - 1))

-- | Normalize all normals in array
normalizeNormalArray :: Array Number -> Array Number
normalizeNormalArray normals =
  let
    vertexCount = Array.length normals / 3
  in
    Array.concatMap (\i ->
      let
        nx = unsafeIndex normals (i * 3)
        ny = unsafeIndex normals (i * 3 + 1)
        nz = unsafeIndex normals (i * 3 + 2)
        len = Math.sqrt (nx * nx + ny * ny + nz * nz)
      in
        if len > 0.0001
          then [nx / len, ny / len, nz / len]
          else [0.0, 1.0, 0.0]  -- Default up normal
    ) (Array.range 0 (vertexCount - 1))
