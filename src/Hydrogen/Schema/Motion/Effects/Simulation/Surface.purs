-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // motion // effects // surface
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Surface Effects — Shatter and Card Dance.
-- |
-- | ## After Effects Parity
-- |
-- | - **Shatter**: Glass/surface shatter effect
-- | - **Card Dance**: Grid-based card animation
-- |
-- | ## GPU Simulation
-- |
-- | Surface fragmentation uses GPU tessellation in the runtime.

module Hydrogen.Schema.Motion.Effects.Simulation.Surface
  ( -- * Shatter
    ShatterEffect
  , ShatterShape(..)
  , ShatterForce(..)
  , defaultShatter
  , shatterWithForce
  
  -- * Card Dance
  , CardDanceEffect
  , CardDanceAxis(..)
  , defaultCardDance
  , cardDanceWithRows
  
  -- * Serialization
  , shatterShapeToString
  , shatterForceToString
  , cardDanceAxisToString
  
  -- * Effect Names
  , shatterEffectName
  , cardDanceEffectName
  
  -- * Effect Descriptions
  , describeShatter
  , describeCardDance
  
  -- * Queries
  , isShatterRadial
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (<)
  , (>)
  , negate
  , show
  , otherwise
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // shatter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shatter shape — pattern of breakage.
data ShatterShape
  = SSGlass             -- ^ Glass-like shards
  | SSBrick             -- ^ Brick pattern
  | SSPuzzle            -- ^ Puzzle pieces
  | SSTriangles         -- ^ Triangle shards
  | SSCustom            -- ^ Custom pattern from layer

derive instance eqShatterShape :: Eq ShatterShape
derive instance ordShatterShape :: Ord ShatterShape

instance showShatterShape :: Show ShatterShape where
  show SSGlass = "glass"
  show SSBrick = "brick"
  show SSPuzzle = "puzzle"
  show SSTriangles = "triangles"
  show SSCustom = "custom"

-- | Shatter force — what drives the shattering.
data ShatterForce
  = SFGradient          -- ^ Gradient map force
  | SFRadius            -- ^ Radial explosion
  | SFDepth             -- ^ Depth-based

derive instance eqShatterForce :: Eq ShatterForce
derive instance ordShatterForce :: Ord ShatterForce

instance showShatterForce :: Show ShatterForce where
  show SFGradient = "gradient"
  show SFRadius = "radius"
  show SFDepth = "depth"

-- | Shatter Effect — glass/surface break simulation.
-- |
-- | ## AE Properties
-- |
-- | Shatters layer into pieces based on force.
type ShatterEffect =
  { -- View
    renderMode :: Int                -- ^ 0=Rendered, 1=Wireframe, 2=Front
    
  -- Shape
  , shatterShape :: ShatterShape     -- ^ Breakage pattern
  , repetitions :: Number            -- ^ Pattern repetitions (1-100)
  , extrusionDepth :: Number         -- ^ 3D extrusion (0-100)
  
  -- Force
  , forceType :: ShatterForce        -- ^ Force source
  , forcePosition :: Point2D         -- ^ Force center
  , forceStrength :: Number          -- ^ Force strength (0-100)
  , forceRadius :: Number            -- ^ Force radius (0-1000)
  
  -- Physics
  , gravity :: Number                -- ^ Gravity strength (0-100)
  , gravityDirection :: Number       -- ^ Gravity angle (0-360)
  , randomness :: Number             -- ^ Random variation (0-100)
  
  -- Rendering
  , lightingType :: Int              -- ^ 0=First, 1=None
  , ambientLight :: Number           -- ^ Ambient intensity (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default shatter: glass pattern, radial force.
defaultShatter :: ShatterEffect
defaultShatter =
  { renderMode: 0
  , shatterShape: SSGlass
  , repetitions: 10.0
  , extrusionDepth: 10.0
  , forceType: SFRadius
  , forcePosition: point2D 100.0 100.0
  , forceStrength: 50.0
  , forceRadius: 100.0
  , gravity: 50.0
  , gravityDirection: 180.0
  , randomness: 50.0
  , lightingType: 0
  , ambientLight: 50.0
  , randomSeed: 0
  }

-- | Create shatter with specific force.
shatterWithForce :: ShatterForce -> Number -> Number -> ShatterEffect
shatterWithForce force strength rad =
  { renderMode: 0
  , shatterShape: SSGlass
  , repetitions: 10.0
  , extrusionDepth: 10.0
  , forceType: force
  , forcePosition: point2D 100.0 100.0
  , forceStrength: clampNumber 0.0 100.0 strength
  , forceRadius: clampNumber 0.0 1000.0 rad
  , gravity: 50.0
  , gravityDirection: 180.0
  , randomness: 50.0
  , lightingType: 0
  , ambientLight: 50.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // card // dance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card dance axis — which axis to animate.
data CardDanceAxis
  = CDAPosition         -- ^ Position offset
  | CDARotation         -- ^ Rotation
  | CDAScale            -- ^ Scale

derive instance eqCardDanceAxis :: Eq CardDanceAxis
derive instance ordCardDanceAxis :: Ord CardDanceAxis

instance showCardDanceAxis :: Show CardDanceAxis where
  show CDAPosition = "position"
  show CDARotation = "rotation"
  show CDAScale = "scale"

-- | Card Dance Effect — grid-based card animation.
-- |
-- | ## AE Properties
-- |
-- | Divides layer into cards and animates them based on gradient.
type CardDanceEffect =
  { -- Grid
    rows :: Int                      -- ^ Number of rows (1-200)
  , columns :: Int                   -- ^ Number of columns (1-200)
  
  -- Position
  , positionX :: Number              -- ^ X position multiplier (-1000 to 1000)
  , positionY :: Number              -- ^ Y position multiplier (-1000 to 1000)
  , positionZ :: Number              -- ^ Z position multiplier (-1000 to 1000)
  
  -- Rotation
  , rotationX :: Number              -- ^ X rotation multiplier (-1000 to 1000)
  , rotationY :: Number              -- ^ Y rotation multiplier (-1000 to 1000)
  , rotationZ :: Number              -- ^ Z rotation multiplier (-1000 to 1000)
  
  -- Scale
  , scaleX :: Number                 -- ^ X scale multiplier (-1000 to 1000)
  , scaleY :: Number                 -- ^ Y scale multiplier (-1000 to 1000)
  
  -- Camera
  , cameraPosition :: Vec3 Number    -- ^ Camera position
  , focalLength :: Number            -- ^ Camera focal length (1-1000)
  
  -- Control
  , gradientLayer :: Int             -- ^ Source gradient layer index
  }

-- | Default card dance: 10x10 grid.
defaultCardDance :: CardDanceEffect
defaultCardDance =
  { rows: 10
  , columns: 10
  , positionX: 0.0
  , positionY: 0.0
  , positionZ: 100.0
  , rotationX: 0.0
  , rotationY: 0.0
  , rotationZ: 0.0
  , scaleX: 100.0
  , scaleY: 100.0
  , cameraPosition: vec3 0.0 0.0 (negate 500.0)
  , focalLength: 50.0
  , gradientLayer: 0
  }

-- | Create card dance with specific grid size.
cardDanceWithRows :: Int -> Int -> CardDanceEffect
cardDanceWithRows r c =
  { rows: clampInt 1 200 r
  , columns: clampInt 1 200 c
  , positionX: 0.0
  , positionY: 0.0
  , positionZ: 100.0
  , rotationX: 0.0
  , rotationY: 0.0
  , rotationZ: 0.0
  , scaleX: 100.0
  , scaleY: 100.0
  , cameraPosition: vec3 0.0 0.0 (negate 500.0)
  , focalLength: 50.0
  , gradientLayer: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert ShatterShape to string.
shatterShapeToString :: ShatterShape -> String
shatterShapeToString ss = show ss

-- | Convert ShatterForce to string.
shatterForceToString :: ShatterForce -> String
shatterForceToString sf = show sf

-- | Convert CardDanceAxis to string.
cardDanceAxisToString :: CardDanceAxis -> String
cardDanceAxisToString cda = show cda

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Shatter.
shatterEffectName :: ShatterEffect -> String
shatterEffectName _ = "Shatter"

-- | Effect name for Card Dance.
cardDanceEffectName :: CardDanceEffect -> String
cardDanceEffectName _ = "Card Dance"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // effect // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create shatter description.
describeShatter :: ShatterEffect -> String
describeShatter e =
  "Shatter(" <> show e.shatterShape <> ", force: " <>
  show e.forceStrength <> "%)"

-- | Create card dance description.
describeCardDance :: CardDanceEffect -> String
describeCardDance e =
  "CardDance(" <> show e.rows <> "x" <> show e.columns <> " grid)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if shatter force is radial.
isShatterRadial :: ShatterEffect -> Boolean
isShatterRadial e = case e.forceType of
  SFRadius -> true
  _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp integer to bounds.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n
