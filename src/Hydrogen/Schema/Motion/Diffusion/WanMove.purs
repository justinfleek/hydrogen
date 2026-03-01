-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // motion // diffusion // wanmove
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WanMove trajectory export format types.
-- |
-- | WanMove is a trajectory-based video generation system that uses
-- | point tracks to guide motion in generated videos. This module
-- | provides types for defining flow patterns, morph shapes, and
-- | trajectory data.
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Schemas.Exports.WanMoveSchema` from the
-- | Haskell backend, ensuring type-level compatibility for serialization.
-- |
-- | ## Flow Patterns
-- |
-- | - Spiral: Points rotate inward/outward
-- | - Wave: Sinusoidal motion patterns
-- | - Explosion: Radial expansion from center
-- | - Vortex: Rotating swirl effect
-- | - DataRiver: Flow driven by data values
-- | - Morph: Shape-to-shape transformation
-- | - Swarm: Particle-like collective motion
-- |
-- | ## Constants
-- |
-- | - Max dimension: 8192px (width or height)
-- | - Max points: 10000 per trajectory
-- | - Max frames: 10000 per export
-- | - Max FPS: 120

module Hydrogen.Schema.Motion.Diffusion.WanMove
  ( -- * Flow Patterns
    FlowPattern(..)
  , flowPatternToString
  , flowPatternFromString
  , allFlowPatterns
  
  -- * Morph Shape Types
  , MorphShapeType(..)
  , morphShapeTypeToString
  , morphShapeTypeFromString
  , allMorphShapeTypes
  
  -- * Morph Easing
  , MorphEasing(..)
  , morphEasingToString
  , morphEasingFromString
  , allMorphEasings
  
  -- * Shape Easing (Extended)
  , ShapeEasing(..)
  , shapeEasingToString
  , shapeEasingFromString
  , allShapeEasings
  
  -- * Attractor Types
  , AttractorType(..)
  , attractorTypeToString
  , attractorTypeFromString
  , allAttractorTypes
  
  -- * Data Mapping
  , DataMapping(..)
  , dataMappingToString
  , dataMappingFromString
  , allDataMappings
  
  -- * Force Falloff
  , ForceFalloff(..)
  , forceFalloffToString
  , forceFalloffFromString
  , allForceFalloffs
  
  -- * Initial Distribution
  , InitialDistribution(..)
  , initialDistributionToString
  , initialDistributionFromString
  , allInitialDistributions
  
  -- * Shape Types
  , ShapeType(..)
  , shapeTypeToString
  , shapeTypeFromString
  , allShapeTypes
  
  -- * Constants
  , wanMoveMaxDimension
  , wanMoveMaxPoints
  , wanMoveMaxFrames
  , wanMoveMaxFPS
  
  -- * Trajectory Structures
  , TrackPoint(..)
  , mkTrackPoint
  , WanMoveMetadata(..)
  , mkWanMoveMetadata
  , WanMoveTrajectory(..)
  , mkWanMoveTrajectory
  
  -- * Validation
  , isValidMetadata
  , isValidTrajectory
  , isValidTrackPoint
  
  -- * Default Values
  , defaultFlowPattern
  , defaultMorphShapeType
  , defaultMorphEasing
  , defaultShapeEasing
  , defaultAttractorType
  , defaultDataMapping
  , defaultForceFalloff
  , defaultInitialDistribution
  , defaultShapeType
  , lastFlowPattern
  , lastShapeType
  
  -- * Trajectory Utilities
  , mapTrackPoints
  , flipTrajectoryVertical
  , flipTrajectoryHorizontal
  , translateTrajectory
  , trackPointDistanceSquared
  , flowPatternStrings
  , shapeTypeStrings
  , attractorTypeStrings
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , (==)
  , (/=)
  , (<=)
  , (>=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (&&)
  , (<>)
  , ($)
  , not
  , otherwise
  , bottom
  , top
  , show
  , map
  , negate
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (length) as Array
import Data.Int (toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // flow // patterns
-- ═════════════════════════════════════════════════════════════════════════════

-- | Available flow pattern types for trajectory generation.
-- |
-- | Each pattern defines how points move over time in the generated video.
data FlowPattern
  = FlowSpiral      -- ^ Points rotate inward or outward in spiral
  | FlowWave        -- ^ Sinusoidal wave motion
  | FlowExplosion   -- ^ Radial expansion from center point
  | FlowVortex      -- ^ Rotating swirl with radius variation
  | FlowDataRiver   -- ^ Motion driven by external data values
  | FlowMorph       -- ^ Shape-to-shape transformation
  | FlowSwarm       -- ^ Collective particle-like motion

derive instance eqFlowPattern :: Eq FlowPattern
derive instance ordFlowPattern :: Ord FlowPattern

instance boundedFlowPattern :: Bounded FlowPattern where
  bottom = FlowSpiral
  top = FlowSwarm

instance showFlowPattern :: Show FlowPattern where
  show = flowPatternToString

-- | Convert flow pattern to string identifier.
flowPatternToString :: FlowPattern -> String
flowPatternToString FlowSpiral = "spiral"
flowPatternToString FlowWave = "wave"
flowPatternToString FlowExplosion = "explosion"
flowPatternToString FlowVortex = "vortex"
flowPatternToString FlowDataRiver = "data-river"
flowPatternToString FlowMorph = "morph"
flowPatternToString FlowSwarm = "swarm"

-- | Parse flow pattern from string.
flowPatternFromString :: String -> Maybe FlowPattern
flowPatternFromString "spiral" = Just FlowSpiral
flowPatternFromString "wave" = Just FlowWave
flowPatternFromString "explosion" = Just FlowExplosion
flowPatternFromString "vortex" = Just FlowVortex
flowPatternFromString "data-river" = Just FlowDataRiver
flowPatternFromString "morph" = Just FlowMorph
flowPatternFromString "swarm" = Just FlowSwarm
flowPatternFromString _ = Nothing

-- | All flow patterns for enumeration.
allFlowPatterns :: Array FlowPattern
allFlowPatterns =
  [ FlowSpiral
  , FlowWave
  , FlowExplosion
  , FlowVortex
  , FlowDataRiver
  , FlowMorph
  , FlowSwarm
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // morph // shape // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Morph source and target shape types.
data MorphShapeType
  = MorphCircle   -- ^ Circular arrangement of points
  | MorphGrid     -- ^ Regular grid arrangement
  | MorphText     -- ^ Points arranged to form text
  | MorphCustom   -- ^ User-defined point arrangement

derive instance eqMorphShapeType :: Eq MorphShapeType
derive instance ordMorphShapeType :: Ord MorphShapeType

instance boundedMorphShapeType :: Bounded MorphShapeType where
  bottom = MorphCircle
  top = MorphCustom

instance showMorphShapeType :: Show MorphShapeType where
  show = morphShapeTypeToString

-- | Convert morph shape type to string.
morphShapeTypeToString :: MorphShapeType -> String
morphShapeTypeToString MorphCircle = "circle"
morphShapeTypeToString MorphGrid = "grid"
morphShapeTypeToString MorphText = "text"
morphShapeTypeToString MorphCustom = "custom"

-- | Parse morph shape type from string.
morphShapeTypeFromString :: String -> Maybe MorphShapeType
morphShapeTypeFromString "circle" = Just MorphCircle
morphShapeTypeFromString "grid" = Just MorphGrid
morphShapeTypeFromString "text" = Just MorphText
morphShapeTypeFromString "custom" = Just MorphCustom
morphShapeTypeFromString _ = Nothing

-- | All morph shape types.
allMorphShapeTypes :: Array MorphShapeType
allMorphShapeTypes =
  [ MorphCircle
  , MorphGrid
  , MorphText
  , MorphCustom
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // morph // easing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Easing functions for morph transitions.
data MorphEasing
  = MEasingLinear     -- ^ Constant speed
  | MEasingEaseIn     -- ^ Slow start, fast end
  | MEasingEaseOut    -- ^ Fast start, slow end
  | MEasingEaseInOut  -- ^ Slow start and end

derive instance eqMorphEasing :: Eq MorphEasing
derive instance ordMorphEasing :: Ord MorphEasing

instance boundedMorphEasing :: Bounded MorphEasing where
  bottom = MEasingLinear
  top = MEasingEaseInOut

instance showMorphEasing :: Show MorphEasing where
  show = morphEasingToString

-- | Convert morph easing to string.
morphEasingToString :: MorphEasing -> String
morphEasingToString MEasingLinear = "linear"
morphEasingToString MEasingEaseIn = "ease-in"
morphEasingToString MEasingEaseOut = "ease-out"
morphEasingToString MEasingEaseInOut = "ease-in-out"

-- | Parse morph easing from string.
morphEasingFromString :: String -> Maybe MorphEasing
morphEasingFromString "linear" = Just MEasingLinear
morphEasingFromString "ease-in" = Just MEasingEaseIn
morphEasingFromString "ease-out" = Just MEasingEaseOut
morphEasingFromString "ease-in-out" = Just MEasingEaseInOut
morphEasingFromString _ = Nothing

-- | All morph easing types.
allMorphEasings :: Array MorphEasing
allMorphEasings =
  [ MEasingLinear
  , MEasingEaseIn
  , MEasingEaseOut
  , MEasingEaseInOut
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // shape // easing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extended easing functions for shape morphing.
-- |
-- | Includes elastic and bounce effects not available in basic morph easing.
data ShapeEasing
  = SEasingLinear     -- ^ Constant speed
  | SEasingEaseIn     -- ^ Slow start
  | SEasingEaseOut    -- ^ Slow end
  | SEasingEaseInOut  -- ^ Slow start and end
  | SEasingElastic    -- ^ Overshoot with spring-back
  | SEasingBounce     -- ^ Bounce effect at end

derive instance eqShapeEasing :: Eq ShapeEasing
derive instance ordShapeEasing :: Ord ShapeEasing

instance boundedShapeEasing :: Bounded ShapeEasing where
  bottom = SEasingLinear
  top = SEasingBounce

instance showShapeEasing :: Show ShapeEasing where
  show = shapeEasingToString

-- | Convert shape easing to string.
shapeEasingToString :: ShapeEasing -> String
shapeEasingToString SEasingLinear = "linear"
shapeEasingToString SEasingEaseIn = "ease-in"
shapeEasingToString SEasingEaseOut = "ease-out"
shapeEasingToString SEasingEaseInOut = "ease-in-out"
shapeEasingToString SEasingElastic = "elastic"
shapeEasingToString SEasingBounce = "bounce"

-- | Parse shape easing from string.
shapeEasingFromString :: String -> Maybe ShapeEasing
shapeEasingFromString "linear" = Just SEasingLinear
shapeEasingFromString "ease-in" = Just SEasingEaseIn
shapeEasingFromString "ease-out" = Just SEasingEaseOut
shapeEasingFromString "ease-in-out" = Just SEasingEaseInOut
shapeEasingFromString "elastic" = Just SEasingElastic
shapeEasingFromString "bounce" = Just SEasingBounce
shapeEasingFromString _ = Nothing

-- | All shape easing types.
allShapeEasings :: Array ShapeEasing
allShapeEasings =
  [ SEasingLinear
  , SEasingEaseIn
  , SEasingEaseOut
  , SEasingEaseInOut
  , SEasingElastic
  , SEasingBounce
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // attractor // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Strange attractor types for complex flow patterns.
-- |
-- | These are mathematical attractors that produce deterministic but
-- | chaotic-looking motion patterns.
data AttractorType
  = AttractorLorenz     -- ^ Lorenz butterfly attractor
  | AttractorRossler    -- ^ Rossler attractor
  | AttractorAizawa     -- ^ Aizawa attractor
  | AttractorThomas     -- ^ Thomas attractor
  | AttractorHalvorsen  -- ^ Halvorsen attractor

derive instance eqAttractorType :: Eq AttractorType
derive instance ordAttractorType :: Ord AttractorType

instance boundedAttractorType :: Bounded AttractorType where
  bottom = AttractorLorenz
  top = AttractorHalvorsen

instance showAttractorType :: Show AttractorType where
  show = attractorTypeToString

-- | Convert attractor type to string.
attractorTypeToString :: AttractorType -> String
attractorTypeToString AttractorLorenz = "lorenz"
attractorTypeToString AttractorRossler = "rossler"
attractorTypeToString AttractorAizawa = "aizawa"
attractorTypeToString AttractorThomas = "thomas"
attractorTypeToString AttractorHalvorsen = "halvorsen"

-- | Parse attractor type from string.
attractorTypeFromString :: String -> Maybe AttractorType
attractorTypeFromString "lorenz" = Just AttractorLorenz
attractorTypeFromString "rossler" = Just AttractorRossler
attractorTypeFromString "aizawa" = Just AttractorAizawa
attractorTypeFromString "thomas" = Just AttractorThomas
attractorTypeFromString "halvorsen" = Just AttractorHalvorsen
attractorTypeFromString _ = Nothing

-- | All attractor types.
allAttractorTypes :: Array AttractorType
allAttractorTypes =
  [ AttractorLorenz
  , AttractorRossler
  , AttractorAizawa
  , AttractorThomas
  , AttractorHalvorsen
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // data // mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Data mapping types for data-driven flows.
-- |
-- | Defines how external data values map to motion parameters.
data DataMapping
  = MapSpeed      -- ^ Data controls point speed
  | MapDirection  -- ^ Data controls motion direction
  | MapAmplitude  -- ^ Data controls motion amplitude
  | MapPhase      -- ^ Data controls phase offset
  | MapSize       -- ^ Data controls point size

derive instance eqDataMapping :: Eq DataMapping
derive instance ordDataMapping :: Ord DataMapping

instance boundedDataMapping :: Bounded DataMapping where
  bottom = MapSpeed
  top = MapSize

instance showDataMapping :: Show DataMapping where
  show = dataMappingToString

-- | Convert data mapping to string.
dataMappingToString :: DataMapping -> String
dataMappingToString MapSpeed = "speed"
dataMappingToString MapDirection = "direction"
dataMappingToString MapAmplitude = "amplitude"
dataMappingToString MapPhase = "phase"
dataMappingToString MapSize = "size"

-- | Parse data mapping from string.
dataMappingFromString :: String -> Maybe DataMapping
dataMappingFromString "speed" = Just MapSpeed
dataMappingFromString "direction" = Just MapDirection
dataMappingFromString "amplitude" = Just MapAmplitude
dataMappingFromString "phase" = Just MapPhase
dataMappingFromString "size" = Just MapSize
dataMappingFromString _ = Nothing

-- | All data mapping types.
allDataMappings :: Array DataMapping
allDataMappings =
  [ MapSpeed
  , MapDirection
  , MapAmplitude
  , MapPhase
  , MapSize
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // force // falloff
-- ═════════════════════════════════════════════════════════════════════════════

-- | Falloff types for force points in force field flows.
data ForceFalloff
  = FalloffLinear     -- ^ Force decreases linearly with distance
  | FalloffQuadratic  -- ^ Force decreases with square of distance
  | FalloffNone       -- ^ No falloff (constant force)

derive instance eqForceFalloff :: Eq ForceFalloff
derive instance ordForceFalloff :: Ord ForceFalloff

instance boundedForceFalloff :: Bounded ForceFalloff where
  bottom = FalloffLinear
  top = FalloffNone

instance showForceFalloff :: Show ForceFalloff where
  show = forceFalloffToString

-- | Convert force falloff to string.
forceFalloffToString :: ForceFalloff -> String
forceFalloffToString FalloffLinear = "linear"
forceFalloffToString FalloffQuadratic = "quadratic"
forceFalloffToString FalloffNone = "none"

-- | Parse force falloff from string.
forceFalloffFromString :: String -> Maybe ForceFalloff
forceFalloffFromString "linear" = Just FalloffLinear
forceFalloffFromString "quadratic" = Just FalloffQuadratic
forceFalloffFromString "none" = Just FalloffNone
forceFalloffFromString _ = Nothing

-- | All force falloff types.
allForceFalloffs :: Array ForceFalloff
allForceFalloffs =
  [ FalloffLinear
  , FalloffQuadratic
  , FalloffNone
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // initial // distribution
-- ═════════════════════════════════════════════════════════════════════════════

-- | Initial distribution types for point placement.
data InitialDistribution
  = DistRandom   -- ^ Random placement within bounds
  | DistGrid     -- ^ Regular grid arrangement
  | DistEdge     -- ^ Points along edges
  | DistCenter   -- ^ Points clustered at center

derive instance eqInitialDistribution :: Eq InitialDistribution
derive instance ordInitialDistribution :: Ord InitialDistribution

instance boundedInitialDistribution :: Bounded InitialDistribution where
  bottom = DistRandom
  top = DistCenter

instance showInitialDistribution :: Show InitialDistribution where
  show = initialDistributionToString

-- | Convert initial distribution to string.
initialDistributionToString :: InitialDistribution -> String
initialDistributionToString DistRandom = "random"
initialDistributionToString DistGrid = "grid"
initialDistributionToString DistEdge = "edge"
initialDistributionToString DistCenter = "center"

-- | Parse initial distribution from string.
initialDistributionFromString :: String -> Maybe InitialDistribution
initialDistributionFromString "random" = Just DistRandom
initialDistributionFromString "grid" = Just DistGrid
initialDistributionFromString "edge" = Just DistEdge
initialDistributionFromString "center" = Just DistCenter
initialDistributionFromString _ = Nothing

-- | All initial distribution types.
allInitialDistributions :: Array InitialDistribution
allInitialDistributions =
  [ DistRandom
  , DistGrid
  , DistEdge
  , DistCenter
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // shape // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape types for shape morphing and arrangement.
data ShapeType
  = ShapeCircle   -- ^ Circular arrangement
  | ShapeGrid     -- ^ Grid arrangement
  | ShapeText     -- ^ Text-based arrangement
  | ShapeHeart    -- ^ Heart shape
  | ShapeStar     -- ^ Star shape
  | ShapeSpiral   -- ^ Spiral arrangement
  | ShapeRandom   -- ^ Random placement
  | ShapeCustom   -- ^ User-defined shape

derive instance eqShapeType :: Eq ShapeType
derive instance ordShapeType :: Ord ShapeType

instance boundedShapeType :: Bounded ShapeType where
  bottom = ShapeCircle
  top = ShapeCustom

instance showShapeType :: Show ShapeType where
  show = shapeTypeToString

-- | Convert shape type to string.
shapeTypeToString :: ShapeType -> String
shapeTypeToString ShapeCircle = "circle"
shapeTypeToString ShapeGrid = "grid"
shapeTypeToString ShapeText = "text"
shapeTypeToString ShapeHeart = "heart"
shapeTypeToString ShapeStar = "star"
shapeTypeToString ShapeSpiral = "spiral"
shapeTypeToString ShapeRandom = "random"
shapeTypeToString ShapeCustom = "custom"

-- | Parse shape type from string.
shapeTypeFromString :: String -> Maybe ShapeType
shapeTypeFromString "circle" = Just ShapeCircle
shapeTypeFromString "grid" = Just ShapeGrid
shapeTypeFromString "text" = Just ShapeText
shapeTypeFromString "heart" = Just ShapeHeart
shapeTypeFromString "star" = Just ShapeStar
shapeTypeFromString "spiral" = Just ShapeSpiral
shapeTypeFromString "random" = Just ShapeRandom
shapeTypeFromString "custom" = Just ShapeCustom
shapeTypeFromString _ = Nothing

-- | All shape types.
allShapeTypes :: Array ShapeType
allShapeTypes =
  [ ShapeCircle
  , ShapeGrid
  , ShapeText
  , ShapeHeart
  , ShapeStar
  , ShapeSpiral
  , ShapeRandom
  , ShapeCustom
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum dimension (width or height) in pixels.
wanMoveMaxDimension :: Int
wanMoveMaxDimension = 8192

-- | Maximum number of track points per trajectory.
wanMoveMaxPoints :: Int
wanMoveMaxPoints = 10000

-- | Maximum number of frames per export.
wanMoveMaxFrames :: Int
wanMoveMaxFrames = 10000

-- | Maximum frames per second.
wanMoveMaxFPS :: Number
wanMoveMaxFPS = 120.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // trajectory // structures
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single track point with 2D coordinates.
-- |
-- | Coordinates are normalized to [0, dimension] range.
newtype TrackPoint = TrackPoint
  { x :: Number
  , y :: Number
  }

derive instance eqTrackPoint :: Eq TrackPoint

instance showTrackPoint :: Show TrackPoint where
  show (TrackPoint p) = "(" <> show p.x <> ", " <> show p.y <> ")"

-- | Smart constructor for track point with bounds validation.
mkTrackPoint :: Number -> Number -> Int -> Int -> Maybe TrackPoint
mkTrackPoint x y width height
  | x < 0.0 = Nothing
  | y < 0.0 = Nothing
  | x > Int.toNumber width = Nothing
  | y > Int.toNumber height = Nothing
  | otherwise = Just $ TrackPoint { x, y }

-- | Check if a track point is valid within given dimensions.
isValidTrackPoint :: Int -> Int -> TrackPoint -> Boolean
isValidTrackPoint width height (TrackPoint p) =
  p.x >= 0.0 && p.x <= Int.toNumber width &&
  p.y >= 0.0 && p.y <= Int.toNumber height

-- | WanMove trajectory metadata.
-- |
-- | Contains dimensions and timing information for the trajectory export.
newtype WanMoveMetadata = WanMoveMetadata
  { numPoints :: Int      -- ^ Number of track points
  , numFrames :: Int      -- ^ Number of frames
  , width :: Int          -- ^ Frame width in pixels
  , height :: Int         -- ^ Frame height in pixels
  , fps :: Number         -- ^ Frames per second
  }

derive instance eqWanMoveMetadata :: Eq WanMoveMetadata

instance showWanMoveMetadata :: Show WanMoveMetadata where
  show (WanMoveMetadata m) = 
    "WanMoveMetadata(" <> 
    show m.numPoints <> " points, " <>
    show m.numFrames <> " frames, " <>
    show m.width <> "x" <> show m.height <> " @ " <>
    show m.fps <> "fps)"

-- | Smart constructor for metadata with validation.
mkWanMoveMetadata 
  :: Int -> Int -> Int -> Int -> Number 
  -> Maybe WanMoveMetadata
mkWanMoveMetadata numPoints numFrames width height fps
  | numPoints <= 0 = Nothing
  | numPoints > wanMoveMaxPoints = Nothing
  | numFrames <= 0 = Nothing
  | numFrames > wanMoveMaxFrames = Nothing
  | width <= 0 = Nothing
  | width > wanMoveMaxDimension = Nothing
  | height <= 0 = Nothing
  | height > wanMoveMaxDimension = Nothing
  | fps <= 0.0 = Nothing
  | fps > wanMoveMaxFPS = Nothing
  | otherwise = Just $ WanMoveMetadata
      { numPoints, numFrames, width, height, fps }

-- | Validate metadata against constants.
isValidMetadata :: WanMoveMetadata -> Boolean
isValidMetadata (WanMoveMetadata m) =
  m.numPoints > 0 && m.numPoints <= wanMoveMaxPoints &&
  m.numFrames > 0 && m.numFrames <= wanMoveMaxFrames &&
  m.width > 0 && m.width <= wanMoveMaxDimension &&
  m.height > 0 && m.height <= wanMoveMaxDimension &&
  m.fps > 0.0 && m.fps <= wanMoveMaxFPS

-- | Complete WanMove trajectory structure.
-- |
-- | Contains track data and visibility flags for each point across frames.
newtype WanMoveTrajectory = WanMoveTrajectory
  { tracks :: Array (Array TrackPoint)     -- ^ [numPoints][numFrames]
  , visibility :: Array (Array Boolean)    -- ^ [numPoints][numFrames]
  , metadata :: WanMoveMetadata
  }

derive instance eqWanMoveTrajectory :: Eq WanMoveTrajectory

instance showWanMoveTrajectory :: Show WanMoveTrajectory where
  show (WanMoveTrajectory t) = 
    "WanMoveTrajectory(" <> show t.metadata <> ")"

-- | Smart constructor for trajectory with validation.
mkWanMoveTrajectory 
  :: Array (Array TrackPoint) 
  -> Array (Array Boolean) 
  -> WanMoveMetadata 
  -> Maybe WanMoveTrajectory
mkWanMoveTrajectory tracks visibility metadata
  | not (isValidMetadata metadata) = Nothing
  | Array.length tracks == 0 = Nothing
  | Array.length tracks /= Array.length visibility = Nothing
  | otherwise = Just $ WanMoveTrajectory { tracks, visibility, metadata }

-- | Validate a complete trajectory structure.
isValidTrajectory :: WanMoveTrajectory -> Boolean
isValidTrajectory (WanMoveTrajectory t) =
  isValidMetadata t.metadata &&
  Array.length t.tracks > 0 &&
  Array.length t.tracks == Array.length t.visibility

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // default // values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default flow pattern (first in enumeration).
defaultFlowPattern :: FlowPattern
defaultFlowPattern = bottom

-- | Default morph shape type.
defaultMorphShapeType :: MorphShapeType
defaultMorphShapeType = bottom

-- | Default morph easing.
defaultMorphEasing :: MorphEasing
defaultMorphEasing = bottom

-- | Default shape easing.
defaultShapeEasing :: ShapeEasing
defaultShapeEasing = bottom

-- | Default attractor type.
defaultAttractorType :: AttractorType
defaultAttractorType = bottom

-- | Default data mapping.
defaultDataMapping :: DataMapping
defaultDataMapping = bottom

-- | Default force falloff.
defaultForceFalloff :: ForceFalloff
defaultForceFalloff = bottom

-- | Default initial distribution.
defaultInitialDistribution :: InitialDistribution
defaultInitialDistribution = bottom

-- | Default shape type.
defaultShapeType :: ShapeType
defaultShapeType = bottom

-- | Last flow pattern in enumeration.
lastFlowPattern :: FlowPattern
lastFlowPattern = top

-- | Last shape type in enumeration.
lastShapeType :: ShapeType
lastShapeType = top

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // trajectory // utils
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a function over all track points in a trajectory.
mapTrackPoints :: (TrackPoint -> TrackPoint) -> WanMoveTrajectory -> WanMoveTrajectory
mapTrackPoints f (WanMoveTrajectory t) =
  WanMoveTrajectory 
    { tracks: map (map f) t.tracks
    , visibility: t.visibility
    , metadata: t.metadata
    }

-- | Flip track points vertically (invert Y coordinates).
flipTrajectoryVertical :: Int -> WanMoveTrajectory -> WanMoveTrajectory
flipTrajectoryVertical height traj = mapTrackPoints flipY traj
  where
    h = Int.toNumber height
    flipY (TrackPoint p) = TrackPoint { x: p.x, y: h + negate p.y }

-- | Flip track points horizontally (invert X coordinates).
flipTrajectoryHorizontal :: Int -> WanMoveTrajectory -> WanMoveTrajectory
flipTrajectoryHorizontal width traj = mapTrackPoints flipX traj
  where
    w = Int.toNumber width
    flipX (TrackPoint p) = TrackPoint { x: w + negate p.x, y: p.y }

-- | Get all flow pattern strings for UI dropdowns.
flowPatternStrings :: Array String
flowPatternStrings = map flowPatternToString allFlowPatterns

-- | Get all shape type strings for UI dropdowns.
shapeTypeStrings :: Array String
shapeTypeStrings = map shapeTypeToString allShapeTypes

-- | Get all attractor type strings.
attractorTypeStrings :: Array String
attractorTypeStrings = map attractorTypeToString allAttractorTypes

-- | Translate all track points by an offset.
translateTrajectory :: Number -> Number -> WanMoveTrajectory -> WanMoveTrajectory
translateTrajectory dx dy traj = mapTrackPoints translate traj
  where
    translate (TrackPoint p) = TrackPoint { x: p.x + dx, y: p.y + dy }

-- | Calculate squared distance between two track points.
-- |
-- | Use this when comparing distances (avoids sqrt). 
-- | For actual distance, use sqrt from Data.Number.
trackPointDistanceSquared :: TrackPoint -> TrackPoint -> Number
trackPointDistanceSquared (TrackPoint p1) (TrackPoint p2) =
  let dx = p1.x - p2.x
      dy = p1.y - p2.y
  in dx * dx + dy * dy
