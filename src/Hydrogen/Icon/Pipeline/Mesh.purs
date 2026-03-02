-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // icon // pipeline // mesh
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Icon 3D Mesh Generation — Convert 2D icons to 3D extruded meshes.
-- |
-- | This module provides the bridge between 2D IconPath and 3D Mesh3D:
-- |
-- | ```
-- | IconPath ──► Shape2D ──► ExtrudeMeshParams ──► Mesh3D
-- | ```
-- |
-- | ## Pipeline
-- |
-- | 1. **Path → Profile**: Convert SVG path commands to 2D profile points
-- | 2. **Profile → Shape**: Build Shape2D with contour and optional holes
-- | 3. **Shape → Mesh**: Extrude to 3D with depth, bevel, segments
-- |
-- | ## Research References
-- |
-- | - Bezier subdivision for smooth path sampling
-- | - Marching squares for implicit surface conversion
-- | - Loop subdivision for mesh refinement

module Hydrogen.Icon.Pipeline.Mesh
  ( -- * Mesh Generation
    iconToMesh3D
  , pathToMesh3D
  , partToMesh3D
  
  -- * Path → Profile Conversion
  , pathToProfile
  , pathToPoint2DProfile
  , samplePath
  , samplePathArcLength
  
  -- * Interpolation
  , interpolatePoints
  , interpolateTwo
  
  -- * Shape Construction
  , profileToShape2D
  , profileWithHoles
  
  -- * Extrusion Parameters
  , IconExtrusionParams(..)
  , defaultExtrusionParams
  , iconExtrusionParams
  
  -- * Bevel Configuration
  , BevelConfig(..)
  , noBevel
  , subtleBevel
  , mediumBevel
  , heavyBevel
  
  -- * Mesh Output
  , IconMesh3D
  , iconMesh3D
  , meshToElement
  
  -- * Material Assignment
  , MeshMaterial
  , assignMaterial
  , assignBrandMaterial
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (/=)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (<>)
  , map
  , bind
  , pure
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  )
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array (head, length, drop, index, snoc) as Array
import Data.Tuple (Tuple(..))
import Data.Number (sqrt) as Number

import Hydrogen.Schema.Geometry.Path.Types (Path(..), PathCommand(..))
import Hydrogen.Schema.Geometry.Path.Query (firstPoint, lastPoint)
import Hydrogen.Schema.Geometry.Point (Point2D, getX, getY)
import Hydrogen.Schema.Dimension.Physical.SI (Meter, meter, unwrapMeter)
import Hydrogen.Schema.Dimension.Device.Types (Pixel(Pixel))
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees)

import Hydrogen.GPU.Scene3D.Mesh
  ( Mesh3D(..)
  , Shape2D(..)
  , Point2DProfile
  , ExtrudeMeshParams
  , extrudeMesh3D
  )

import Hydrogen.Icon.Types
  ( IconDefinition(..)
  , IconPath(..)
  , IconPart
  , IconStyle(..)
  )

import Hydrogen.Icon.Brand
  ( ThemedIcon
  , resolveIconColor
  , IconTheme(..)
  , iconThemeMode
  , iconThemeColors
  )

import Hydrogen.Schema.Brand.ColorSystem (ThemedColorSystem)
import Hydrogen.Schema.Brand.Token.Color (ColorRole)
import Hydrogen.Schema.Brand.ColorSystem (PaletteMode(..))

import Hydrogen.Schema.Color.OKLCH (OKLCH)
import Hydrogen.GPU.Scene3D.Material (Material3D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // extrusion // parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extrusion parameters for icon mesh generation.
newtype IconExtrusionParams = IconExtrusionParams
  { depth :: Meter              -- ^ Extrusion depth (Z thickness)
  , bevel :: BevelConfig        -- ^ Bevel configuration
  , curveSegments :: Int        -- ^ Curve subdivision
  , depthSegments :: Int        -- ^ Depth subdivision
  }

-- | Bevel configuration for rounded edges.
data BevelConfig
  = BevelNone
  | BevelSubtle Meter Meter Int    -- ^ thickness, size, segments
  | BevelMedium Meter Meter Int
  | BevelHeavy Meter Meter Int

-- | Default extrusion: slight depth, no bevel.
defaultExtrusionParams :: IconExtrusionParams
defaultExtrusionParams = IconExtrusionParams
  { depth: meter 2.0
  , bevel: BevelNone
  , curveSegments: 8
  , depthSegments: 1
  }

-- | Create extrusion params from icon size.
iconExtrusionParams :: Meter -> IconExtrusionParams
iconExtrusionParams size = IconExtrusionParams
  { depth: size
  , bevel: BevelNone
  , curveSegments: 12
  , depthSegments: 1
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // path // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert IconPath to array of 2D profile points.
-- |
-- | Samples the path at regular intervals to create smooth profile.
pathToProfile :: IconPath -> Int -> Array Point2DProfile
pathToProfile paths samples = case paths of
  SinglePath p -> pathToPoint2DProfile p samples
  MultiPath ps -> case Array.head ps of
    Just p -> pathToPoint2DProfile p samples
    Nothing -> []
  PartedIcon parts -> case Array.head parts of
    Just part -> pathToPoint2DProfile part.path samples
    Nothing -> []

-- | Convert Path to Point2DProfile array.
-- |
-- | Extracts X,Y coordinates from path commands.
pathToPoint2DProfile :: Path -> Int -> Array Point2DProfile
pathToPoint2DProfile path sampleCount =
  samplePath path sampleCount

-- | Sample path at regular intervals (parametric).
-- |
-- | Creates uniform samples using parameter t (0 to 1).
-- | Fast but may produce uneven spacing for complex paths.
samplePath :: Path -> Int -> Array Point2DProfile
samplePath path n = case n of
  0 -> []
  1 -> [centerProfile path]
  _ -> map sampleIndex (rangeTo n)
  where
    sampleIndex :: Int -> Point2DProfile
    sampleIndex i = 
      let t = toNumber i / toNumber (n - 1)
      in pointAtT path t

-- | Sample path at regular arc-length intervals.
-- |
-- | Uses arc-length parameterization for uniform spacing.
-- | More accurate than parametric sampling for curves.
samplePathArcLength :: Path -> Int -> Array Point2DProfile
samplePathArcLength path n = case n of
  0 -> []
  1 -> [centerProfile path]
  _ -> 
    let
      -- First get dense parametric samples
      denseSamples = samplePath path 100
      -- Then resample at uniform arc-length
      totalLength = computeTotalLength denseSamples
    in
      if totalLength == 0.0
        then [centerProfile path]
        else map (sampleAtLength denseSamples totalLength) (rangeTo n)
  where
    sampleAtLength :: Array Point2DProfile -> Number -> Int -> Point2DProfile
    sampleAtLength pts total i =
      let targetDist = (toNumber i / toNumber (n - 1)) * total
      in interpolatePoints pts targetDist
    
    computeTotalLength :: Array Point2DProfile -> Number
    computeTotalLength pts = 
      let dists = scanDistances pts
      in fromMaybe 0.0 (lastElem dists)
    
    lastElem :: Array Number -> Maybe Number
    lastElem arr = 
      let len = Array.length arr
      in if len == 0 then Nothing else Array.index arr (len - 1)

-- | Interpolate points to find point at distance.
interpolatePoints :: Array Point2DProfile -> Number -> Point2DProfile
interpolatePoints pts targetDist = 
  let distances = scanDistances pts
  in findPointAt distances targetDist pts

-- | Scan cumulative distances.
scanDistances :: Array Point2DProfile -> Array Number
scanDistances pts = scanHelper pts 0.0 []
  where
    scanHelper :: Array Point2DProfile -> Number -> Array Number -> Array Number
    scanHelper arr acc res = case Array.head arr of
      Nothing -> res
      Just p -> 
        let rest = dropFirst arr
            dist = distanceTo p
        in if Array.length rest == 0
           then Array.snoc res (acc + dist)
           else scanHelper rest (acc + dist) (Array.snoc res acc)
    distanceTo :: Point2DProfile -> Number
    distanceTo p = sqrt (unwrapMeter p.x * unwrapMeter p.x + unwrapMeter p.y * unwrapMeter p.y)

-- | Find point at target distance.
findPointAt :: Array Number -> Number -> Array Point2DProfile -> Point2DProfile
findPointAt dists target pts = case Array.head dists of
  Nothing -> centerProfileFrom pts
  Just d -> if d >= target 
    then fromMaybe (centerProfileFrom pts) (Array.head pts)
    else findPointAt (dropFirst dists) target (dropFirst pts)

-- | Interpolate between two points.
-- |
-- | Used for smooth path sampling between discrete points.
interpolateTwo :: Number -> Number -> Point2DProfile -> Point2DProfile
interpolateTwo prevDist target p2 =
  let t = if target - prevDist == 0.0 then 0.0 else (target - prevDist) / 1.0
  in { x: meter (unwrapMeter p2.x * t), y: meter (unwrapMeter p2.y * t) }

-- | Center profile (for single-sample case).
centerProfile :: Path -> Point2DProfile
centerProfile path = case firstPoint path of
  Just p -> pointToProfile p
  Nothing -> { x: meter 0.0, y: meter 0.0 }

-- | Center profile from points.
centerProfileFrom :: Array Point2DProfile -> Point2DProfile
centerProfileFrom pts = case Array.head pts of
  Nothing -> { x: meter 0.0, y: meter 0.0 }
  Just first -> { x: first.x, y: first.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // shape // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert profile to Shape2D for extrusion.
profileToShape2D :: Array Point2DProfile -> Shape2D
profileToShape2D contour = 
  { contour: contour
  , holes: []
  }

-- | Create shape with holes.
profileWithHoles :: Array Point2DProfile -> Array (Array Point2DProfile) -> Shape2D
profileWithHoles contour holes = 
  { contour: contour
  , holes: holes
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // mesh // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert icon definition to 3D mesh.
iconToMesh3D :: IconDefinition -> IconExtrusionParams -> Mesh3D
iconToMesh3D icon params = 
  let profile = pathToProfile icon.paths 24
      shape = profileToShape2D profile
      baseParams = extrusionParamsFromIcon params
      extrudeParams = baseParams { shape = shape }
  in extrudeMesh3D extrudeParams

-- | Convert icon path to 3D mesh.
pathToMesh3D :: IconPath -> IconExtrusionParams -> Mesh3D
pathToMesh3D path params = 
  let profile = pathToProfile path 24
      shape = profileToShape2D profile
      baseParams = extrusionParamsFromIcon params
      extrudeParams = baseParams { shape = shape }
  in extrudeMesh3D extrudeParams

-- | Convert icon part to 3D mesh.
partToMesh3D :: IconPart -> IconExtrusionParams -> Mesh3D
partToMesh3D part params = 
  let profile = pathToPoint2DProfile part.path 24
      shape = profileToShape2D profile
      baseParams = extrusionParamsFromIcon params
      extrudeParams = baseParams { shape = shape }
  in extrudeMesh3D extrudeParams

-- | Convert IconExtrusionParams to ExtrudeMeshParams.
extrusionParamsFromIcon :: IconExtrusionParams -> ExtrudeMeshParams
extrusionParamsFromIcon (IconExtrusionParams p) = 
  { shape: emptyShape
  , depth: p.depth
  , bevelEnabled: bevelEnabled p.bevel
  , bevelThickness: bevelThickness p.bevel
  , bevelSize: bevelSize p.bevel
  , bevelSegments: bevelSegments p.bevel
  , curveSegments: p.curveSegments
  }

-- | Empty shape for params.
emptyShape :: Shape2D
emptyShape = { contour: [], holes: [] }

-- | Bevel enabled flag.
bevelEnabled :: BevelConfig -> Boolean
bevelEnabled = case _ of
  BevelNone -> false
  _ -> true

-- | Bevel thickness from config.
bevelThickness :: BevelConfig -> Meter
bevelThickness = case _ of
  BevelNone -> meter 0.0
  BevelSubtle t _ _ -> t
  BevelMedium t _ _ -> t
  BevelHeavy t _ _ -> t

-- | Bevel size from config.
bevelSize :: BevelConfig -> Meter
bevelSize = case _ of
  BevelNone -> meter 0.0
  BevelSubtle _ s _ -> s
  BevelMedium _ s _ -> s
  BevelHeavy _ s _ -> s

-- | Bevel segments from config.
bevelSegments :: BevelConfig -> Int
bevelSegments = case _ of
  BevelNone -> 0
  BevelSubtle _ _ s -> s
  BevelMedium _ _ s -> s
  BevelHeavy _ _ s -> s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // bevel // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | No bevel (sharp edges).
noBevel :: BevelConfig
noBevel = BevelNone

-- | Subtle bevel for slight rounding.
subtleBevel :: BevelConfig
subtleBevel = BevelSubtle (meter 0.1) (meter 0.1) 3

-- | Medium bevel for visible rounding.
mediumBevel :: BevelConfig
mediumBevel = BevelMedium (meter 0.2) (meter 0.2) 5

-- | Heavy bevel for pronounced rounding.
heavyBevel :: BevelConfig
heavyBevel = BevelHeavy (meter 0.4) (meter 0.4) 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // icon // mesh3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D icon with metadata.
newtype IconMesh3D = IconMesh3D
  { mesh :: Mesh3D
  , name :: String
  , depth :: Meter
  , material :: Maybe MeshMaterial
  }

-- | Create icon mesh.
iconMesh3D :: String -> Mesh3D -> Meter -> IconMesh3D
iconMesh3D name mesh depth = IconMesh3D
  { mesh: mesh
  , name: name
  , depth: depth
  , material: Nothing
  }

-- | Convert mesh to element (for rendering).
meshToElement :: IconMesh3D -> Mesh3D
meshToElement (IconMesh3D m) = m.mesh

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // material // assignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Material assignment for icon mesh.
newtype MeshMaterial = MeshMaterial
  { baseColor :: OKLCH
  , metallic :: Number      -- 0.0 to 1.0
  , roughness :: Number     -- 0.0 to 1.0
  }

-- | Assign material to icon mesh.
assignMaterial :: MeshMaterial -> IconMesh3D -> IconMesh3D
assignMaterial mat (IconMesh3D m) = IconMesh3D 
  { mesh: m.mesh
  , name: m.name
  , depth: m.depth
  , material: Just mat
  }

-- | Assign brand material from theme.
assignBrandMaterial :: ColorRole -> IconTheme -> IconMesh3D -> IconMesh3D
assignBrandMaterial role theme (IconMesh3D m) = 
  let mode = iconThemeMode theme
      colors = iconThemeColors theme
      color = resolveIconColor role mode colors
      mat = MeshMaterial 
        { baseColor: color
        , metallic: 0.0
        , roughness: 0.5
        }
  in IconMesh3D 
    { mesh: m.mesh
    , name: m.name
    , depth: m.depth
    , material: Just mat
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // show // instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show instance for IconExtrusionParams.
instance showIconExtrusionParams :: Show IconExtrusionParams where
  show (IconExtrusionParams p) = "(IconExtrusionParams depth:" <> show p.depth <> ")"

-- | Show instance for BevelConfig.
instance showBevelConfig :: Show BevelConfig where
  show = case _ of
    BevelNone -> "BevelNone"
    BevelSubtle t s seg -> "(BevelSubtle " <> show t <> " " <> show s <> " " <> show seg <> ")"
    BevelMedium t s seg -> "(BevelMedium " <> show t <> " " <> show s <> " " <> show seg <> ")"
    BevelHeavy t s seg -> "(BevelHeavy " <> show t <> " " <> show s <> " " <> show seg <> ")"

-- | Show instance for IconMesh3D.
instance showIconMesh3D :: Show IconMesh3D where
  show (IconMesh3D m) = "(IconMesh3D " <> m.name <> " depth:" <> show m.depth <> ")"

-- | Show instance for MeshMaterial.
instance showMeshMaterial :: Show MeshMaterial where
  show (MeshMaterial m) = "(MeshMaterial color:" <> show m.baseColor <> " metallic:" <> show m.metallic <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drop first element of array (O(n) but safe).
dropFirst :: forall a. Array a -> Array a
dropFirst arr = Array.drop 1 arr

-- | Range from 0 to n-1.
-- |
-- | Bounded: max 10000 to prevent runaway recursion.
rangeTo :: Int -> Array Int
rangeTo n
  | n <= 0 = []
  | n > 10000 = rangeTo 10000  -- Prevent time dilation attack
  | otherwise = rangeHelper 0 n []
  where
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper i max acc
      | i >= max = acc
      | otherwise = rangeHelper (i + 1) max (Array.snoc acc i)

-- | Convert Int to Number (use Data.Int.toNumber).
toNumber :: Int -> Number
toNumber = Int.toNumber

-- | Square root (use Data.Number.sqrt).
sqrt :: Number -> Number
sqrt = Number.sqrt

-- | Convert Point2D to Point2DProfile.
pointToProfile :: Point2D -> Point2DProfile
pointToProfile p = { x: meter (getX p), y: meter (getY p) }

-- | Get point at parametric position t (0.0 to 1.0) along path.
-- |
-- | Samples path commands to find approximate point.
-- | Returns center if path is empty.
pointAtT :: Path -> Number -> Point2DProfile
pointAtT (Path cmds) t =
  let
    points = extractPoints cmds
    len = Array.length points
  in
    if len == 0 
      then { x: meter 0.0, y: meter 0.0 }
      else 
        let
          -- Clamp t to valid range
          tClamped = if t < 0.0 then 0.0 else if t > 1.0 then 1.0 else t
          -- Get index along points
          idx = if len == 1 then 0 else floor (tClamped * Int.toNumber (len - 1))
        in
          case Array.index points idx of
            Nothing -> { x: meter 0.0, y: meter 0.0 }
            Just p -> pointToProfile p

-- | Extract all points from path commands.
extractPoints :: Array PathCommand -> Array Point2D
extractPoints cmds = extractHelper cmds []
  where
    extractHelper :: Array PathCommand -> Array Point2D -> Array Point2D
    extractHelper cs acc = case Array.head cs of
      Nothing -> acc
      Just cmd -> extractHelper (Array.drop 1 cs) (acc <> pointsFromCommand cmd)
    
    pointsFromCommand :: PathCommand -> Array Point2D
    pointsFromCommand = case _ of
      MoveTo p -> [p]
      LineTo p -> [p]
      HLineTo _ -> []  -- Would need current Y to construct point
      VLineTo _ -> []  -- Would need current X to construct point
      QuadTo _ p -> [p]
      SmoothQuadTo p -> [p]
      CubicTo _ _ p -> [p]
      SmoothCurveTo _ p -> [p]
      ArcTo params -> [params.end]
      ClosePath -> []

-- | Floor a Number to Int (bounded).
floor :: Number -> Int
floor n
  | n < 0.0 = 0
  | n > 10000.0 = 10000
  | otherwise = floorHelper n 0
  where
    -- Simple floor by counting (safe due to upper bound)
    floorHelper :: Number -> Int -> Int
    floorHelper x acc
      | x < 1.0 = acc
      | otherwise = floorHelper (x - 1.0) (acc + 1)
