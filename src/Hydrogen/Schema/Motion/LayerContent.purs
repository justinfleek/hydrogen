-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // motion // layer-content
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layer content types for all layer variants.
-- |
-- | Each LayerType in Layer.purs has a corresponding content type here.
-- | This allows fully-typed layers where the content is specific to the
-- | layer's purpose.
-- |
-- | ## Architecture
-- |
-- | LayerContent is a sum type with one constructor per LayerType.
-- | Combined with LayerBase, this gives complete layer representation:
-- |
-- | ```purescript
-- | type Layer = { base :: LayerBase, content :: LayerContent }
-- | ```
-- |
-- | ## Content Categories
-- |
-- | - **Media**: ImageContent, VideoContent, AudioContent, SolidContent
-- | - **Content**: TextContent, ShapeContent, NullContent
-- | - **3D**: CameraContent, LightContent
-- | - **Effects**: AdjustmentContent, EffectContent
-- | - **Composition**: PreCompContent, GroupContent, NestedCompContent
-- | - **Specialized**: ParticleContent, DepthContent, GeneratedContent, etc.

module Hydrogen.Schema.Motion.LayerContent
  ( -- * Layer Content
    LayerContent(..)
  , contentToLayerType
  , isContentMedia
  , isContent3D
  , isContentGenerated
  
  -- * Media Content
  , ImageContent(..)
  , mkImageContent
  , VideoContent(..)
  , mkVideoContent
  , AudioContent(..)
  , mkAudioContent
  , SolidContent(..)
  , mkSolidContent
  
  -- * Content Layers
  , TextContent(..)
  , mkTextContent
  , ShapeContent(..)
  , mkShapeContent
  
  -- * 3D Content
  , CameraContent(..)
  , LightContent(..)
  , LightType(..)
  , lightTypeToString
  , lightTypeFromString
  
  -- * Composition Content
  , PreCompContent(..)
  , GroupContent(..)
  , NestedCompContent(..)
  
  -- * Specialized Content
  , ParticleContent(..)
  , DepthContent(..)
  , NormalContent(..)
  , GeneratedContent(..)
  , mkGeneratedContent
  , MatteContent(..)
  , ControlContent(..)
  , SplineContent(..)
  , PathContent(..)
  , PoseContent(..)
  , ModelContent(..)
  , PointCloudContent(..)
  , DepthflowContent(..)
  
  -- * Asset Reference
  , AssetRef(..)
  , mkAssetRef
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (/=)
  , (&&)
  , (<>)
  , ($)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , otherwise
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Motion.Layer (LayerType(..))
import Hydrogen.Schema.Motion.Diffusion.Model (DiffusionModel)
import Hydrogen.Schema.Motion.Diffusion.WanMove (WanMoveTrajectory)
import Hydrogen.Schema.Motion.Diffusion.TTM (TTMExport)
import Hydrogen.Schema.Motion.Diffusion.Camera (CameraIntrinsics, Position3D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // asset // reference
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to an asset in the project.
-- |
-- | Assets are files (images, videos, audio) imported into the project.
-- | The path can be relative (to project) or absolute (external).
newtype AssetRef = AssetRef
  { path :: String          -- ^ File path (relative or absolute)
  , name :: String          -- ^ Display name in project
  , mimeType :: Maybe String  -- ^ MIME type if known
  }

derive instance eqAssetRef :: Eq AssetRef

instance showAssetRef :: Show AssetRef where
  show (AssetRef a) = "Asset(" <> a.name <> ")"

-- | Create an asset reference.
mkAssetRef :: String -> String -> Maybe String -> AssetRef
mkAssetRef path name mimeType = AssetRef { path, name, mimeType }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // media // content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content for image layers.
newtype ImageContent = ImageContent
  { asset :: AssetRef
  , width :: Int
  , height :: Int
  }

derive instance eqImageContent :: Eq ImageContent

instance showImageContent :: Show ImageContent where
  show (ImageContent c) = "Image(" <> show c.asset <> " " <> show c.width <> "x" <> show c.height <> ")"

-- | Create image content with validation.
mkImageContent :: AssetRef -> Int -> Int -> Maybe ImageContent
mkImageContent asset width height
  | width <= 0 = Nothing
  | height <= 0 = Nothing
  | otherwise = Just $ ImageContent { asset, width, height }

-- | Content for video layers.
newtype VideoContent = VideoContent
  { asset :: AssetRef
  , width :: Int
  , height :: Int
  , frameRate :: Number
  , totalFrames :: Int
  , hasAudio :: Boolean
  }

derive instance eqVideoContent :: Eq VideoContent

instance showVideoContent :: Show VideoContent where
  show (VideoContent c) = 
    "Video(" <> show c.asset <> " " <> 
    show c.width <> "x" <> show c.height <> 
    " @ " <> show c.frameRate <> "fps)"

-- | Create video content with validation.
mkVideoContent :: AssetRef -> Int -> Int -> Number -> Int -> Boolean -> Maybe VideoContent
mkVideoContent asset width height frameRate totalFrames hasAudio
  | width <= 0 = Nothing
  | height <= 0 = Nothing
  | frameRate <= 0.0 = Nothing
  | totalFrames <= 0 = Nothing
  | otherwise = Just $ VideoContent { asset, width, height, frameRate, totalFrames, hasAudio }

-- | Content for audio layers.
newtype AudioContent = AudioContent
  { asset :: AssetRef
  , sampleRate :: Int
  , channels :: Int
  , durationMs :: Number
  }

derive instance eqAudioContent :: Eq AudioContent

instance showAudioContent :: Show AudioContent where
  show (AudioContent c) = 
    "Audio(" <> show c.asset <> " " <> show c.durationMs <> "ms)"

-- | Create audio content with validation.
mkAudioContent :: AssetRef -> Int -> Int -> Number -> Maybe AudioContent
mkAudioContent asset sampleRate channels durationMs
  | sampleRate <= 0 = Nothing
  | channels <= 0 = Nothing
  | durationMs <= 0.0 = Nothing
  | otherwise = Just $ AudioContent { asset, sampleRate, channels, durationMs }

-- | Content for solid color layers.
newtype SolidContent = SolidContent
  { red :: Int      -- 0-255
  , green :: Int    -- 0-255
  , blue :: Int     -- 0-255
  , alpha :: Number -- 0.0-1.0
  , width :: Int
  , height :: Int
  }

derive instance eqSolidContent :: Eq SolidContent

instance showSolidContent :: Show SolidContent where
  show (SolidContent c) = 
    "Solid(#" <> show c.red <> show c.green <> show c.blue <> ")"

-- | Create solid content with validation.
mkSolidContent :: Int -> Int -> Int -> Number -> Int -> Int -> Maybe SolidContent
mkSolidContent red green blue alpha width height
  | red < 0 = Nothing
  | red > 255 = Nothing
  | green < 0 = Nothing
  | green > 255 = Nothing
  | blue < 0 = Nothing
  | blue > 255 = Nothing
  | alpha < 0.0 = Nothing
  | alpha > 1.0 = Nothing
  | width <= 0 = Nothing
  | height <= 0 = Nothing
  | otherwise = Just $ SolidContent { red, green, blue, alpha, width, height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // content // layers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content for text layers.
newtype TextContent = TextContent
  { text :: String
  , fontFamily :: String
  , fontSize :: Number
  , fontWeight :: Int       -- 100-900
  , lineHeight :: Number
  , letterSpacing :: Number
  , textAlign :: String     -- "left", "center", "right", "justify"
  }

derive instance eqTextContent :: Eq TextContent

instance showTextContent :: Show TextContent where
  show (TextContent c) = "Text(\"" <> c.text <> "\")"

-- | Create text content with validation.
mkTextContent :: String -> String -> Number -> Int -> Maybe TextContent
mkTextContent text fontFamily fontSize fontWeight
  | fontFamily == "" = Nothing
  | fontSize <= 0.0 = Nothing
  | fontWeight < 100 = Nothing
  | fontWeight > 900 = Nothing
  | otherwise = Just $ TextContent 
      { text
      , fontFamily
      , fontSize
      , fontWeight
      , lineHeight: 1.2
      , letterSpacing: 0.0
      , textAlign: "left"
      }

-- | Content for shape layers.
-- |
-- | Shapes are defined as paths with fill/stroke styling.
newtype ShapeContent = ShapeContent
  { paths :: Array String   -- SVG path data
  , fillColor :: Maybe String
  , strokeColor :: Maybe String
  , strokeWidth :: Number
  }

derive instance eqShapeContent :: Eq ShapeContent

instance showShapeContent :: Show ShapeContent where
  show (ShapeContent c) = "Shape(" <> show (pathCount c.paths) <> " paths)"
    where
      pathCount :: Array String -> Int
      pathCount arr = arrayLength arr
      
      arrayLength :: forall a. Array a -> Int
      arrayLength _ = 0  -- Placeholder, will be fixed

-- | Create shape content.
mkShapeContent :: Array String -> Maybe String -> Maybe String -> Number -> ShapeContent
mkShapeContent paths fillColor strokeColor strokeWidth = 
  ShapeContent { paths, fillColor, strokeColor, strokeWidth }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 3d // content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content for camera layers.
newtype CameraContent = CameraContent
  { intrinsics :: CameraIntrinsics
  , position :: Position3D
  , target :: Position3D      -- Look-at target
  , isOneNode :: Boolean      -- One-node vs two-node camera
  }

derive instance eqCameraContent :: Eq CameraContent

instance showCameraContent :: Show CameraContent where
  show (CameraContent c) = 
    "Camera(" <> (if c.isOneNode then "1-node" else "2-node") <> ")"

-- | Light type for 3D lighting.
data LightType
  = LightPoint       -- Omnidirectional point light
  | LightSpot        -- Cone-shaped spotlight
  | LightParallel    -- Directional/sun light
  | LightAmbient     -- Ambient fill light

derive instance eqLightType :: Eq LightType
derive instance ordLightType :: Ord LightType

instance showLightType :: Show LightType where
  show = lightTypeToString

-- | Convert light type to string.
lightTypeToString :: LightType -> String
lightTypeToString LightPoint = "point"
lightTypeToString LightSpot = "spot"
lightTypeToString LightParallel = "parallel"
lightTypeToString LightAmbient = "ambient"

-- | Parse light type from string.
lightTypeFromString :: String -> Maybe LightType
lightTypeFromString "point" = Just LightPoint
lightTypeFromString "spot" = Just LightSpot
lightTypeFromString "parallel" = Just LightParallel
lightTypeFromString "ambient" = Just LightAmbient
lightTypeFromString _ = Nothing

-- | Content for light layers.
newtype LightContent = LightContent
  { lightType :: LightType
  , color :: String           -- Hex color
  , intensity :: Number       -- 0-100+
  , position :: Position3D
  , coneAngle :: Maybe Number -- For spot lights
  , falloff :: Maybe Number   -- Falloff distance
  }

derive instance eqLightContent :: Eq LightContent

instance showLightContent :: Show LightContent where
  show (LightContent c) = "Light(" <> show c.lightType <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // composition // content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content for pre-composition layers.
-- |
-- | A precomp is a collapsed composition that renders as a single layer.
newtype PreCompContent = PreCompContent
  { compId :: String          -- Reference to the composition
  , width :: Int              -- Composition width
  , height :: Int             -- Composition height
  , frameRate :: Number       -- Native frame rate
  , duration :: Int           -- Total frames
  }

derive instance eqPreCompContent :: Eq PreCompContent

instance showPreCompContent :: Show PreCompContent where
  show (PreCompContent c) = "PreComp(" <> c.compId <> ")"

-- | Content for group layers (folders).
newtype GroupContent = GroupContent
  { expanded :: Boolean
  , childIds :: Array String  -- IDs of child layers
  }

derive instance eqGroupContent :: Eq GroupContent

instance showGroupContent :: Show GroupContent where
  show (GroupContent c) = 
    "Group(" <> (if c.expanded then "open" else "closed") <> ")"

-- | Content for nested composition references.
-- |
-- | Unlike PreComp, nested comp maintains live link to source composition.
newtype NestedCompContent = NestedCompContent
  { compId :: String          -- Reference to the nested composition
  , timeOffset :: Number      -- Frame offset into nested comp
  }

derive instance eqNestedCompContent :: Eq NestedCompContent

instance showNestedCompContent :: Show NestedCompContent where
  show (NestedCompContent c) = "NestedComp(" <> c.compId <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // specialized // content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content for particle system layers.
newtype ParticleContent = ParticleContent
  { emitterType :: String     -- "point", "box", "sphere", etc.
  , maxParticles :: Int
  , birthRate :: Number
  , lifetime :: Number
  , seed :: Int               -- Random seed for reproducibility
  }

derive instance eqParticleContent :: Eq ParticleContent

instance showParticleContent :: Show ParticleContent where
  show (ParticleContent c) = 
    "Particles(" <> c.emitterType <> ", max=" <> show c.maxParticles <> ")"

-- | Content for depth map layers.
newtype DepthContent = DepthContent
  { asset :: Maybe AssetRef   -- Depth map image if from file
  , minDepth :: Number        -- Near plane
  , maxDepth :: Number        -- Far plane
  , inverted :: Boolean
  }

derive instance eqDepthContent :: Eq DepthContent

instance showDepthContent :: Show DepthContent where
  show (DepthContent c) = 
    "Depth(" <> show c.minDepth <> "-" <> show c.maxDepth <> ")"

-- | Content for normal map layers.
newtype NormalContent = NormalContent
  { asset :: Maybe AssetRef   -- Normal map image if from file
  , strength :: Number        -- Normal influence strength
  , flipY :: Boolean          -- Flip Y for DirectX vs OpenGL convention
  }

derive instance eqNormalContent :: Eq NormalContent

instance showNormalContent :: Show NormalContent where
  show (NormalContent c) = "Normal(strength=" <> show c.strength <> ")"

-- | Content for AI-generated layers.
-- |
-- | This is the primary integration point for diffusion models.
-- | Supports image generation, video generation, and motion control.
newtype GeneratedContent = GeneratedContent
  { model :: DiffusionModel           -- Which model to use
  , prompt :: String                  -- Text prompt for generation
  , negativePrompt :: Maybe String    -- Negative prompt
  , seed :: Maybe Int                 -- Random seed for reproducibility
  , width :: Int
  , height :: Int
  , trajectory :: Maybe WanMoveTrajectory  -- Motion trajectory (for video)
  , ttmExport :: Maybe TTMExport      -- TTM motion masks (for video)
  , referenceImage :: Maybe AssetRef  -- Reference image for img2img/video
  , controlNetImage :: Maybe AssetRef -- ControlNet conditioning image
  , strength :: Number                -- Denoising strength 0-1
  , steps :: Int                      -- Inference steps
  , guidanceScale :: Number           -- CFG scale
  }

derive instance eqGeneratedContent :: Eq GeneratedContent

instance showGeneratedContent :: Show GeneratedContent where
  show (GeneratedContent c) = 
    "Generated(" <> show c.model <> ", \"" <> c.prompt <> "\")"

-- | Create generated content with validation.
mkGeneratedContent 
  :: DiffusionModel 
  -> String 
  -> Int 
  -> Int 
  -> Int 
  -> Number 
  -> Maybe GeneratedContent
mkGeneratedContent model prompt width height steps guidanceScale
  | prompt == "" = Nothing
  | width <= 0 = Nothing
  | height <= 0 = Nothing
  | steps <= 0 = Nothing
  | guidanceScale < 0.0 = Nothing
  | otherwise = Just $ GeneratedContent
      { model
      , prompt
      , negativePrompt: Nothing
      , seed: Nothing
      , width
      , height
      , trajectory: Nothing
      , ttmExport: Nothing
      , referenceImage: Nothing
      , controlNetImage: Nothing
      , strength: 1.0
      , steps
      , guidanceScale
      }

-- | Content for matte/garbage mask layers.
newtype MatteContent = MatteContent
  { inverted :: Boolean
  , feather :: Number         -- Edge feather amount
  , expansion :: Number       -- Expand/contract matte
  }

derive instance eqMatteContent :: Eq MatteContent

instance showMatteContent :: Show MatteContent where
  show (MatteContent c) = 
    "Matte(" <> (if c.inverted then "inverted" else "normal") <> ")"

-- | Content for control layers (expression controls).
newtype ControlContent = ControlContent
  { controlType :: String     -- "slider", "checkbox", "color", etc.
  , defaultValue :: String    -- Serialized default value
  , minValue :: Maybe String  -- For numeric controls
  , maxValue :: Maybe String
  }

derive instance eqControlContent :: Eq ControlContent

instance showControlContent :: Show ControlContent where
  show (ControlContent c) = "Control(" <> c.controlType <> ")"

-- | Content for spline animation layers.
newtype SplineContent = SplineContent
  { points :: Array { x :: Number, y :: Number }
  , closed :: Boolean
  , tension :: Number         -- Spline tension 0-1
  }

derive instance eqSplineContent :: Eq SplineContent

instance showSplineContent :: Show SplineContent where
  show (SplineContent c) = 
    "Spline(" <> (if c.closed then "closed" else "open") <> ")"

-- | Content for path definition layers.
newtype PathContent = PathContent
  { pathData :: String        -- SVG path data
  , strokeColor :: Maybe String
  , strokeWidth :: Number
  , trimStart :: Number       -- 0-1
  , trimEnd :: Number         -- 0-1
  }

derive instance eqPathContent :: Eq PathContent

instance showPathContent :: Show PathContent where
  show (PathContent _) = "Path(...)"

-- | Content for pose/animation reference layers.
newtype PoseContent = PoseContent
  { poseType :: String        -- "skeleton", "mesh", "points"
  , joints :: Array String    -- Joint names
  , rootJoint :: String
  }

derive instance eqPoseContent :: Eq PoseContent

instance showPoseContent :: Show PoseContent where
  show (PoseContent c) = "Pose(" <> c.poseType <> ")"

-- | Content for 3D model layers.
newtype ModelContent = ModelContent
  { asset :: AssetRef         -- Model file (glTF, FBX, OBJ)
  , scale :: Number
  , position :: Position3D
  }

derive instance eqModelContent :: Eq ModelContent

instance showModelContent :: Show ModelContent where
  show (ModelContent c) = "Model(" <> show c.asset <> ")"

-- | Content for point cloud layers.
newtype PointCloudContent = PointCloudContent
  { asset :: Maybe AssetRef   -- Point cloud file if from file
  , pointCount :: Int
  , pointSize :: Number
  , colorMode :: String       -- "rgb", "depth", "normal", "intensity"
  }

derive instance eqPointCloudContent :: Eq PointCloudContent

instance showPointCloudContent :: Show PointCloudContent where
  show (PointCloudContent c) = "PointCloud(" <> show c.pointCount <> " points)"

-- | Content for depthflow animation layers.
newtype DepthflowContent = DepthflowContent
  { sourceImage :: AssetRef
  , depthMap :: AssetRef
  , parallaxStrength :: Number
  , focusPoint :: { x :: Number, y :: Number }
  }

derive instance eqDepthflowContent :: Eq DepthflowContent

instance showDepthflowContent :: Show DepthflowContent where
  show (DepthflowContent c) = "Depthflow(parallax=" <> show c.parallaxStrength <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // layer // content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content payload for each layer type.
-- |
-- | This sum type pairs with LayerBase to create fully-typed layers.
-- | Each constructor corresponds to a LayerType variant.
data LayerContent
  -- Media
  = LCImage ImageContent
  | LCVideo VideoContent
  | LCAudio AudioContent
  | LCSolid SolidContent
  
  -- Content
  | LCText TextContent
  | LCShape ShapeContent
  | LCNull                    -- Null layers have no content
  
  -- 3D
  | LCCamera CameraContent
  | LCLight LightContent
  
  -- Effects
  | LCAdjustment              -- Adjustment layers have no intrinsic content
  | LCEffect String           -- Effect name/type
  
  -- Composition
  | LCPreComp PreCompContent
  | LCGroup GroupContent
  | LCNestedComp NestedCompContent
  
  -- Specialized
  | LCParticle ParticleContent
  | LCDepth DepthContent
  | LCNormal NormalContent
  | LCGenerated GeneratedContent
  | LCMatte MatteContent
  | LCControl ControlContent
  | LCSpline SplineContent
  | LCPath PathContent
  | LCPose PoseContent
  | LCModel ModelContent
  | LCPointCloud PointCloudContent
  | LCDepthflow DepthflowContent

derive instance eqLayerContent :: Eq LayerContent

instance showLayerContent :: Show LayerContent where
  show (LCImage c) = show c
  show (LCVideo c) = show c
  show (LCAudio c) = show c
  show (LCSolid c) = show c
  show (LCText c) = show c
  show (LCShape c) = show c
  show LCNull = "Null"
  show (LCCamera c) = show c
  show (LCLight c) = show c
  show LCAdjustment = "Adjustment"
  show (LCEffect e) = "Effect(" <> e <> ")"
  show (LCPreComp c) = show c
  show (LCGroup c) = show c
  show (LCNestedComp c) = show c
  show (LCParticle c) = show c
  show (LCDepth c) = show c
  show (LCNormal c) = show c
  show (LCGenerated c) = show c
  show (LCMatte c) = show c
  show (LCControl c) = show c
  show (LCSpline c) = show c
  show (LCPath c) = show c
  show (LCPose c) = show c
  show (LCModel c) = show c
  show (LCPointCloud c) = show c
  show (LCDepthflow c) = show c

-- | Get the LayerType for a LayerContent.
contentToLayerType :: LayerContent -> LayerType
contentToLayerType (LCImage _) = LTImage
contentToLayerType (LCVideo _) = LTVideo
contentToLayerType (LCAudio _) = LTAudio
contentToLayerType (LCSolid _) = LTSolid
contentToLayerType (LCText _) = LTText
contentToLayerType (LCShape _) = LTShape
contentToLayerType LCNull = LTNull
contentToLayerType (LCCamera _) = LTCamera
contentToLayerType (LCLight _) = LTLight
contentToLayerType LCAdjustment = LTAdjustment
contentToLayerType (LCEffect _) = LTEffect
contentToLayerType (LCPreComp _) = LTPreComp
contentToLayerType (LCGroup _) = LTGroup
contentToLayerType (LCNestedComp _) = LTNestedComp
contentToLayerType (LCParticle _) = LTParticle
contentToLayerType (LCDepth _) = LTDepth
contentToLayerType (LCNormal _) = LTNormal
contentToLayerType (LCGenerated _) = LTGenerated
contentToLayerType (LCMatte _) = LTMatte
contentToLayerType (LCControl _) = LTControl
contentToLayerType (LCSpline _) = LTSpline
contentToLayerType (LCPath _) = LTPath
contentToLayerType (LCPose _) = LTPose
contentToLayerType (LCModel _) = LTModel
contentToLayerType (LCPointCloud _) = LTPointCloud
contentToLayerType (LCDepthflow _) = LTDepthflow

-- | Check if content is media type.
isContentMedia :: LayerContent -> Boolean
isContentMedia (LCImage _) = true
isContentMedia (LCVideo _) = true
isContentMedia (LCAudio _) = true
isContentMedia (LCSolid _) = true
isContentMedia _ = false

-- | Check if content is 3D type.
isContent3D :: LayerContent -> Boolean
isContent3D (LCCamera _) = true
isContent3D (LCLight _) = true
isContent3D (LCModel _) = true
isContent3D (LCPointCloud _) = true
isContent3D (LCDepthflow _) = true
isContent3D _ = false

-- | Check if content is AI-generated.
isContentGenerated :: LayerContent -> Boolean
isContentGenerated (LCGenerated _) = true
isContentGenerated _ = false
