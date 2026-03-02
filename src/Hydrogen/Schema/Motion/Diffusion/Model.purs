-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // diffusion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Diffusion model types for AI-generated content layers.
-- |
-- | This module defines the generative AI models supported for LTGenerated
-- | layer content. Includes image generation, video generation, 3D generation,
-- | and image editing models.
-- |
-- | ## Supported Model Categories
-- |
-- | **Image Generation:**
-- | - Flux 2 (Black Forest Labs)
-- | - Z-Image (Zhipu AI)
-- | - Qwen Image 2509 (Alibaba)
-- | - Stable Diffusion XL
-- |
-- | **Video Generation:**
-- | - Wan 2.2 (Alibaba)
-- | - CogVideoX (Tsinghua)
-- | - Stable Video Diffusion
-- | - ATI (Advanced Text-to-Image-to-Video)
-- |
-- | **3D Generation:**
-- | - Hunyuan 3D (Tencent)
-- | - Trellis 2 (Microsoft)
-- |
-- | **Image Editing:**
-- | - Qwen Image Edit 2511
-- | - Z-Image Edit
-- | - InstructPix2Pix
-- |
-- | **Motion Control:**
-- | - MotionCtrl (pose-based video)
-- | - Uni3C (camera control)
-- | - WanMove (trajectory-based)
-- | - Time-to-Move (TTM)
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Export` from the Haskell backend, ensuring
-- | type-level compatibility for serialization between PureScript UI and
-- | Haskell generation backend.
-- |
-- | ## Architecture Note
-- |
-- | This module exceeds the standard 500-line limit due to schema coherence.
-- | The unified DiffusionModel type wraps all 5 model categories (Image, Video,
-- | 3D, Edit, Motion), requiring their enums to be co-located. The parser
-- | `diffusionModelFromString` dispatches to category-specific parsers that
-- | must be defined in the same module.

module Hydrogen.Schema.Motion.Diffusion.Model
  ( -- * Image Generation Models
    ImageModel(IMFlux2Dev, IMFlux2Pro, IMFlux2Schnell, IMZImage, IMQwenImage2509, IMSDXL, IMSD3, IMDalle3, IMMidjourney, IMIdeogram2)
  , imageModelToString
  , imageModelFromString
  , isImageModelFast
  , isImageModelHighQuality
  
  -- * Video Generation Models
  , VideoModel(VMWan22, VMWan21, VMCogVideoX, VMCogVideoX5B, VMSVD, VMSVDXT, VMATI, VMRunway, VMKling, VMPika, VMLuma, VMHunyuanVideo)
  , videoModelToString
  , videoModelFromString
  , videoModelMaxFrames
  , videoModelMaxResolution
  
  -- * 3D Generation Models
  , Model3D(M3DHunyuan3D, M3DTrellis2, M3DTripoSR, M3DLGMesh, M3DInstant3D, M3DZero123Plus, M3DMeshAnything)
  , model3DToString
  , model3DFromString
  
  -- * Image Editing Models
  , EditModel(EMQwenImageEdit2511, EMZImageEdit, EMInstructPix2Pix, EMSDEdit, EMControlNetInpaint, EMFluxFill)
  , editModelToString
  , editModelFromString
  
  -- * Motion Control Models
  , MotionModel(MMMotionCtrl, MMUni3C, MMWanMove, MMTimeToMove, MMCameraCtrl, MMAnimateDiff, MMDragAnything)
  , motionModelToString
  , motionModelFromString
  
  -- * Unified Model Type
  , DiffusionModel(DMImage, DMVideo, DM3D, DMEdit, DMMotion)
  , diffusionModelToString
  , diffusionModelFromString
  , diffusionModelCategory
  
  -- * Model Enumeration
  , allImageModels
  , allVideoModels
  , all3DModels
  , allEditModels
  , allMotionModels
  
  -- * Model Filtering
  , filterImageModels
  , filterVideoModels
  , videoModelsWithMinFrames
  , videoModelsWithMinResolution
  
  -- * Model Mapping
  , mapImageModels
  , mapVideoModels
  , map3DModels
  , mapEditModels
  , mapMotionModels
  
  -- * Model Composition
  , lookupAndTransform
  
  -- * Default Models (First/Last in Enumeration)
  , firstImageModel
  , lastImageModel
  , firstVideoModel
  , lastVideoModel
  , first3DModel
  , last3DModel
  , firstEditModel
  , lastEditModel
  , firstMotionModel
  , lastMotionModel
  , ModelCategory(MCImage, MCVideo, MC3D, MCEdit, MCMotion)
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , (==)
  , (<>)
  , ($)
  , (<$>)
  , (<<<)
  , (>=)
  , otherwise
  , map
  , bottom
  , top
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String.CodeUnits (take, drop, length) as SCU
import Data.Array (filter) as Array

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // image // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Image generation models.
-- |
-- | These models generate static images from text prompts and optional
-- | reference images.
data ImageModel
  = IMFlux2Dev          -- ^ Flux 2 Dev - fast iteration
  | IMFlux2Pro          -- ^ Flux 2 Pro - high quality
  | IMFlux2Schnell      -- ^ Flux 2 Schnell - fastest
  | IMZImage            -- ^ Z-Image (Zhipu AI)
  | IMQwenImage2509     -- ^ Qwen Image 2509
  | IMSDXL              -- ^ Stable Diffusion XL
  | IMSD3               -- ^ Stable Diffusion 3
  | IMDalle3            -- ^ DALL-E 3 (OpenAI)
  | IMMidjourney        -- ^ Midjourney (via API)
  | IMIdeogram2         -- ^ Ideogram 2

derive instance eqImageModel :: Eq ImageModel
derive instance ordImageModel :: Ord ImageModel

instance boundedImageModel :: Bounded ImageModel where
  bottom = IMFlux2Dev
  top = IMIdeogram2

instance showImageModel :: Show ImageModel where
  show = imageModelToString

-- | Convert image model to string identifier.
imageModelToString :: ImageModel -> String
imageModelToString IMFlux2Dev = "flux2-dev"
imageModelToString IMFlux2Pro = "flux2-pro"
imageModelToString IMFlux2Schnell = "flux2-schnell"
imageModelToString IMZImage = "z-image"
imageModelToString IMQwenImage2509 = "qwen-image-2509"
imageModelToString IMSDXL = "sdxl"
imageModelToString IMSD3 = "sd3"
imageModelToString IMDalle3 = "dalle3"
imageModelToString IMMidjourney = "midjourney"
imageModelToString IMIdeogram2 = "ideogram2"

-- | Parse image model from string.
imageModelFromString :: String -> Maybe ImageModel
imageModelFromString "flux2-dev" = Just IMFlux2Dev
imageModelFromString "flux2-pro" = Just IMFlux2Pro
imageModelFromString "flux2-schnell" = Just IMFlux2Schnell
imageModelFromString "z-image" = Just IMZImage
imageModelFromString "qwen-image-2509" = Just IMQwenImage2509
imageModelFromString "sdxl" = Just IMSDXL
imageModelFromString "sd3" = Just IMSD3
imageModelFromString "dalle3" = Just IMDalle3
imageModelFromString "midjourney" = Just IMMidjourney
imageModelFromString "ideogram2" = Just IMIdeogram2
imageModelFromString _ = Nothing

-- | Check if model is optimized for fast generation.
isImageModelFast :: ImageModel -> Boolean
isImageModelFast IMFlux2Schnell = true
isImageModelFast IMFlux2Dev = true
isImageModelFast _ = false

-- | Check if model is optimized for high quality.
isImageModelHighQuality :: ImageModel -> Boolean
isImageModelHighQuality IMFlux2Pro = true
isImageModelHighQuality IMSD3 = true
isImageModelHighQuality IMDalle3 = true
isImageModelHighQuality IMMidjourney = true
isImageModelHighQuality _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // video // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Video generation models.
-- |
-- | These models generate video sequences from text prompts, reference images,
-- | and optional motion guidance.
data VideoModel
  = VMWan22             -- ^ Wan 2.2 (Alibaba)
  | VMWan21             -- ^ Wan 2.1
  | VMCogVideoX         -- ^ CogVideoX (Tsinghua)
  | VMCogVideoX5B       -- ^ CogVideoX 5B
  | VMSVD               -- ^ Stable Video Diffusion
  | VMSVDXT             -- ^ SVD-XT (extended)
  | VMATI               -- ^ ATI model
  | VMRunway            -- ^ Runway Gen-3
  | VMKling             -- ^ Kling (Kuaishou)
  | VMPika              -- ^ Pika Labs
  | VMLuma              -- ^ Luma Dream Machine
  | VMHunyuanVideo      -- ^ Hunyuan Video (Tencent)

derive instance eqVideoModel :: Eq VideoModel
derive instance ordVideoModel :: Ord VideoModel

instance boundedVideoModel :: Bounded VideoModel where
  bottom = VMWan22
  top = VMHunyuanVideo

instance showVideoModel :: Show VideoModel where
  show = videoModelToString

-- | Convert video model to string identifier.
videoModelToString :: VideoModel -> String
videoModelToString VMWan22 = "wan22"
videoModelToString VMWan21 = "wan21"
videoModelToString VMCogVideoX = "cogvideox"
videoModelToString VMCogVideoX5B = "cogvideox-5b"
videoModelToString VMSVD = "svd"
videoModelToString VMSVDXT = "svd-xt"
videoModelToString VMATI = "ati"
videoModelToString VMRunway = "runway-gen3"
videoModelToString VMKling = "kling"
videoModelToString VMPika = "pika"
videoModelToString VMLuma = "luma"
videoModelToString VMHunyuanVideo = "hunyuan-video"

-- | Parse video model from string.
videoModelFromString :: String -> Maybe VideoModel
videoModelFromString "wan22" = Just VMWan22
videoModelFromString "wan21" = Just VMWan21
videoModelFromString "cogvideox" = Just VMCogVideoX
videoModelFromString "cogvideox-5b" = Just VMCogVideoX5B
videoModelFromString "svd" = Just VMSVD
videoModelFromString "svd-xt" = Just VMSVDXT
videoModelFromString "ati" = Just VMATI
videoModelFromString "runway-gen3" = Just VMRunway
videoModelFromString "kling" = Just VMKling
videoModelFromString "pika" = Just VMPika
videoModelFromString "luma" = Just VMLuma
videoModelFromString "hunyuan-video" = Just VMHunyuanVideo
videoModelFromString _ = Nothing

-- | Maximum frames supported by model.
-- |
-- | Returns the maximum number of frames the model can generate in a single
-- | inference pass.
videoModelMaxFrames :: VideoModel -> Int
videoModelMaxFrames VMWan22 = 257          -- 81 or 257 frames
videoModelMaxFrames VMWan21 = 81
videoModelMaxFrames VMCogVideoX = 49
videoModelMaxFrames VMCogVideoX5B = 49
videoModelMaxFrames VMSVD = 25
videoModelMaxFrames VMSVDXT = 25
videoModelMaxFrames VMATI = 120
videoModelMaxFrames VMRunway = 256
videoModelMaxFrames VMKling = 150
videoModelMaxFrames VMPika = 24
videoModelMaxFrames VMLuma = 120
videoModelMaxFrames VMHunyuanVideo = 129

-- | Maximum resolution (width or height) supported by model.
videoModelMaxResolution :: VideoModel -> Int
videoModelMaxResolution VMWan22 = 1280
videoModelMaxResolution VMWan21 = 1280
videoModelMaxResolution VMCogVideoX = 720
videoModelMaxResolution VMCogVideoX5B = 1080
videoModelMaxResolution VMSVD = 1024
videoModelMaxResolution VMSVDXT = 1024
videoModelMaxResolution VMATI = 1024
videoModelMaxResolution VMRunway = 1280
videoModelMaxResolution VMKling = 1080
videoModelMaxResolution VMPika = 1080
videoModelMaxResolution VMLuma = 1080
videoModelMaxResolution VMHunyuanVideo = 720

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // 3d // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D generation models.
-- |
-- | These models generate 3D meshes, point clouds, or volumetric data
-- | from images or text prompts.
data Model3D
  = M3DHunyuan3D        -- ^ Hunyuan 3D (Tencent)
  | M3DTrellis2         -- ^ Trellis 2 (Microsoft)
  | M3DTripoSR          -- ^ TripoSR (Stability AI)
  | M3DLGMesh           -- ^ LGMesh
  | M3DInstant3D        -- ^ Instant3D
  | M3DZero123Plus      -- ^ Zero123++
  | M3DMeshAnything     -- ^ MeshAnything

derive instance eqModel3D :: Eq Model3D
derive instance ordModel3D :: Ord Model3D

instance boundedModel3D :: Bounded Model3D where
  bottom = M3DHunyuan3D
  top = M3DMeshAnything

instance showModel3D :: Show Model3D where
  show = model3DToString

-- | Convert 3D model to string identifier.
model3DToString :: Model3D -> String
model3DToString M3DHunyuan3D = "hunyuan3d"
model3DToString M3DTrellis2 = "trellis2"
model3DToString M3DTripoSR = "triposr"
model3DToString M3DLGMesh = "lgmesh"
model3DToString M3DInstant3D = "instant3d"
model3DToString M3DZero123Plus = "zero123plus"
model3DToString M3DMeshAnything = "meshanything"

-- | Parse 3D model from string.
model3DFromString :: String -> Maybe Model3D
model3DFromString "hunyuan3d" = Just M3DHunyuan3D
model3DFromString "trellis2" = Just M3DTrellis2
model3DFromString "triposr" = Just M3DTripoSR
model3DFromString "lgmesh" = Just M3DLGMesh
model3DFromString "instant3d" = Just M3DInstant3D
model3DFromString "zero123plus" = Just M3DZero123Plus
model3DFromString "meshanything" = Just M3DMeshAnything
model3DFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // image // editing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Image editing models.
-- |
-- | These models perform targeted edits on existing images based on
-- | text instructions or mask regions.
data EditModel
  = EMQwenImageEdit2511   -- ^ Qwen Image Edit 2511
  | EMZImageEdit          -- ^ Z-Image Edit
  | EMInstructPix2Pix     -- ^ InstructPix2Pix
  | EMSDEdit              -- ^ Stable Diffusion Edit
  | EMControlNetInpaint   -- ^ ControlNet Inpainting
  | EMFluxFill            -- ^ Flux Fill (inpainting)

derive instance eqEditModel :: Eq EditModel
derive instance ordEditModel :: Ord EditModel

instance boundedEditModel :: Bounded EditModel where
  bottom = EMQwenImageEdit2511
  top = EMFluxFill

instance showEditModel :: Show EditModel where
  show = editModelToString

-- | Convert edit model to string identifier.
editModelToString :: EditModel -> String
editModelToString EMQwenImageEdit2511 = "qwen-image-edit-2511"
editModelToString EMZImageEdit = "z-image-edit"
editModelToString EMInstructPix2Pix = "instructpix2pix"
editModelToString EMSDEdit = "sd-edit"
editModelToString EMControlNetInpaint = "controlnet-inpaint"
editModelToString EMFluxFill = "flux-fill"

-- | Parse edit model from string.
editModelFromString :: String -> Maybe EditModel
editModelFromString "qwen-image-edit-2511" = Just EMQwenImageEdit2511
editModelFromString "z-image-edit" = Just EMZImageEdit
editModelFromString "instructpix2pix" = Just EMInstructPix2Pix
editModelFromString "sd-edit" = Just EMSDEdit
editModelFromString "controlnet-inpaint" = Just EMControlNetInpaint
editModelFromString "flux-fill" = Just EMFluxFill
editModelFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // motion // control
-- ═════════════════════════════════════════════════════════════════════════════

-- | Motion control models.
-- |
-- | These models add motion guidance to video generation via camera paths,
-- | pose sequences, or trajectory data.
data MotionModel
  = MMMotionCtrl        -- ^ MotionCtrl (pose-based)
  | MMUni3C             -- ^ Uni3C (camera control)
  | MMWanMove           -- ^ WanMove (trajectory-based)
  | MMTimeToMove        -- ^ Time-to-Move (TTM)
  | MMCameraCtrl        -- ^ CameraCtrl
  | MMAnimateDiff       -- ^ AnimateDiff
  | MMDragAnything      -- ^ DragAnything

derive instance eqMotionModel :: Eq MotionModel
derive instance ordMotionModel :: Ord MotionModel

instance boundedMotionModel :: Bounded MotionModel where
  bottom = MMMotionCtrl
  top = MMDragAnything

instance showMotionModel :: Show MotionModel where
  show = motionModelToString

-- | Convert motion model to string identifier.
motionModelToString :: MotionModel -> String
motionModelToString MMMotionCtrl = "motionctrl"
motionModelToString MMUni3C = "uni3c"
motionModelToString MMWanMove = "wanmove"
motionModelToString MMTimeToMove = "time-to-move"
motionModelToString MMCameraCtrl = "cameractrl"
motionModelToString MMAnimateDiff = "animatediff"
motionModelToString MMDragAnything = "draganything"

-- | Parse motion model from string.
motionModelFromString :: String -> Maybe MotionModel
motionModelFromString "motionctrl" = Just MMMotionCtrl
motionModelFromString "uni3c" = Just MMUni3C
motionModelFromString "wanmove" = Just MMWanMove
motionModelFromString "time-to-move" = Just MMTimeToMove
motionModelFromString "cameractrl" = Just MMCameraCtrl
motionModelFromString "animatediff" = Just MMAnimateDiff
motionModelFromString "draganything" = Just MMDragAnything
motionModelFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // unified // model
-- ═════════════════════════════════════════════════════════════════════════════

-- | Model category for classification.
data ModelCategory
  = MCImage       -- ^ Static image generation
  | MCVideo       -- ^ Video generation
  | MC3D          -- ^ 3D asset generation
  | MCEdit        -- ^ Image editing
  | MCMotion      -- ^ Motion control

derive instance eqModelCategory :: Eq ModelCategory
derive instance ordModelCategory :: Ord ModelCategory

instance showModelCategory :: Show ModelCategory where
  show MCImage = "image"
  show MCVideo = "video"
  show MC3D = "3d"
  show MCEdit = "edit"
  show MCMotion = "motion"

-- | Unified diffusion model type.
-- |
-- | Wraps all model categories into a single sum type for use in
-- | LTGenerated layer content.
data DiffusionModel
  = DMImage ImageModel
  | DMVideo VideoModel
  | DM3D Model3D
  | DMEdit EditModel
  | DMMotion MotionModel

derive instance eqDiffusionModel :: Eq DiffusionModel
derive instance ordDiffusionModel :: Ord DiffusionModel

instance showDiffusionModel :: Show DiffusionModel where
  show = diffusionModelToString

-- | Convert unified model to string identifier.
-- |
-- | Prefixes with category for unambiguous parsing.
diffusionModelToString :: DiffusionModel -> String
diffusionModelToString (DMImage m) = "image:" <> imageModelToString m
diffusionModelToString (DMVideo m) = "video:" <> videoModelToString m
diffusionModelToString (DM3D m) = "3d:" <> model3DToString m
diffusionModelToString (DMEdit m) = "edit:" <> editModelToString m
diffusionModelToString (DMMotion m) = "motion:" <> motionModelToString m

-- | Parse unified model from string.
-- |
-- | Expects format "category:model-id".
diffusionModelFromString :: String -> Maybe DiffusionModel
diffusionModelFromString s = parseWithPrefix s
  where
    parseWithPrefix str
      | hasPrefix "image:" str = 
          DMImage <$> imageModelFromString (SCU.drop 6 str)
      | hasPrefix "video:" str = 
          DMVideo <$> videoModelFromString (SCU.drop 6 str)
      | hasPrefix "3d:" str = 
          DM3D <$> model3DFromString (SCU.drop 3 str)
      | hasPrefix "edit:" str = 
          DMEdit <$> editModelFromString (SCU.drop 5 str)
      | hasPrefix "motion:" str = 
          DMMotion <$> motionModelFromString (SCU.drop 7 str)
      | otherwise = Nothing
    
    hasPrefix :: String -> String -> Boolean
    hasPrefix prefix str = SCU.take (SCU.length prefix) str == prefix

-- | Get the category of a diffusion model.
diffusionModelCategory :: DiffusionModel -> ModelCategory
diffusionModelCategory (DMImage _) = MCImage
diffusionModelCategory (DMVideo _) = MCVideo
diffusionModelCategory (DM3D _) = MC3D
diffusionModelCategory (DMEdit _) = MCEdit
diffusionModelCategory (DMMotion _) = MCMotion

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // enumeration // utils
-- ═════════════════════════════════════════════════════════════════════════════

-- | All image generation models.
-- |
-- | Use this to iterate over available models for UI dropdowns, validation,
-- | or capability checks.
allImageModels :: Array ImageModel
allImageModels =
  [ IMFlux2Dev
  , IMFlux2Pro
  , IMFlux2Schnell
  , IMZImage
  , IMQwenImage2509
  , IMSDXL
  , IMSD3
  , IMDalle3
  , IMMidjourney
  , IMIdeogram2
  ]

-- | All video generation models.
allVideoModels :: Array VideoModel
allVideoModels =
  [ VMWan22
  , VMWan21
  , VMCogVideoX
  , VMCogVideoX5B
  , VMSVD
  , VMSVDXT
  , VMATI
  , VMRunway
  , VMKling
  , VMPika
  , VMLuma
  , VMHunyuanVideo
  ]

-- | All 3D generation models.
all3DModels :: Array Model3D
all3DModels =
  [ M3DHunyuan3D
  , M3DTrellis2
  , M3DTripoSR
  , M3DLGMesh
  , M3DInstant3D
  , M3DZero123Plus
  , M3DMeshAnything
  ]

-- | All image editing models.
allEditModels :: Array EditModel
allEditModels =
  [ EMQwenImageEdit2511
  , EMZImageEdit
  , EMInstructPix2Pix
  , EMSDEdit
  , EMControlNetInpaint
  , EMFluxFill
  ]

-- | All motion control models.
allMotionModels :: Array MotionModel
allMotionModels =
  [ MMMotionCtrl
  , MMUni3C
  , MMWanMove
  , MMTimeToMove
  , MMCameraCtrl
  , MMAnimateDiff
  , MMDragAnything
  ]

-- | Filter models by a predicate.
-- |
-- | Example: `filterImageModels isImageModelFast` returns only fast models.
filterImageModels :: (ImageModel -> Boolean) -> Array ImageModel
filterImageModels pred = Array.filter pred allImageModels

-- | Filter video models by a predicate.
filterVideoModels :: (VideoModel -> Boolean) -> Array VideoModel
filterVideoModels pred = Array.filter pred allVideoModels

-- | Get all models that support a minimum frame count.
videoModelsWithMinFrames :: Int -> Array VideoModel
videoModelsWithMinFrames minFrames = 
  filterVideoModels $ \m -> videoModelMaxFrames m >= minFrames

-- | Get all models that support a minimum resolution.
videoModelsWithMinResolution :: Int -> Array VideoModel
videoModelsWithMinResolution minRes =
  filterVideoModels $ \m -> videoModelMaxResolution m >= minRes

-- | Map a function over all image models.
-- |
-- | Useful for building UI components or serialization.
mapImageModels :: forall a. (ImageModel -> a) -> Array a
mapImageModels f = map f allImageModels

-- | Map a function over all video models.
mapVideoModels :: forall a. (VideoModel -> a) -> Array a
mapVideoModels f = map f allVideoModels

-- | Map a function over all 3D models.
map3DModels :: forall a. (Model3D -> a) -> Array a
map3DModels f = map f all3DModels

-- | Map a function over all edit models.
mapEditModels :: forall a. (EditModel -> a) -> Array a
mapEditModels f = map f allEditModels

-- | Map a function over all motion models.
mapMotionModels :: forall a. (MotionModel -> a) -> Array a
mapMotionModels f = map f allMotionModels

-- | Compose model lookup with transformation.
-- |
-- | Example: `lookupAndTransform imageModelFromString imageModelToString`
-- | creates a round-trip function.
lookupAndTransform 
  :: forall a b
   . (String -> Maybe a) 
  -> (a -> b) 
  -> String 
  -> Maybe b
lookupAndTransform lookup transform = (map transform) <<< lookup

-- | First image model in enumeration order (for default values).
-- |
-- | Uses Bounded instance - change the instance to change the default.
firstImageModel :: ImageModel
firstImageModel = bottom

-- | Last image model in enumeration order.
-- |
-- | Uses Bounded instance.
lastImageModel :: ImageModel
lastImageModel = top

-- | First video model in enumeration order.
-- |
-- | Uses Bounded instance - change the instance to change the default.
firstVideoModel :: VideoModel
firstVideoModel = bottom

-- | Last video model in enumeration order.
-- |
-- | Uses Bounded instance.
lastVideoModel :: VideoModel
lastVideoModel = top

-- | First 3D model in enumeration order.
first3DModel :: Model3D
first3DModel = bottom

-- | Last 3D model in enumeration order.
last3DModel :: Model3D
last3DModel = top

-- | First edit model in enumeration order.
firstEditModel :: EditModel
firstEditModel = bottom

-- | Last edit model in enumeration order.
lastEditModel :: EditModel
lastEditModel = top

-- | First motion model in enumeration order.
firstMotionModel :: MotionModel
firstMotionModel = bottom

-- | Last motion model in enumeration order.
lastMotionModel :: MotionModel
lastMotionModel = top
