-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // icon // pipeline // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Icon Pipeline Types — T2I → SVG → Mesh generation pipeline.
-- |
-- | This module defines the complete pipeline for generating icons from
-- | text prompts through to brand-colored 3D meshes:
-- |
-- | ```
-- | TextPrompt
-- |     │
-- |     ▼ (T2I: Flux, SDXL, etc.)
-- | GeneratedImage
-- |     │
-- |     ▼ (I2SVG: vectorization)
-- | ExtractedSVG
-- |     │
-- |     ├──► IconDefinition (2D icon)
-- |     │
-- |     ▼ (I2-3D: Trellis2, Hunyuan3D, etc.)
-- | IconMesh
-- |     │
-- |     ▼ (Segmentation + Brand mapping)
-- | BrandedIconMesh
-- | ```
-- |
-- | ## Pipeline Stages
-- |
-- | 1. **T2I (Text-to-Image)**: Generate raster image from prompt
-- | 2. **I2SVG (Image-to-SVG)**: Vectorize to paths (vtracer, potrace)
-- | 3. **SVG Parse**: Extract Path data from SVG
-- | 4. **I2-3D (Image-to-3D)**: Generate mesh from image (Trellis2)
-- | 5. **Segmentation**: Identify mesh regions for coloring
-- | 6. **Brand Mapping**: Assign brand colors to regions
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Each pipeline stage is deterministic given the same inputs and model
-- | weights. Agents can request icons by semantic description and receive
-- | consistent, brand-aligned results.

module Hydrogen.Icon.Pipeline.Types
  ( -- * Pipeline Request
    IconPipelineRequest
  , mkIconPipelineRequest
  , IconPrompt
  , IconStylePrompt
  , IconBaseStyle
      ( StyleMinimal
      , StyleDetailed
      , StyleIsometric
      , StyleGlyph
      , StyleIllustrative
      )
  , IconColorMode
      ( ColorMonochrome
      , ColorDuotone
      , ColorMulti
      , ColorGradient
      )
  , IconComplexity
      ( ComplexitySimple
      , ComplexityMedium
      , ComplexityComplex
      )
  
  -- * T2I Stage
  , T2IRequest
  , T2IResult
  , T2IModel
      ( T2IFlux2Schnell
      , T2IFlux2Dev
      , T2IFlux2Pro
      , T2ISDXL
      , T2IIdeogram2
      )
  , allT2IModels
  , t2iModelToString
  , ImageData
  , ImageFormat
      ( FormatPNG
      , FormatJPEG
      , FormatWebP
      )
  
  -- * I2SVG Stage  
  , I2SVGRequest
  , I2SVGResult
  , ExtractedPath
  , VectorizationMethod
      ( VMPotrace
      , VMVtracer
      , VMAutotrace
      , VMImageTracerJS
      )
  , allVectorizationMethods
  , VectorizationParams
  , VectorizationColorMode
      ( VCMBinary
      , VCMGrayscale
      , VCMColor
      , VCMQuantized
      )
  , defaultVectorizationParams
  
  -- * I2-3D Stage
  , I23DRequest
  , I23DResult
  , I23DModel
      ( I23DTrellis2
      , I23DHunyuan3D
      , I23DTripoSR
      , I23DInstant3D
      , I23DMeshAnything
      )
  , allI23DModels
  , i23DModelToString
  , MeshOutputFormat
      ( MeshGLTF
      , MeshOBJ
      , MeshFBX
      , MeshUSD
      )
  , MeshSimplification
      ( MeshFull
      , MeshMedium
      , MeshLow
      , MeshCustom
      )
  , IconMesh
  , UVMapping
  , MeshBounds
  
  -- * Mesh Segmentation
  , MeshSegment
  , MeshCentroid
  , SegmentId
      ( SegmentId
      )
  , mkSegmentId
  , unSegmentId
  , segmentIdEq
  , SegmentationResult
  
  -- * Brand Mapping
  , BrandMapping
  , BrandMappingEntry
  , BrandedMeshRegion
  , BrandedIconMesh
  
  -- * Pipeline Result
  , IconPipelineResult
      ( PipelineSuccess
      , PipelinePartial
      , PipelineFailure
      )
  , IconPipelineOutput
  , PipelineStage
      ( StageT2I
      , StageI2SVG
      , StageSVGParse
      , StageI23D
      , StageSegmentation
      , StageBrandMapping
      )
  , PipelineError
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String

import Hydrogen.Schema.Geometry.Path.Types (Path)
import Hydrogen.Schema.Brand.Token.Color (ColorRole)
import Hydrogen.Schema.Color.OKLCH (OKLCH)
import Hydrogen.Schema.Dimension.Physical.SI (Meter)
import Hydrogen.GPU.Scene3D.Mesh (Mesh3D)

import Hydrogen.Icon.Types
  ( IconDefinition
  , IconName
  , IconCategory
  , IconViewBox
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // pipeline // request
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete pipeline request for icon generation.
-- |
-- | Specifies what to generate, how to generate it, and brand constraints.
type IconPipelineRequest =
  { -- Identification
    name :: IconName
  , category :: IconCategory
  , tags :: Array String
  
  -- Generation prompt
  , prompt :: IconPrompt
  
  -- Pipeline configuration
  , t2iModel :: T2IModel
  , vectorization :: VectorizationMethod
  , generate3D :: Boolean              -- Whether to also generate 3D mesh
  , i23DModel :: Maybe I23DModel       -- Model for 3D generation
  
  -- Brand constraints
  , brandMapping :: Maybe BrandMapping  -- How to map regions to brand colors
  }

-- | Create a pipeline request with defaults.
mkIconPipelineRequest :: IconName -> IconCategory -> IconPrompt -> IconPipelineRequest
mkIconPipelineRequest name category prompt =
  { name: name
  , category: category
  , tags: []
  , prompt: prompt
  , t2iModel: T2IFlux2Schnell  -- Fast default
  , vectorization: VMPotrace
  , generate3D: false
  , i23DModel: Nothing
  , brandMapping: Nothing
  }

-- | Icon generation prompt.
-- |
-- | Contains the text description and style guidance for T2I.
type IconPrompt =
  { description :: String        -- What the icon represents ("shopping cart")
  , style :: IconStylePrompt     -- Visual style guidance
  , negativePrompt :: Maybe String  -- What to avoid
  }

-- | Style guidance for icon generation.
-- |
-- | Helps T2I models produce icon-appropriate output.
type IconStylePrompt =
  { baseStyle :: IconBaseStyle
  , colorMode :: IconColorMode
  , complexity :: IconComplexity
  }

-- | Base visual style for icons.
data IconBaseStyle
  = StyleMinimal      -- ^ Clean lines, simple shapes
  | StyleDetailed     -- ^ Rich detail, gradients
  | StyleIsometric    -- ^ 3D isometric projection
  | StyleGlyph        -- ^ Single-stroke glyph style
  | StyleIllustrative -- ^ Hand-drawn illustration feel

derive instance eqIconBaseStyle :: Eq IconBaseStyle
derive instance ordIconBaseStyle :: Ord IconBaseStyle

instance showIconBaseStyle :: Show IconBaseStyle where
  show StyleMinimal = "minimal"
  show StyleDetailed = "detailed"
  show StyleIsometric = "isometric"
  show StyleGlyph = "glyph"
  show StyleIllustrative = "illustrative"

-- | Color mode for generated icons.
data IconColorMode
  = ColorMonochrome   -- ^ Single color (will use brand primary)
  | ColorDuotone      -- ^ Two colors (primary + secondary)
  | ColorMulti        -- ^ Multiple colors (requires segmentation)
  | ColorGradient     -- ^ Gradient fills

derive instance eqIconColorMode :: Eq IconColorMode
derive instance ordIconColorMode :: Ord IconColorMode

instance showIconColorMode :: Show IconColorMode where
  show ColorMonochrome = "monochrome"
  show ColorDuotone = "duotone"
  show ColorMulti = "multi"
  show ColorGradient = "gradient"

-- | Complexity level for icons.
data IconComplexity
  = ComplexitySimple    -- ^ Few shapes, fast to render
  | ComplexityMedium    -- ^ Moderate detail
  | ComplexityComplex   -- ^ High detail, many paths

derive instance eqIconComplexity :: Eq IconComplexity
derive instance ordIconComplexity :: Ord IconComplexity

instance showIconComplexity :: Show IconComplexity where
  show ComplexitySimple = "simple"
  show ComplexityMedium = "medium"
  show ComplexityComplex = "complex"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // t2i // stage
-- ═════════════════════════════════════════════════════════════════════════════

-- | T2I model selection for icon generation.
-- |
-- | Subset of ImageModel from Diffusion.Model optimized for icons.
data T2IModel
  = T2IFlux2Schnell   -- ^ Fast iteration (recommended for icons)
  | T2IFlux2Dev       -- ^ Higher quality, slower
  | T2IFlux2Pro       -- ^ Highest quality
  | T2ISDXL           -- ^ Stable Diffusion XL
  | T2IIdeogram2      -- ^ Good for text/symbols

derive instance eqT2IModel :: Eq T2IModel
derive instance ordT2IModel :: Ord T2IModel

instance showT2IModel :: Show T2IModel where
  show = t2iModelToString

-- | Convert T2I model to string.
t2iModelToString :: T2IModel -> String
t2iModelToString T2IFlux2Schnell = "flux2-schnell"
t2iModelToString T2IFlux2Dev = "flux2-dev"
t2iModelToString T2IFlux2Pro = "flux2-pro"
t2iModelToString T2ISDXL = "sdxl"
t2iModelToString T2IIdeogram2 = "ideogram2"

-- | All available T2I models.
allT2IModels :: Array T2IModel
allT2IModels =
  [ T2IFlux2Schnell
  , T2IFlux2Dev
  , T2IFlux2Pro
  , T2ISDXL
  , T2IIdeogram2
  ]

-- | T2I generation request.
type T2IRequest =
  { prompt :: String
  , negativePrompt :: Maybe String
  , model :: T2IModel
  , width :: Int               -- Output width (bounded: 256-2048)
  , height :: Int              -- Output height (bounded: 256-2048)
  , seed :: Maybe Int          -- For reproducibility
  , steps :: Int               -- Inference steps (bounded: 1-100)
  , guidanceScale :: Number    -- CFG scale (bounded: 1.0-20.0)
  }

-- | T2I generation result.
-- |
-- | Contains the generated image as raw bytes (PNG format).
type T2IResult =
  { imageData :: ImageData
  , width :: Int
  , height :: Int
  , model :: T2IModel
  , seed :: Int                -- Actual seed used
  }

-- | Raw image data (PNG bytes).
-- |
-- | Opaque type - actual bytes handled by backend.
type ImageData = 
  { format :: ImageFormat
  , byteLength :: Int
  }

-- | Supported image formats.
data ImageFormat
  = FormatPNG
  | FormatJPEG
  | FormatWebP

derive instance eqImageFormat :: Eq ImageFormat

instance showImageFormat :: Show ImageFormat where
  show FormatPNG = "png"
  show FormatJPEG = "jpeg"
  show FormatWebP = "webp"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // i2svg // stage
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vectorization method for converting raster to SVG.
data VectorizationMethod
  = VMPotrace       -- ^ Potrace (good for simple icons)
  | VMVtracer       -- ^ vtracer (good for detailed images)
  | VMAutotrace     -- ^ Autotrace
  | VMImageTracerJS -- ^ Browser-based (for client-side)

derive instance eqVectorizationMethod :: Eq VectorizationMethod
derive instance ordVectorizationMethod :: Ord VectorizationMethod

instance showVectorizationMethod :: Show VectorizationMethod where
  show VMPotrace = "potrace"
  show VMVtracer = "vtracer"
  show VMAutotrace = "autotrace"
  show VMImageTracerJS = "imagetracerjs"

-- | All vectorization methods.
allVectorizationMethods :: Array VectorizationMethod
allVectorizationMethods =
  [ VMPotrace
  , VMVtracer
  , VMAutotrace
  , VMImageTracerJS
  ]

-- | Vectorization parameters.
type VectorizationParams =
  { method :: VectorizationMethod
  , colorMode :: VectorizationColorMode
  , pathSimplification :: Number    -- 0.0-1.0, higher = simpler paths
  , cornerThreshold :: Number       -- Angle threshold for corners (degrees)
  , curveOptimization :: Boolean    -- Optimize curves vs line segments
  }

-- | How to handle colors during vectorization.
data VectorizationColorMode
  = VCMBinary        -- ^ Black and white only
  | VCMGrayscale     -- ^ Grayscale levels
  | VCMColor         -- ^ Preserve colors
  | VCMQuantized Int -- ^ Reduce to N colors

derive instance eqVectorizationColorMode :: Eq VectorizationColorMode

instance showVectorizationColorMode :: Show VectorizationColorMode where
  show VCMBinary = "binary"
  show VCMGrayscale = "grayscale"
  show VCMColor = "color"
  show (VCMQuantized n) = "quantized-" <> show n

-- | Default vectorization parameters for icons.
defaultVectorizationParams :: VectorizationParams
defaultVectorizationParams =
  { method: VMPotrace
  , colorMode: VCMBinary
  , pathSimplification: 0.5
  , cornerThreshold: 60.0
  , curveOptimization: true
  }

-- | I2SVG request.
type I2SVGRequest =
  { imageData :: ImageData
  , params :: VectorizationParams
  , targetViewBox :: IconViewBox     -- Scale output to this viewBox
  }

-- | I2SVG result.
type I2SVGResult =
  { paths :: Array ExtractedPath     -- Extracted paths with colors
  , viewBox :: IconViewBox
  , pathCount :: Int
  }

-- | A single extracted path with its detected color.
type ExtractedPath =
  { path :: Path
  , fillColor :: Maybe OKLCH         -- Detected fill color
  , strokeColor :: Maybe OKLCH       -- Detected stroke color
  , strokeWidth :: Maybe Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // i2-3d // stage
-- ═════════════════════════════════════════════════════════════════════════════

-- | I2-3D model selection.
-- |
-- | Subset of Model3D from Diffusion.Model for icon mesh generation.
data I23DModel
  = I23DTrellis2      -- ^ Trellis 2 (Microsoft) - recommended
  | I23DHunyuan3D     -- ^ Hunyuan 3D (Tencent)
  | I23DTripoSR       -- ^ TripoSR (Stability AI)
  | I23DInstant3D     -- ^ Instant3D
  | I23DMeshAnything  -- ^ MeshAnything

derive instance eqI23DModel :: Eq I23DModel
derive instance ordI23DModel :: Ord I23DModel

instance showI23DModel :: Show I23DModel where
  show = i23DModelToString

-- | Convert I2-3D model to string.
i23DModelToString :: I23DModel -> String
i23DModelToString I23DTrellis2 = "trellis2"
i23DModelToString I23DHunyuan3D = "hunyuan3d"
i23DModelToString I23DTripoSR = "triposr"
i23DModelToString I23DInstant3D = "instant3d"
i23DModelToString I23DMeshAnything = "meshanything"

-- | All I2-3D models.
allI23DModels :: Array I23DModel
allI23DModels =
  [ I23DTrellis2
  , I23DHunyuan3D
  , I23DTripoSR
  , I23DInstant3D
  , I23DMeshAnything
  ]

-- | I2-3D generation request.
type I23DRequest =
  { imageData :: ImageData
  , model :: I23DModel
  , outputFormat :: MeshOutputFormat
  , simplification :: MeshSimplification
  }

-- | Mesh output format.
data MeshOutputFormat
  = MeshGLTF         -- ^ glTF 2.0 (recommended)
  | MeshOBJ          -- ^ Wavefront OBJ
  | MeshFBX          -- ^ FBX
  | MeshUSD          -- ^ Universal Scene Description

derive instance eqMeshOutputFormat :: Eq MeshOutputFormat

instance showMeshOutputFormat :: Show MeshOutputFormat where
  show MeshGLTF = "gltf"
  show MeshOBJ = "obj"
  show MeshFBX = "fbx"
  show MeshUSD = "usd"

-- | Mesh simplification level.
data MeshSimplification
  = MeshFull         -- ^ Full detail from model
  | MeshMedium       -- ^ Reduced polygon count
  | MeshLow          -- ^ Low-poly for performance
  | MeshCustom Int   -- ^ Target face count

derive instance eqMeshSimplification :: Eq MeshSimplification

instance showMeshSimplification :: Show MeshSimplification where
  show MeshFull = "full"
  show MeshMedium = "medium"
  show MeshLow = "low"
  show (MeshCustom n) = "custom-" <> show n

-- | I2-3D generation result.
type I23DResult =
  { mesh :: IconMesh
  , model :: I23DModel
  , faceCount :: Int
  , vertexCount :: Int
  }

-- | Generated icon mesh.
-- |
-- | Contains the 3D geometry plus UV coordinates for texturing.
type IconMesh =
  { geometry :: Mesh3D
  , uvMapping :: UVMapping
  , bounds :: MeshBounds
  }

-- | UV mapping for mesh texturing.
type UVMapping =
  { hasUVs :: Boolean
  , uvChannels :: Int            -- Number of UV sets
  }

-- | Axis-aligned bounding box.
type MeshBounds =
  { minX :: Meter
  , minY :: Meter
  , minZ :: Meter
  , maxX :: Meter
  , maxY :: Meter
  , maxZ :: Meter
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // mesh // segmentation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Segment identifier for mesh regions.
newtype SegmentId = SegmentId String

derive instance eqSegmentId :: Eq SegmentId
derive instance ordSegmentId :: Ord SegmentId

instance showSegmentId :: Show SegmentId where
  show (SegmentId s) = "(SegmentId " <> show s <> ")"

-- | Create a segment ID (bounded: 1-32 chars).
mkSegmentId :: String -> Maybe SegmentId
mkSegmentId s
  | String.length s >= 1 && String.length s <= 32 = Just (SegmentId s)
  | true = Nothing

-- | Extract raw string from segment ID.
unSegmentId :: SegmentId -> String
unSegmentId (SegmentId s) = s

-- | Check if two segment IDs are equal.
-- |
-- | Used for brand mapping validation.
segmentIdEq :: SegmentId -> SegmentId -> Boolean
segmentIdEq (SegmentId a) (SegmentId b) = a == b

-- | A mesh segment (region that can be colored independently).
type MeshSegment =
  { id :: SegmentId
  , faceIndices :: Array Int       -- Which faces belong to this segment
  , centroid :: MeshCentroid       -- Center of segment for UI
  , area :: Number                 -- Relative area (0-1)
  }

-- | Centroid position in mesh space.
type MeshCentroid =
  { x :: Meter
  , y :: Meter
  , z :: Meter
  }

-- | Result of mesh segmentation.
type SegmentationResult =
  { segments :: Array MeshSegment
  , segmentCount :: Int
  , coveragePercent :: Number      -- How much of mesh is segmented (0-100)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // brand // mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Brand color mapping for icon regions.
-- |
-- | Maps segment IDs to brand color roles.
type BrandMapping =
  { mappings :: Array BrandMappingEntry
  , defaultRole :: ColorRole       -- Fallback for unmapped segments
  }

-- | Single mapping entry.
type BrandMappingEntry =
  { segmentId :: SegmentId
  , colorRole :: ColorRole
  }

-- | A mesh region with assigned brand color.
type BrandedMeshRegion =
  { segment :: MeshSegment
  , colorRole :: ColorRole
  , resolvedColor :: OKLCH         -- Actual color from brand palette
  }

-- | Complete branded icon mesh.
type BrandedIconMesh =
  { mesh :: IconMesh
  , regions :: Array BrandedMeshRegion
  , brandId :: Maybe String        -- Which brand palette was used
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // pipeline // result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pipeline stage identifier.
data PipelineStage
  = StageT2I
  | StageI2SVG
  | StageSVGParse
  | StageI23D
  | StageSegmentation
  | StageBrandMapping

derive instance eqPipelineStage :: Eq PipelineStage

instance showPipelineStage :: Show PipelineStage where
  show StageT2I = "t2i"
  show StageI2SVG = "i2svg"
  show StageSVGParse = "svg-parse"
  show StageI23D = "i2-3d"
  show StageSegmentation = "segmentation"
  show StageBrandMapping = "brand-mapping"

-- | Pipeline error.
type PipelineError =
  { stage :: PipelineStage
  , message :: String
  , recoverable :: Boolean
  }

-- | Complete pipeline result.
data IconPipelineResult
  = PipelineSuccess IconPipelineOutput
  | PipelinePartial IconPipelineOutput PipelineError  -- Partial success
  | PipelineFailure PipelineError

derive instance eqIconPipelineResult :: Eq IconPipelineResult

-- | Successful pipeline output.
type IconPipelineOutput =
  { -- 2D Icon (always present on success)
    icon2D :: IconDefinition
  
  -- 3D Mesh (optional, if generate3D was true)
  , icon3D :: Maybe BrandedIconMesh
  
  -- Intermediate results (for debugging/inspection)
  , t2iResult :: Maybe T2IResult
  , i2svgResult :: Maybe I2SVGResult
  , i23DResult :: Maybe I23DResult
  , segmentationResult :: Maybe SegmentationResult
  }
