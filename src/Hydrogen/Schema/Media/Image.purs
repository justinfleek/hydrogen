-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // media // image
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Image — Pure image manipulation state and commands.
-- |
-- | ## Design Philosophy
-- |
-- | Image manipulation is modeled as pure state transformations. No Canvas
-- | or ImageData APIs leak into this module. The runtime interprets commands
-- | against actual image elements or canvas contexts.
-- |
-- | This enables:
-- | - Deterministic crop/rotate/flip operations
-- | - Server-side image operation planning
-- | - Agent composition of image editing interfaces
-- |
-- | ## Bounded Types
-- |
-- | All values use bounded types:
-- | - Zoom: [0.1, 10.0] clamped
-- | - Rotation: [0, 360) wrapping degrees
-- | - Crop coordinates: non-negative, bounded by image size
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (bounded type foundations)
-- | - Hydrogen.Schema.Dimension.Rect (bounding rectangles)
-- | - Hydrogen.Schema.Geometry.Angle (rotation)
-- |
-- | ## Dependents
-- |
-- | - Component.ImageEditor (image editing UI)
-- | - Component.AvatarCrop (avatar cropping)
-- | - Component.PhotoGallery (thumbnail generation)

module Hydrogen.Schema.Media.Image
  ( -- * Scale Factor
    ScaleFactor
  , scaleFactor
  , unwrapScaleFactor
  , scaleFactorOne
  , scaleFactorHalf
  , scaleFactorDouble
  , scaleFactorBounds
  
  -- * Flip State
  , FlipState
  , FlipAxis(FlipX, FlipY)
  , flipNone
  , flipHorizontal
  , flipVertical
  , flipBoth
  , toggleFlipX
  , toggleFlipY
  , isFlippedX
  , isFlippedY
  
  -- * Rotation
  , Rotation
  , rotation
  , rotationFromDegrees
  , unwrapRotation
  , toDegrees
  , rotationZero
  , rotation90
  , rotation180
  , rotation270
  , rotateClockwise
  , rotateCounterClockwise
  , rotationBounds
  
  -- * Crop Area
  , CropArea
  , cropArea
  , cropAreaFromRect
  , cropX
  , cropY
  , cropWidth
  , cropHeight
  , cropToRect
  , cropAreaFullImage
  , constrainCropToImage
  , cropAspectRatio
  
  -- * Crop State
  , CropState
  , initialCropState
  , setCropArea
  , setZoom
  , setRotation
  , setFlip
  , resetCrop
  , applyCropTransform
  
  -- * Image Command
  , ImageCommand(SetCrop, ZoomIn, ZoomOut, SetZoom, RotateCW, RotateCCW, SetRotation, FlipHorizontal, FlipVertical, ResetTransforms)
  , applyImageCommand
  
  -- * Image Dimensions
  , ImageDimensions
  , imageDimensions
  , imageWidth
  , imageHeight
  , imageAspectRatio
  , fitWithinBounds
  , fillBounds
  
  -- * Image Metadata
  , ImageMetadata
  , imageMetadata
  , hasAlpha
  , imageFormat
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
  , not
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Int (floor, toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Dimension.Rect (Rect)
import Hydrogen.Schema.Dimension.Rect as Rect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // scale factor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zoom/scale factor clamped to [0.1, 10.0].
-- |
-- | 1.0 = original size, 2.0 = double size, 0.5 = half size.
-- | Minimum 0.1 (10%) prevents invisible images.
-- | Maximum 10.0 (1000%) prevents excessive memory usage.
newtype ScaleFactor = ScaleFactor Number

derive instance eqScaleFactor :: Eq ScaleFactor
derive instance ordScaleFactor :: Ord ScaleFactor

instance showScaleFactor :: Show ScaleFactor where
  show (ScaleFactor s) = "(ScaleFactor " <> show s <> "x)"

-- | Create a ScaleFactor, clamping to [0.1, 10.0].
scaleFactor :: Number -> ScaleFactor
scaleFactor s
  | s < 0.1 = ScaleFactor 0.1
  | s > 10.0 = ScaleFactor 10.0
  | otherwise = ScaleFactor s

-- | Extract raw scale factor.
unwrapScaleFactor :: ScaleFactor -> Number
unwrapScaleFactor (ScaleFactor s) = s

-- | Original size (1.0x)
scaleFactorOne :: ScaleFactor
scaleFactorOne = ScaleFactor 1.0

-- | Half size (0.5x)
scaleFactorHalf :: ScaleFactor
scaleFactorHalf = ScaleFactor 0.5

-- | Double size (2.0x)
scaleFactorDouble :: ScaleFactor
scaleFactorDouble = ScaleFactor 2.0

-- | Scale factor bounds documentation.
scaleFactorBounds :: Bounded.NumberBounds
scaleFactorBounds = Bounded.numberBounds 0.1 10.0 Bounded.Clamps "scaleFactor"
  "Zoom/scale factor (0.1x to 10.0x)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // flip state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flip axis for image manipulation.
data FlipAxis
  = FlipX     -- ^ Horizontal flip (mirror left-right)
  | FlipY     -- ^ Vertical flip (mirror top-bottom)

derive instance eqFlipAxis :: Eq FlipAxis
derive instance ordFlipAxis :: Ord FlipAxis

instance showFlipAxis :: Show FlipAxis where
  show FlipX = "FlipX"
  show FlipY = "FlipY"

-- | Image flip state (horizontal and vertical).
type FlipState =
  { horizontal :: Boolean   -- ^ Flipped horizontally
  , vertical :: Boolean     -- ^ Flipped vertically
  }

-- | No flip applied.
flipNone :: FlipState
flipNone = { horizontal: false, vertical: false }

-- | Horizontal flip only.
flipHorizontal :: FlipState
flipHorizontal = { horizontal: true, vertical: false }

-- | Vertical flip only.
flipVertical :: FlipState
flipVertical = { horizontal: false, vertical: true }

-- | Both horizontal and vertical flip.
flipBoth :: FlipState
flipBoth = { horizontal: true, vertical: true }

-- | Toggle horizontal flip.
toggleFlipX :: FlipState -> FlipState
toggleFlipX fs = fs { horizontal = not fs.horizontal }

-- | Toggle vertical flip.
toggleFlipY :: FlipState -> FlipState
toggleFlipY fs = fs { vertical = not fs.vertical }

-- | Check if horizontally flipped.
isFlippedX :: FlipState -> Boolean
isFlippedX fs = fs.horizontal

-- | Check if vertically flipped.
isFlippedY :: FlipState -> Boolean
isFlippedY fs = fs.vertical

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // rotation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotation in degrees [0, 360), wrapping.
-- |
-- | Stored as integer degrees for deterministic behavior.
-- | 370 degrees becomes 10 degrees.
newtype Rotation = Rotation Int

derive instance eqRotation :: Eq Rotation
derive instance ordRotation :: Ord Rotation

instance showRotation :: Show Rotation where
  show (Rotation r) = show r <> "deg"

-- | Create a Rotation, wrapping to [0, 360).
rotation :: Int -> Rotation
rotation r = Rotation (wrapDegrees r)

-- | Create from floating point degrees.
rotationFromDegrees :: Number -> Rotation
rotationFromDegrees n = rotation (floorToInt n)

-- | Extract raw rotation value.
unwrapRotation :: Rotation -> Int
unwrapRotation (Rotation r) = r

-- | Convert to degrees as Number.
toDegrees :: Rotation -> Number
toDegrees (Rotation r) = intToNumber r

-- | No rotation (0 degrees)
rotationZero :: Rotation
rotationZero = Rotation 0

-- | 90 degree rotation
rotation90 :: Rotation
rotation90 = Rotation 90

-- | 180 degree rotation
rotation180 :: Rotation
rotation180 = Rotation 180

-- | 270 degree rotation
rotation270 :: Rotation
rotation270 = Rotation 270

-- | Rotate 90 degrees clockwise.
rotateClockwise :: Rotation -> Rotation
rotateClockwise (Rotation r) = rotation (r + 90)

-- | Rotate 90 degrees counter-clockwise.
rotateCounterClockwise :: Rotation -> Rotation
rotateCounterClockwise (Rotation r) = rotation (r - 90)

-- | Wrap degrees to [0, 360).
wrapDegrees :: Int -> Int
wrapDegrees d =
  let m = d - (d / 360) * 360
  in if m < 0 then m + 360 else m

-- | Rotation bounds documentation.
rotationBounds :: Bounded.IntBounds
rotationBounds = Bounded.intBounds 0 360 Bounded.Wraps "rotation"
  "Rotation in degrees (0-360, wraps)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // crop area
-- ═════════════════════════════════════════════════════════════════════════════

-- | Crop area defined by position and size.
-- |
-- | All values are non-negative. Coordinates are relative to image origin.
type CropArea =
  { x :: Number          -- ^ Left edge position
  , y :: Number          -- ^ Top edge position
  , width :: Number      -- ^ Crop width
  , height :: Number     -- ^ Crop height
  }

-- | Create a crop area with validation.
cropArea :: Number -> Number -> Number -> Number -> CropArea
cropArea x' y' w h =
  { x: maxNum 0.0 x'
  , y: maxNum 0.0 y'
  , width: maxNum 0.0 w
  , height: maxNum 0.0 h
  }

-- | Create crop area from Rect.
cropAreaFromRect :: Rect -> CropArea
cropAreaFromRect r =
  { x: Rect.x r
  , y: Rect.y r
  , width: Rect.width r
  , height: Rect.height r
  }

-- | Get crop X position.
cropX :: CropArea -> Number
cropX c = c.x

-- | Get crop Y position.
cropY :: CropArea -> Number
cropY c = c.y

-- | Get crop width.
cropWidth :: CropArea -> Number
cropWidth c = c.width

-- | Get crop height.
cropHeight :: CropArea -> Number
cropHeight c = c.height

-- | Convert crop area to Rect.
cropToRect :: CropArea -> Rect
cropToRect c = Rect.rect c.x c.y c.width c.height

-- | Full image crop area (no cropping).
cropAreaFullImage :: Number -> Number -> CropArea
cropAreaFullImage imgWidth imgHeight =
  { x: 0.0
  , y: 0.0
  , width: maxNum 0.0 imgWidth
  , height: maxNum 0.0 imgHeight
  }

-- | Constrain crop area to fit within image bounds.
constrainCropToImage :: Number -> Number -> CropArea -> CropArea
constrainCropToImage imgWidth imgHeight crop =
  let
    -- Ensure crop doesn't exceed image bounds
    x' = clampNum 0.0 (imgWidth - 1.0) crop.x
    y' = clampNum 0.0 (imgHeight - 1.0) crop.y
    maxW = imgWidth - x'
    maxH = imgHeight - y'
    w' = clampNum 1.0 maxW crop.width
    h' = clampNum 1.0 maxH crop.height
  in
    { x: x', y: y', width: w', height: h' }

-- | Calculate crop area aspect ratio.
cropAspectRatio :: CropArea -> Number
cropAspectRatio c =
  if c.height <= 0.0
  then 1.0
  else c.width / c.height

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // crop state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete crop/transform state for an image.
type CropState =
  { cropArea :: CropArea       -- ^ Current crop region
  , zoom :: ScaleFactor        -- ^ Current zoom level
  , rotation :: Rotation       -- ^ Current rotation
  , flip :: FlipState          -- ^ Current flip state
  , imageWidth :: Number       -- ^ Original image width
  , imageHeight :: Number      -- ^ Original image height
  }

-- | Initialize crop state for an image.
initialCropState :: Number -> Number -> CropState
initialCropState imgWidth imgHeight =
  { cropArea: cropAreaFullImage imgWidth imgHeight
  , zoom: scaleFactorOne
  , rotation: rotationZero
  , flip: flipNone
  , imageWidth: maxNum 1.0 imgWidth
  , imageHeight: maxNum 1.0 imgHeight
  }

-- | Set crop area.
setCropArea :: CropArea -> CropState -> CropState
setCropArea area state =
  state { cropArea = constrainCropToImage state.imageWidth state.imageHeight area }

-- | Set zoom level.
setZoom :: ScaleFactor -> CropState -> CropState
setZoom z state = state { zoom = z }

-- | Set rotation.
setRotation :: Rotation -> CropState -> CropState
setRotation r state = state { rotation = r }

-- | Set flip state.
setFlip :: FlipState -> CropState -> CropState
setFlip f state = state { flip = f }

-- | Reset to original state (no crop, no transform).
resetCrop :: CropState -> CropState
resetCrop state =
  { cropArea: cropAreaFullImage state.imageWidth state.imageHeight
  , zoom: scaleFactorOne
  , rotation: rotationZero
  , flip: flipNone
  , imageWidth: state.imageWidth
  , imageHeight: state.imageHeight
  }

-- | Apply all transforms to get final crop area.
-- |
-- | Returns the effective crop considering zoom and rotation.
applyCropTransform :: CropState -> CropArea
applyCropTransform state =
  let
    z = unwrapScaleFactor state.zoom
    -- Scale crop area by inverse of zoom
    scaled = 
      { x: state.cropArea.x / z
      , y: state.cropArea.y / z
      , width: state.cropArea.width / z
      , height: state.cropArea.height / z
      }
  in
    constrainCropToImage state.imageWidth state.imageHeight scaled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // image command
-- ═════════════════════════════════════════════════════════════════════════════

-- | Commands for image manipulation.
data ImageCommand
  = SetCrop CropArea
  | ZoomIn                      -- ^ Increase zoom by 25%
  | ZoomOut                     -- ^ Decrease zoom by 25%
  | SetZoom ScaleFactor
  | RotateCW                    -- ^ Rotate 90 degrees clockwise
  | RotateCCW                   -- ^ Rotate 90 degrees counter-clockwise
  | SetRotation Rotation
  | FlipHorizontal              -- ^ Toggle horizontal flip
  | FlipVertical                -- ^ Toggle vertical flip
  | ResetTransforms             -- ^ Reset all transforms

derive instance eqImageCommand :: Eq ImageCommand

instance showImageCommand :: Show ImageCommand where
  show (SetCrop c) = "(SetCrop " <> show c.x <> "," <> show c.y <> ")"
  show ZoomIn = "ZoomIn"
  show ZoomOut = "ZoomOut"
  show (SetZoom z) = "(SetZoom " <> show z <> ")"
  show RotateCW = "RotateCW"
  show RotateCCW = "RotateCCW"
  show (SetRotation r) = "(SetRotation " <> show r <> ")"
  show FlipHorizontal = "FlipHorizontal"
  show FlipVertical = "FlipVertical"
  show ResetTransforms = "ResetTransforms"

-- | Apply image command to crop state.
applyImageCommand :: ImageCommand -> CropState -> CropState
applyImageCommand cmd state = case cmd of
  SetCrop area -> setCropArea area state
  ZoomIn ->
    let current = unwrapScaleFactor state.zoom
    in setZoom (scaleFactor (current * 1.25)) state
  ZoomOut ->
    let current = unwrapScaleFactor state.zoom
    in setZoom (scaleFactor (current / 1.25)) state
  SetZoom z -> setZoom z state
  RotateCW -> setRotation (rotateClockwise state.rotation) state
  RotateCCW -> setRotation (rotateCounterClockwise state.rotation) state
  SetRotation r -> setRotation r state
  FlipHorizontal -> setFlip (toggleFlipX state.flip) state
  FlipVertical -> setFlip (toggleFlipY state.flip) state
  ResetTransforms -> resetCrop state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // image dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Image dimensions in pixels.
type ImageDimensions =
  { width :: Int       -- ^ Width in pixels
  , height :: Int      -- ^ Height in pixels
  }

-- | Create image dimensions.
imageDimensions :: Int -> Int -> ImageDimensions
imageDimensions w h =
  { width: maxInt 1 w
  , height: maxInt 1 h
  }

-- | Get image width.
imageWidth :: ImageDimensions -> Int
imageWidth d = d.width

-- | Get image height.
imageHeight :: ImageDimensions -> Int
imageHeight d = d.height

-- | Calculate aspect ratio.
imageAspectRatio :: ImageDimensions -> Number
imageAspectRatio d =
  if d.height == 0
  then 1.0
  else intToNumber d.width / intToNumber d.height

-- | Fit image within bounds while preserving aspect ratio.
-- | Returns scaled dimensions that fit within the bounds.
fitWithinBounds :: Int -> Int -> ImageDimensions -> ImageDimensions
fitWithinBounds maxW maxH dims =
  let
    scaleX = intToNumber maxW / intToNumber dims.width
    scaleY = intToNumber maxH / intToNumber dims.height
    scale = minNum scaleX scaleY
    newW = floorToInt (intToNumber dims.width * scale)
    newH = floorToInt (intToNumber dims.height * scale)
  in
    imageDimensions newW newH

-- | Fill bounds while preserving aspect ratio (may crop).
fillBounds :: Int -> Int -> ImageDimensions -> ImageDimensions
fillBounds targetW targetH dims =
  let
    scaleX = intToNumber targetW / intToNumber dims.width
    scaleY = intToNumber targetH / intToNumber dims.height
    scale = maxNum scaleX scaleY
    newW = floorToInt (intToNumber dims.width * scale)
    newH = floorToInt (intToNumber dims.height * scale)
  in
    imageDimensions newW newH

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // image metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Image file metadata.
type ImageMetadata =
  { dimensions :: ImageDimensions  -- ^ Image size
  , format :: String               -- ^ Image format (e.g., "jpeg", "png")
  , hasAlphaChannel :: Boolean     -- ^ Has transparency
  , colorDepth :: Int              -- ^ Bits per pixel
  , fileSize :: Maybe Int          -- ^ File size in bytes
  }

-- | Create image metadata.
imageMetadata :: Int -> Int -> String -> ImageMetadata
imageMetadata w h fmt =
  { dimensions: imageDimensions w h
  , format: fmt
  , hasAlphaChannel: fmt == "png" || fmt == "webp" || fmt == "gif"
  , colorDepth: 24
  , fileSize: Nothing
  }

-- | Check if image has alpha channel.
hasAlpha :: ImageMetadata -> Boolean
hasAlpha m = m.hasAlphaChannel

-- | Get image format.
imageFormat :: ImageMetadata -> String
imageFormat m = m.format

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum of two numbers.
maxNum :: Number -> Number -> Number
maxNum a b = if a >= b then a else b

-- | Minimum of two numbers.
minNum :: Number -> Number -> Number
minNum a b = if a <= b then a else b

-- | Clamp number to range.
clampNum :: Number -> Number -> Number -> Number
clampNum minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n

-- | Maximum of two integers.
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Floor Number to Int.
floorToInt :: Number -> Int
floorToInt = Int.floor

-- | Convert Int to Number.
intToNumber :: Int -> Number
intToNumber = Int.toNumber
