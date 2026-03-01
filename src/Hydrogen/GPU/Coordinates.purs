-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // gpu // coordinates
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Coordinates — Bounded geometric types for GPU rendering.
-- |
-- | ## Design Philosophy
-- |
-- | Raw `Number` types allow invalid states: negative widths, NaN coordinates,
-- | infinite depths. At billion-agent scale, these edge cases cause cascading
-- | failures. Bounded types eliminate entire classes of bugs by construction.
-- |
-- | ## Clamping Semantics
-- |
-- | All types use CLAMPING, not error. Why?
-- | - Errors propagate and require handling at every call site
-- | - Clamping provides deterministic "best effort" rendering
-- | - An element slightly off-screen clamps to edge rather than crashing
-- | - Animation interpolation naturally handles overshoots
-- |
-- | ## Bounds Rationale
-- |
-- | - `ScreenX`, `ScreenY`: Signed to support off-screen positioning for
-- |   animations and clipping calculations. Bounded to ±32768 (typical max
-- |   texture size in WebGPU).
-- |
-- | - `PixelWidth`, `PixelHeight`: Non-negative dimensions. Zero is valid
-- |   (invisible element). Upper bound 32768 matches texture limits.
-- |
-- | - `DepthValue`: 24-bit normalized depth buffer range [0.0, 1.0].
-- |   0.0 = near plane, 1.0 = far plane. Clamped to valid range.
-- |
-- | - `DepthLayer`: Integer z-index for painter's algorithm. Bounded to
-- |   ±2147483647 (full Int range) since z-ordering is relative.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Semiring, Ring)
-- | - Hydrogen.Schema.Bounded (clamping functions, bounds documentation)
-- |
-- | ## Dependents
-- |
-- | - Hydrogen.GPU.DrawCommand (all parameter types)
-- | - Hydrogen.GPU.Flatten (coordinate conversion)
-- | - Hydrogen.GPU.Binary (serialization)

module Hydrogen.GPU.Coordinates
  ( -- * Screen Coordinates
    ScreenX(ScreenX)
  , screenX
  , unwrapScreenX
  , screenXBounds
  , screenXZero
  
  , ScreenY(ScreenY)
  , screenY
  , unwrapScreenY
  , screenYBounds
  , screenYZero
  
  -- * Pixel Dimensions
  , PixelWidth(PixelWidth)
  , pixelWidth
  , unwrapPixelWidth
  , pixelWidthBounds
  , pixelWidthZero
  
  , PixelHeight(PixelHeight)
  , pixelHeight
  , unwrapPixelHeight
  , pixelHeightBounds
  , pixelHeightZero
  
  -- * Depth Values
  , DepthValue(DepthValue)
  , depthValue
  , unwrapDepthValue
  , depthValueBounds
  , depthValueNear
  , depthValueFar
  , depthValueMid
  
  , DepthLayer(DepthLayer)
  , depthLayer
  , unwrapDepthLayer
  , depthLayerBounds
  , depthLayerBase
  
  -- * Normalized Coordinates (0.0-1.0)
  , NormalizedX(NormalizedX)
  , normalizedX
  , unwrapNormalizedX
  
  , NormalizedY(NormalizedY)
  , normalizedY
  , unwrapNormalizedY
  
  -- * Operations
  , addScreenX
  , addScreenY
  , scaleScreenX
  , scaleScreenY
  , addPixelWidth
  , addPixelHeight
  , scalePixelWidth
  , scalePixelHeight
  , lerpDepthValue
  
  -- * Conversions
  , screenXToNumber
  , screenYToNumber
  , pixelWidthToNumber
  , pixelHeightToNumber
  , depthValueToNumber
  , depthLayerToInt
  
  -- * From Device.Pixel
  , screenXFromPixel
  , screenYFromPixel
  , pixelWidthFromPixel
  , pixelHeightFromPixel
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Ring
  , class Semiring
  , class Show
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Dimension.Device as Device

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum screen coordinate (matches typical WebGPU max texture dimension)
maxScreenCoord :: Number
maxScreenCoord = 32768.0

-- | Minimum screen coordinate (negative for off-screen positioning)
minScreenCoord :: Number
minScreenCoord = -32768.0

-- | Maximum pixel dimension
maxPixelDim :: Number
maxPixelDim = 32768.0

-- | Maximum z-index layer
maxDepthLayer :: Int
maxDepthLayer = 2147483647

-- | Minimum z-index layer
minDepthLayer :: Int
minDepthLayer = -2147483647

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // screen coordinates
-- ═════════════════════════════════════════════════════════════════════════════

-- | X coordinate on screen.
-- |
-- | Bounded to [-32768, 32768] to support off-screen positioning while
-- | staying within GPU texture coordinate limits.
-- |
-- | Negative values represent positions to the left of the viewport origin.
-- | Values exceeding viewport width represent positions to the right.
newtype ScreenX = ScreenX Number

derive instance eqScreenX :: Eq ScreenX
derive instance ordScreenX :: Ord ScreenX

instance showScreenX :: Show ScreenX where
  show (ScreenX n) = "ScreenX(" <> show n <> ")"

instance semiringScreenX :: Semiring ScreenX where
  add (ScreenX a) (ScreenX b) = screenX (a + b)
  zero = ScreenX 0.0
  mul (ScreenX a) (ScreenX b) = screenX (a * b)
  one = ScreenX 1.0

instance ringScreenX :: Ring ScreenX where
  sub (ScreenX a) (ScreenX b) = screenX (a - b)

-- | Bounds documentation for ScreenX.
screenXBounds :: Bounded.NumberBounds
screenXBounds = Bounded.numberBounds 
  minScreenCoord 
  maxScreenCoord 
  Bounded.Clamps 
  "ScreenX" 
  "X coordinate on screen, supports off-screen positioning"

-- | Smart constructor for ScreenX. Clamps to valid range.
screenX :: Number -> ScreenX
screenX n = ScreenX (Bounded.clampNumber minScreenCoord maxScreenCoord n)

-- | Extract the underlying Number from ScreenX.
unwrapScreenX :: ScreenX -> Number
unwrapScreenX (ScreenX n) = n

-- | ScreenX at origin.
screenXZero :: ScreenX
screenXZero = ScreenX 0.0

-- | Y coordinate on screen.
-- |
-- | Bounded to [-32768, 32768]. Positive Y is typically downward in screen
-- | coordinates (matching CSS/DOM convention).
newtype ScreenY = ScreenY Number

derive instance eqScreenY :: Eq ScreenY
derive instance ordScreenY :: Ord ScreenY

instance showScreenY :: Show ScreenY where
  show (ScreenY n) = "ScreenY(" <> show n <> ")"

instance semiringScreenY :: Semiring ScreenY where
  add (ScreenY a) (ScreenY b) = screenY (a + b)
  zero = ScreenY 0.0
  mul (ScreenY a) (ScreenY b) = screenY (a * b)
  one = ScreenY 1.0

instance ringScreenY :: Ring ScreenY where
  sub (ScreenY a) (ScreenY b) = screenY (a - b)

-- | Bounds documentation for ScreenY.
screenYBounds :: Bounded.NumberBounds
screenYBounds = Bounded.numberBounds 
  minScreenCoord 
  maxScreenCoord 
  Bounded.Clamps 
  "ScreenY" 
  "Y coordinate on screen, supports off-screen positioning"

-- | Smart constructor for ScreenY. Clamps to valid range.
screenY :: Number -> ScreenY
screenY n = ScreenY (Bounded.clampNumber minScreenCoord maxScreenCoord n)

-- | Extract the underlying Number from ScreenY.
unwrapScreenY :: ScreenY -> Number
unwrapScreenY (ScreenY n) = n

-- | ScreenY at origin.
screenYZero :: ScreenY
screenYZero = ScreenY 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pixel dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Width in pixels.
-- |
-- | Non-negative, bounded to [0, 32768]. Zero width is valid (invisible).
-- | Negative inputs clamp to 0.
newtype PixelWidth = PixelWidth Number

derive instance eqPixelWidth :: Eq PixelWidth
derive instance ordPixelWidth :: Ord PixelWidth

instance showPixelWidth :: Show PixelWidth where
  show (PixelWidth n) = "PixelWidth(" <> show n <> ")"

instance semiringPixelWidth :: Semiring PixelWidth where
  add (PixelWidth a) (PixelWidth b) = pixelWidth (a + b)
  zero = PixelWidth 0.0
  mul (PixelWidth a) (PixelWidth b) = pixelWidth (a * b)
  one = PixelWidth 1.0

-- | Bounds documentation for PixelWidth.
pixelWidthBounds :: Bounded.NumberBounds
pixelWidthBounds = Bounded.numberBounds 
  0.0 
  maxPixelDim 
  Bounded.Clamps 
  "PixelWidth" 
  "Width in pixels, non-negative"

-- | Smart constructor for PixelWidth. Clamps to valid range.
pixelWidth :: Number -> PixelWidth
pixelWidth n = PixelWidth (Bounded.clampNumber 0.0 maxPixelDim n)

-- | Extract the underlying Number from PixelWidth.
unwrapPixelWidth :: PixelWidth -> Number
unwrapPixelWidth (PixelWidth n) = n

-- | Zero width (invisible).
pixelWidthZero :: PixelWidth
pixelWidthZero = PixelWidth 0.0

-- | Height in pixels.
-- |
-- | Non-negative, bounded to [0, 32768]. Zero height is valid (invisible).
-- | Negative inputs clamp to 0.
newtype PixelHeight = PixelHeight Number

derive instance eqPixelHeight :: Eq PixelHeight
derive instance ordPixelHeight :: Ord PixelHeight

instance showPixelHeight :: Show PixelHeight where
  show (PixelHeight n) = "PixelHeight(" <> show n <> ")"

instance semiringPixelHeight :: Semiring PixelHeight where
  add (PixelHeight a) (PixelHeight b) = pixelHeight (a + b)
  zero = PixelHeight 0.0
  mul (PixelHeight a) (PixelHeight b) = pixelHeight (a * b)
  one = PixelHeight 1.0

-- | Bounds documentation for PixelHeight.
pixelHeightBounds :: Bounded.NumberBounds
pixelHeightBounds = Bounded.numberBounds 
  0.0 
  maxPixelDim 
  Bounded.Clamps 
  "PixelHeight" 
  "Height in pixels, non-negative"

-- | Smart constructor for PixelHeight. Clamps to valid range.
pixelHeight :: Number -> PixelHeight
pixelHeight n = PixelHeight (Bounded.clampNumber 0.0 maxPixelDim n)

-- | Extract the underlying Number from PixelHeight.
unwrapPixelHeight :: PixelHeight -> Number
unwrapPixelHeight (PixelHeight n) = n

-- | Zero height (invisible).
pixelHeightZero :: PixelHeight
pixelHeightZero = PixelHeight 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // depth values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized depth value for depth buffer.
-- |
-- | Range [0.0, 1.0] mapping to near/far planes:
-- | - 0.0 = near plane (closest to camera)
-- | - 1.0 = far plane (furthest from camera)
-- |
-- | Used for 3D depth testing and compositing order.
newtype DepthValue = DepthValue Number

derive instance eqDepthValue :: Eq DepthValue
derive instance ordDepthValue :: Ord DepthValue

instance showDepthValue :: Show DepthValue where
  show (DepthValue n) = "DepthValue(" <> show n <> ")"

-- | Bounds documentation for DepthValue.
depthValueBounds :: Bounded.NumberBounds
depthValueBounds = Bounded.numberBounds 
  0.0 
  1.0 
  Bounded.Clamps 
  "DepthValue" 
  "Normalized depth buffer value (0=near, 1=far)"

-- | Smart constructor for DepthValue. Clamps to [0.0, 1.0].
depthValue :: Number -> DepthValue
depthValue n = DepthValue (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the underlying Number from DepthValue.
unwrapDepthValue :: DepthValue -> Number
unwrapDepthValue (DepthValue n) = n

-- | Near plane (0.0).
depthValueNear :: DepthValue
depthValueNear = DepthValue 0.0

-- | Far plane (1.0).
depthValueFar :: DepthValue
depthValueFar = DepthValue 1.0

-- | Middle depth (0.5).
depthValueMid :: DepthValue
depthValueMid = DepthValue 0.5

-- | Integer depth layer for painter's algorithm.
-- |
-- | Higher values render on top. Full Int range supported for flexible
-- | layering. Typically used for 2D UI compositing.
newtype DepthLayer = DepthLayer Int

derive instance eqDepthLayer :: Eq DepthLayer
derive instance ordDepthLayer :: Ord DepthLayer

instance showDepthLayer :: Show DepthLayer where
  show (DepthLayer n) = "DepthLayer(" <> show n <> ")"

instance semiringDepthLayer :: Semiring DepthLayer where
  add (DepthLayer a) (DepthLayer b) = depthLayer (a + b)
  zero = DepthLayer 0
  mul (DepthLayer a) (DepthLayer b) = depthLayer (a * b)
  one = DepthLayer 1

instance ringDepthLayer :: Ring DepthLayer where
  sub (DepthLayer a) (DepthLayer b) = depthLayer (a - b)

-- | Bounds documentation for DepthLayer.
depthLayerBounds :: Bounded.IntBounds
depthLayerBounds = Bounded.intBounds 
  minDepthLayer 
  maxDepthLayer 
  Bounded.Clamps 
  "DepthLayer" 
  "Integer z-index for painter's algorithm"

-- | Smart constructor for DepthLayer. Clamps to valid Int range.
depthLayer :: Int -> DepthLayer
depthLayer n = DepthLayer (Bounded.clampInt minDepthLayer maxDepthLayer n)

-- | Extract the underlying Int from DepthLayer.
unwrapDepthLayer :: DepthLayer -> Int
unwrapDepthLayer (DepthLayer n) = n

-- | Base layer (0).
depthLayerBase :: DepthLayer
depthLayerBase = DepthLayer 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // normalized coordinates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized X coordinate [0.0, 1.0].
-- |
-- | Used for UV coordinates, percentage positioning, and viewport-relative
-- | layouts. 0.0 = left edge, 1.0 = right edge.
newtype NormalizedX = NormalizedX Number

derive instance eqNormalizedX :: Eq NormalizedX
derive instance ordNormalizedX :: Ord NormalizedX

instance showNormalizedX :: Show NormalizedX where
  show (NormalizedX n) = "NormalizedX(" <> show n <> ")"

-- | Smart constructor for NormalizedX. Clamps to [0.0, 1.0].
normalizedX :: Number -> NormalizedX
normalizedX n = NormalizedX (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the underlying Number from NormalizedX.
unwrapNormalizedX :: NormalizedX -> Number
unwrapNormalizedX (NormalizedX n) = n

-- | Normalized Y coordinate [0.0, 1.0].
-- |
-- | 0.0 = top edge, 1.0 = bottom edge (screen coordinates).
newtype NormalizedY = NormalizedY Number

derive instance eqNormalizedY :: Eq NormalizedY
derive instance ordNormalizedY :: Ord NormalizedY

instance showNormalizedY :: Show NormalizedY where
  show (NormalizedY n) = "NormalizedY(" <> show n <> ")"

-- | Smart constructor for NormalizedY. Clamps to [0.0, 1.0].
normalizedY :: Number -> NormalizedY
normalizedY n = NormalizedY (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the underlying Number from NormalizedY.
unwrapNormalizedY :: NormalizedY -> Number
unwrapNormalizedY (NormalizedY n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add offset to ScreenX.
addScreenX :: Number -> ScreenX -> ScreenX
addScreenX offset (ScreenX x) = screenX (x + offset)

-- | Add offset to ScreenY.
addScreenY :: Number -> ScreenY -> ScreenY
addScreenY offset (ScreenY y) = screenY (y + offset)

-- | Scale ScreenX by a factor.
scaleScreenX :: Number -> ScreenX -> ScreenX
scaleScreenX factor (ScreenX x) = screenX (x * factor)

-- | Scale ScreenY by a factor.
scaleScreenY :: Number -> ScreenY -> ScreenY
scaleScreenY factor (ScreenY y) = screenY (y * factor)

-- | Add dimensions.
addPixelWidth :: PixelWidth -> PixelWidth -> PixelWidth
addPixelWidth (PixelWidth a) (PixelWidth b) = pixelWidth (a + b)

-- | Add dimensions.
addPixelHeight :: PixelHeight -> PixelHeight -> PixelHeight
addPixelHeight (PixelHeight a) (PixelHeight b) = pixelHeight (a + b)

-- | Scale width by a factor.
scalePixelWidth :: Number -> PixelWidth -> PixelWidth
scalePixelWidth factor (PixelWidth w) = pixelWidth (w * factor)

-- | Scale height by a factor.
scalePixelHeight :: Number -> PixelHeight -> PixelHeight
scalePixelHeight factor (PixelHeight h) = pixelHeight (h * factor)

-- | Linear interpolation between two depth values.
-- |
-- | t = 0.0 returns `from`, t = 1.0 returns `to`.
-- | t is clamped to [0.0, 1.0].
lerpDepthValue :: Number -> DepthValue -> DepthValue -> DepthValue
lerpDepthValue t (DepthValue from) (DepthValue to) =
  let
    t' = Bounded.clampNumber 0.0 1.0 t
  in
    depthValue (from + t' * (to - from))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert ScreenX to Number for interop.
screenXToNumber :: ScreenX -> Number
screenXToNumber = unwrapScreenX

-- | Convert ScreenY to Number for interop.
screenYToNumber :: ScreenY -> Number
screenYToNumber = unwrapScreenY

-- | Convert PixelWidth to Number for interop.
pixelWidthToNumber :: PixelWidth -> Number
pixelWidthToNumber = unwrapPixelWidth

-- | Convert PixelHeight to Number for interop.
pixelHeightToNumber :: PixelHeight -> Number
pixelHeightToNumber = unwrapPixelHeight

-- | Convert DepthValue to Number for interop.
depthValueToNumber :: DepthValue -> Number
depthValueToNumber = unwrapDepthValue

-- | Convert DepthLayer to Int for interop.
depthLayerToInt :: DepthLayer -> Int
depthLayerToInt = unwrapDepthLayer

-- | Create ScreenX from Device.Pixel.
screenXFromPixel :: Device.Pixel -> ScreenX
screenXFromPixel p = screenX (Device.unwrapPixel p)

-- | Create ScreenY from Device.Pixel.
screenYFromPixel :: Device.Pixel -> ScreenY
screenYFromPixel p = screenY (Device.unwrapPixel p)

-- | Create PixelWidth from Device.Pixel.
pixelWidthFromPixel :: Device.Pixel -> PixelWidth
pixelWidthFromPixel p = pixelWidth (Device.unwrapPixel p)

-- | Create PixelHeight from Device.Pixel.
pixelHeightFromPixel :: Device.Pixel -> PixelHeight
pixelHeightFromPixel p = pixelHeight (Device.unwrapPixel p)
