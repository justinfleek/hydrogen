-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // framestate // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport — Display Surface State and Shape
-- |
-- | ## Purpose
-- |
-- | Tracks the viewport (display surface) for the current frame:
-- |
-- | - **Tensor**: Resolution-independent rendering target
-- | - **Dimensions**: Width, height, device pixel ratio
-- | - **Orientation**: Portrait, landscape, square
-- | - **Shape**: Geometric clip region (rect, circle, bezier path)
-- | - **Safe Area**: Insets for notches, home indicators
-- | - **Change Detection**: Flags for resize, orientation, DPR changes
-- |
-- | ## Tensor Architecture
-- |
-- | The viewport is fundamentally a `ViewportTensor` — a tensor computation
-- | target with both pixel-space and latent-space shapes. This enables:
-- |
-- | - Resolution-independent rendering via latent space
-- | - Same computation for 20ft LED wall and smartwatch
-- | - Diffusion model integration with standard 8× downsample
-- |
-- | ## Non-Rectangular Displays
-- |
-- | Not all viewports are rectangles:
-- |
-- | - **Rectangle**: Standard monitors, most windows
-- | - **RoundedRectangle**: Modern phones, tablets, rounded monitors
-- | - **Circle**: Round smartwatches (Galaxy Watch, some Wear OS)
-- | - **RectangleWithCutout**: Phones with notches, punch-holes
-- | - **Polygon**: AR/VR viewports, unconventional displays

module Hydrogen.GPU.FrameState.Viewport
  ( -- * Viewport State
    ViewportState
  , ViewportOrientation(OrientationPortrait, OrientationLandscape, OrientationSquare)
  
  -- * Construction
  , mkViewportState
  , mkViewportStateWithShape
  , mkCircularViewport
  , mkRoundedRectViewport
  , mkPathViewport
  , mkEllipticalViewport
  
  -- * Basic Accessors
  , viewportWidth
  , viewportHeight
  , viewportDPI
  , viewportOrientation
  
  -- * Change Detection
  , viewportResized
  , viewportOrientationChanged
  , viewportDPRChanged
  , viewportShapeChanged
  , viewportAnyChange
  
  -- * Tensor Access
  , viewportTensor
  , viewportLatentWidth
  , viewportLatentHeight
  , viewportLatentSize
  
  -- * Shape Access
  , viewportClipShape
  , viewportSafeArea
  
  -- * Deltas
  , viewportWidthDelta
  , viewportHeightDelta
  
  -- * Update
  , updateViewportState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (/=)
  , (-)
  , (/)
  , (>)
  , (||)
  , ($)
  )

import Data.Int as Int

-- Viewport tensor abstraction (Schema.Spatial.Viewport)
import Hydrogen.Schema.Spatial.Viewport as Viewport
import Hydrogen.Schema.Spatial.Viewport
  ( ViewportTensor
  , viewportFromPixels
  , pixelWidth
  , pixelHeight
  , latentWidth
  , latentHeight
  , totalLatents
  )

-- Geometric shape for viewport clipping
import Hydrogen.Schema.Geometry.Shape as GeoShape
import Hydrogen.Schema.Geometry.Shape
  ( Shape
      ( ShapeRectangle
      , ShapeEllipse
      , ShapePath
      )
  , RectangleShape
  , rectangleShape
  , EllipseShape
  , circleShape
  , PathShape
  , pixelPoint2D
  , pixelOrigin
  )

-- Corner radius for rounded rectangles
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Geometry.Radius (cornersAll, none)

-- Device units for viewport dimensions
import Hydrogen.Schema.Dimension.Device 
  ( Pixel(Pixel)
  , DevicePixelRatio
  , unwrapPixel
  , unwrapDpr
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // viewport state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport/window state
-- |
-- | Tracks current viewport as a tensor computation target, with geometric
-- | shape for non-rectangular displays, and change detection for reactivity.
type ViewportState =
  { -- Tensor abstraction (full viewport-as-tensor)
    tensor :: Viewport.ViewportTensor
  
    -- Previous tensor (for delta detection)
  , prevTensor :: Viewport.ViewportTensor
  
    -- Geometric shape of the viewport (for non-rectangular displays)
  , clipShape :: GeoShape.Shape
  
    -- Safe area insets (for notches, cutouts, home indicators)
  , safeAreaTop :: Pixel
  , safeAreaRight :: Pixel
  , safeAreaBottom :: Pixel
  , safeAreaLeft :: Pixel
  
    -- Bounding dimensions (derived from tensor)
  , width :: Pixel
  , height :: Pixel
  , devicePixelRatio :: DevicePixelRatio
  , orientation :: ViewportOrientation
  
    -- Change flags (set by updateViewport)
  , resized :: Boolean
  , orientationChanged :: Boolean
  , dprChanged :: Boolean
  , shapeChanged :: Boolean
  }

-- | Viewport orientation
data ViewportOrientation
  = OrientationPortrait
  | OrientationLandscape
  | OrientationSquare

derive instance eqViewportOrientation :: Eq ViewportOrientation

instance showViewportOrientation :: Show ViewportOrientation where
  show OrientationPortrait = "(ViewportOrientation Portrait)"
  show OrientationLandscape = "(ViewportOrientation Landscape)"
  show OrientationSquare = "(ViewportOrientation Square)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create viewport state with rectangular clip shape
-- |
-- | Initializes viewport with given dimensions. Creates a ViewportTensor
-- | with the specified pixel dimensions and standard 8× latent downsample.
-- | Default clip shape is a rectangle matching the dimensions.
mkViewportState :: Pixel -> Pixel -> DevicePixelRatio -> ViewportState
mkViewportState width height devicePixelRatioVal =
  let
    widthNum = unwrapPixel width
    heightNum = unwrapPixel height
    
    tensor = Viewport.viewportFromPixels (Int.floor widthNum) (Int.floor heightNum)
    
    orientation = if widthNum > heightNum then OrientationLandscape
                  else if heightNum > widthNum then OrientationPortrait
                  else OrientationSquare
    
    defaultClipShape = GeoShape.ShapeRectangle $ rectangleShape
      pixelOrigin
      width
      height
      (cornersAll none)
  in
    { tensor
    , prevTensor: tensor
    , clipShape: defaultClipShape
    , safeAreaTop: Pixel 0.0
    , safeAreaRight: Pixel 0.0
    , safeAreaBottom: Pixel 0.0
    , safeAreaLeft: Pixel 0.0
    , width
    , height
    , devicePixelRatio: devicePixelRatioVal
    , orientation
    , resized: false
    , orientationChanged: false
    , dprChanged: false
    , shapeChanged: false
    }

-- | Create viewport state with a custom clip shape
-- |
-- | For non-rectangular displays (watches, notched phones, etc.)
mkViewportStateWithShape 
  :: Pixel
  -> Pixel
  -> DevicePixelRatio
  -> GeoShape.Shape
  -> { top :: Pixel, right :: Pixel, bottom :: Pixel, left :: Pixel }
  -> ViewportState
mkViewportStateWithShape width height devicePixelRatioVal clipShape safeArea =
  let
    widthNum = unwrapPixel width
    heightNum = unwrapPixel height
    
    tensor = Viewport.viewportFromPixels (Int.floor widthNum) (Int.floor heightNum)
    
    orientation = if widthNum > heightNum then OrientationLandscape
                  else if heightNum > widthNum then OrientationPortrait
                  else OrientationSquare
  in
    { tensor
    , prevTensor: tensor
    , clipShape
    , safeAreaTop: safeArea.top
    , safeAreaRight: safeArea.right
    , safeAreaBottom: safeArea.bottom
    , safeAreaLeft: safeArea.left
    , width
    , height
    , devicePixelRatio: devicePixelRatioVal
    , orientation
    , resized: false
    , orientationChanged: false
    , dprChanged: false
    , shapeChanged: false
    }

-- | Create a circular viewport (for round smartwatches)
-- |
-- | Creates a viewport with a circular clip shape centered in the bounding box.
-- | Common for: Galaxy Watch, some Wear OS devices, circular fitness trackers.
mkCircularViewport :: Pixel -> DevicePixelRatio -> ViewportState
mkCircularViewport diameter devicePixelRatioVal =
  let
    diameterNum = unwrapPixel diameter
    radiusNum = diameterNum / 2.0
    radius = Pixel radiusNum
    center = pixelPoint2D radius radius
    
    clipShape = GeoShape.ShapeEllipse $ circleShape center radius
    
    noInsets = { top: Pixel 0.0, right: Pixel 0.0, bottom: Pixel 0.0, left: Pixel 0.0 }
  in
    mkViewportStateWithShape diameter diameter devicePixelRatioVal clipShape noInsets

-- | Create a rounded rectangle viewport (for modern phones/tablets)
-- |
-- | Creates a viewport with rounded corners matching modern device displays.
mkRoundedRectViewport 
  :: Pixel
  -> Pixel
  -> DevicePixelRatio
  -> Radius.Radius
  -> { top :: Pixel, right :: Pixel, bottom :: Pixel, left :: Pixel }
  -> ViewportState
mkRoundedRectViewport width height devicePixelRatioVal cornerRadius safeArea =
  let
    widthNum = unwrapPixel width
    heightNum = unwrapPixel height
    centerX = widthNum / 2.0
    centerY = heightNum / 2.0
    center = pixelPoint2D (Pixel centerX) (Pixel centerY)
    
    clipShape = GeoShape.ShapeRectangle $ rectangleShape
      center
      width
      height
      (cornersAll cornerRadius)
  in
    mkViewportStateWithShape width height devicePixelRatioVal clipShape safeArea

-- | Create a viewport with a custom bezier path shape
-- |
-- | For unconventional displays: AR/VR viewports, unusual aspect ratios,
-- | custom-shaped kiosk displays, etc.
mkPathViewport
  :: Pixel
  -> Pixel
  -> DevicePixelRatio
  -> PathShape
  -> { top :: Pixel, right :: Pixel, bottom :: Pixel, left :: Pixel }
  -> ViewportState
mkPathViewport width height devicePixelRatioVal path safeArea =
  let
    clipShape = ShapePath path
  in
    mkViewportStateWithShape width height devicePixelRatioVal clipShape safeArea

-- | Create a viewport with an elliptical (oval) shape
-- |
-- | For non-circular watches or oval displays.
mkEllipticalViewport
  :: Pixel
  -> Pixel
  -> DevicePixelRatio
  -> ViewportState
mkEllipticalViewport width height devicePixelRatioVal =
  let
    widthNum = unwrapPixel width
    heightNum = unwrapPixel height
    center = pixelPoint2D (Pixel (widthNum / 2.0)) (Pixel (heightNum / 2.0))
    radiusX = Pixel (widthNum / 2.0)
    radiusY = Pixel (heightNum / 2.0)
    
    ellipse :: EllipseShape
    ellipse = { center, radiusX, radiusY }
    
    clipShape = ShapeEllipse ellipse
    noInsets = { top: Pixel 0.0, right: Pixel 0.0, bottom: Pixel 0.0, left: Pixel 0.0 }
  in
    mkViewportStateWithShape width height devicePixelRatioVal clipShape noInsets

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // basic accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get viewport width
viewportWidth :: ViewportState -> Pixel
viewportWidth state = state.width

-- | Get viewport height
viewportHeight :: ViewportState -> Pixel
viewportHeight state = state.height

-- | Get device pixel ratio
viewportDPI :: ViewportState -> DevicePixelRatio
viewportDPI state = state.devicePixelRatio

-- | Get viewport orientation
viewportOrientation :: ViewportState -> ViewportOrientation
viewportOrientation state = state.orientation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // change detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if viewport was resized this frame
viewportResized :: ViewportState -> Boolean
viewportResized state = state.resized

-- | Check if viewport orientation changed this frame
viewportOrientationChanged :: ViewportState -> Boolean
viewportOrientationChanged state = state.orientationChanged

-- | Check if device pixel ratio changed this frame
viewportDPRChanged :: ViewportState -> Boolean
viewportDPRChanged state = state.dprChanged

-- | Check if viewport clip shape changed this frame
viewportShapeChanged :: ViewportState -> Boolean
viewportShapeChanged state = state.shapeChanged

-- | Check if any viewport property changed this frame
viewportAnyChange :: ViewportState -> Boolean
viewportAnyChange state = 
  state.resized || state.orientationChanged || state.dprChanged || state.shapeChanged

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // tensor access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the ViewportTensor for tensor/GPU computation
viewportTensor :: ViewportState -> Viewport.ViewportTensor
viewportTensor state = state.tensor

-- | Get latent width (for tensor/diffusion rendering)
-- |
-- | Returns width / 8, the standard downsample factor for Stable Diffusion.
viewportLatentWidth :: ViewportState -> Int
viewportLatentWidth state = Viewport.latentWidth state.tensor

-- | Get latent height (for tensor/diffusion rendering)
viewportLatentHeight :: ViewportState -> Int
viewportLatentHeight state = Viewport.latentHeight state.tensor

-- | Get total latent count (for GPU memory budgeting)
-- |
-- | Returns latentWidth × latentHeight × 4 (4 latent channels).
viewportLatentSize :: ViewportState -> Int
viewportLatentSize state = Viewport.totalLatents state.tensor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // shape access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the geometric clip shape of the viewport
viewportClipShape :: ViewportState -> GeoShape.Shape
viewportClipShape state = state.clipShape

-- | Get safe area insets as a record
viewportSafeArea :: ViewportState -> { top :: Pixel, right :: Pixel, bottom :: Pixel, left :: Pixel }
viewportSafeArea state = 
  { top: state.safeAreaTop
  , right: state.safeAreaRight
  , bottom: state.safeAreaBottom
  , left: state.safeAreaLeft
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // deltas
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get viewport width delta (current - previous)
viewportWidthDelta :: ViewportState -> Int
viewportWidthDelta state = 
  Viewport.pixelWidth state.tensor - Viewport.pixelWidth state.prevTensor

-- | Get viewport height delta (current - previous)
viewportHeightDelta :: ViewportState -> Int
viewportHeightDelta state = 
  Viewport.pixelHeight state.tensor - Viewport.pixelHeight state.prevTensor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // update
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update viewport state (dimensions only, keeps existing clip shape)
-- |
-- | Compares new dimensions against previous and sets change flags.
-- | Previous tensor is updated to current before applying new values.
-- | Clip shape is updated to match new dimensions.
updateViewportState :: Pixel -> Pixel -> DevicePixelRatio -> ViewportState -> ViewportState
updateViewportState width height devicePixelRatioVal prev =
  let
    widthNum = unwrapPixel width
    heightNum = unwrapPixel height
    prevWidthNum = unwrapPixel prev.width
    prevHeightNum = unwrapPixel prev.height
    
    newOrientation = if widthNum > heightNum then OrientationLandscape
                     else if heightNum > widthNum then OrientationPortrait
                     else OrientationSquare

    sizeChanged = widthNum /= prevWidthNum || heightNum /= prevHeightNum
    orientationDiff = newOrientation /= prev.orientation
    dprDiff = unwrapDpr devicePixelRatioVal /= unwrapDpr prev.devicePixelRatio

    newTensor = Viewport.viewportFromPixels (Int.floor widthNum) (Int.floor heightNum)
    
    newClipShape = GeoShape.ShapeRectangle $ rectangleShape
      pixelOrigin
      width
      height
      (cornersAll none)
  in
    { tensor: newTensor
    , prevTensor: prev.tensor
    , clipShape: newClipShape
    , safeAreaTop: prev.safeAreaTop
    , safeAreaRight: prev.safeAreaRight
    , safeAreaBottom: prev.safeAreaBottom
    , safeAreaLeft: prev.safeAreaLeft
    , width
    , height
    , devicePixelRatio: devicePixelRatioVal
    , orientation: newOrientation
    , resized: sizeChanged
    , orientationChanged: orientationDiff
    , dprChanged: dprDiff
    , shapeChanged: sizeChanged
    }
