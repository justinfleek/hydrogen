-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // element // slider // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SliderGeometry — Spatial atoms for slider/range control layout.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - Pixel (Dimension.Device) — Verified pixel unit
-- | - SpacingValue (Geometry.Spacing) — Bounded spacing [0-1000]
-- | - CornerRadii (Geometry.CornerRadii) — 4-corner radii
-- |
-- | ## Slider Geometry Model
-- |
-- | A slider consists of:
-- | - Track: The rail that the thumb slides along
-- | - Thumb: The handle that moves to indicate current value
-- | - Progress: The filled portion of the track (optional)
-- |
-- | ## Orientation
-- |
-- | Sliders can be horizontal (default) or vertical:
-- | - Horizontal: thumb moves left-right, length is width
-- | - Vertical: thumb moves top-bottom, length is height
-- |
-- | ## Size Presets
-- |
-- | Standard sizes for common use cases:
-- | - Sm: 120×4px track, 12px thumb (inline controls)
-- | - Md: 200×6px track, 16px thumb (default)
-- | - Lg: 280×8px track, 24px thumb (primary controls)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Dimension.Device (Pixel)
-- | - Hydrogen.Schema.Geometry.Spacing (SpacingValue)
-- | - Hydrogen.Schema.Geometry.CornerRadii (CornerRadii)

module Hydrogen.Schema.Element.Slider.Geometry
  ( -- * Slider Orientation
    SliderOrientation
      ( Horizontal
      , Vertical
      )
  , isHorizontal
  , isVertical
  
  -- * Slider Size Presets
  , SliderSize
      ( SizeSm
      , SizeMd
      , SizeLg
      , SizeCustom
      )
  , sizeToTrackLength
  , sizeToTrackThickness
  , sizeToThumbDiameter
  
  -- * Slider Geometry Record
  , SliderGeometry
  , defaultGeometry
  , compactGeometry
  , largeGeometry
  , verticalGeometry
  , colorPickerGeometry
  
  -- * Geometry Accessors
  , getTrackLength
  , getTrackThickness
  , getThumbDiameter
  , getThumbOverhang
  , getTrackRadius
  , getThumbRadius
  , getOrientation
  , getPadding
  
  -- * Geometry Modifiers
  , setTrackLength
  , setTrackThickness
  , setThumbDiameter
  , setOrientation
  , setPillTrack
  , setSquareTrack
  , setPillThumb
  , setSquareThumb
  , setPadding
  
  -- * Computed Properties
  , getEffectiveWidth
  , getEffectiveHeight
  , getThumbTravelDistance
  , thumbPositionAtProgress
  
  -- * Re-exports
  , module Hydrogen.Schema.Dimension.Device.Types
  , module Hydrogen.Schema.Geometry.Spacing
  , module Hydrogen.Schema.Geometry.CornerRadii
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (/)
  , (-)
  , (*)
  , (+)
  , (<>)
  , (==)
  , max
  )

import Prim (Boolean, Number)

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Dimension.Device.Types
  ( Pixel(Pixel)
  )

import Hydrogen.Schema.Geometry.Spacing
  ( SpacingValue(SpacingValue)
  , spacingValue
  , spacingZero
  , spacingSm
  )

import Hydrogen.Schema.Geometry.CornerRadii
  ( CornerRadii
  , uniform
  , none
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // slider orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider orientation — horizontal or vertical axis.
-- |
-- | ## Layout Implications
-- |
-- | - Horizontal: Track extends along X axis, thumb moves left-right
-- | - Vertical: Track extends along Y axis, thumb moves top-bottom
-- |
-- | The geometry record uses "length" and "thickness" to be orientation-agnostic:
-- | - Horizontal: length = width, thickness = height
-- | - Vertical: length = height, thickness = width
data SliderOrientation
  = Horizontal                         -- ^ Thumb moves left-right
  | Vertical                           -- ^ Thumb moves top-bottom

derive instance eqSliderOrientation :: Eq SliderOrientation
derive instance ordSliderOrientation :: Ord SliderOrientation

instance showSliderOrientation :: Show SliderOrientation where
  show Horizontal = "Horizontal"
  show Vertical = "Vertical"

-- | Check if orientation is horizontal.
isHorizontal :: SliderOrientation -> Boolean
isHorizontal Horizontal = true
isHorizontal Vertical = false

-- | Check if orientation is vertical.
isVertical :: SliderOrientation -> Boolean
isVertical Horizontal = false
isVertical Vertical = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // slider sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider size presets — semantic sizes for slider controls.
-- |
-- | ## Size Specifications
-- |
-- | | Size | Track L×T  | Thumb Ø | Use Case           |
-- | |------|------------|---------|---------------------|
-- | | Sm   | 120×4px    | 12px    | Inline/compact UIs  |
-- | | Md   | 200×6px    | 16px    | Default             |
-- | | Lg   | 280×8px    | 24px    | Primary controls    |
-- |
-- | Custom sizes allow full control over all dimensions.
data SliderSize
  = SizeSm                                     -- ^ 120×4px track, 12px thumb
  | SizeMd                                     -- ^ 200×6px track, 16px thumb
  | SizeLg                                     -- ^ 280×8px track, 24px thumb
  | SizeCustom Pixel Pixel Pixel               -- ^ Custom (length, thickness, thumb)

derive instance eqSliderSize :: Eq SliderSize
derive instance ordSliderSize :: Ord SliderSize

instance showSliderSize :: Show SliderSize where
  show SizeSm = "SizeSm"
  show SizeMd = "SizeMd"
  show SizeLg = "SizeLg"
  show (SizeCustom l t th) = "(SizeCustom " <> show l <> " " <> show t <> " " <> show th <> ")"

-- | Get track length for size preset.
sizeToTrackLength :: SliderSize -> Pixel
sizeToTrackLength = case _ of
  SizeSm -> Pixel 120.0
  SizeMd -> Pixel 200.0
  SizeLg -> Pixel 280.0
  SizeCustom l _ _ -> l

-- | Get track thickness for size preset.
sizeToTrackThickness :: SliderSize -> Pixel
sizeToTrackThickness = case _ of
  SizeSm -> Pixel 4.0
  SizeMd -> Pixel 6.0
  SizeLg -> Pixel 8.0
  SizeCustom _ t _ -> t

-- | Get thumb diameter for size preset.
sizeToThumbDiameter :: SliderSize -> Pixel
sizeToThumbDiameter = case _ of
  SizeSm -> Pixel 12.0
  SizeMd -> Pixel 16.0
  SizeLg -> Pixel 24.0
  SizeCustom _ _ th -> th

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // slider geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete slider geometry — all spatial properties.
-- |
-- | ## Verified Bounds
-- |
-- | - Track dimensions: via Pixel (typed, not raw Number)
-- | - Thumb diameter: via Pixel (typically > track thickness)
-- | - Corner radii: via CornerRadii (bounded 0-1000)
-- | - Padding: via SpacingValue (bounded 0-1000)
-- |
-- | ## Thumb Overhang
-- |
-- | When thumb diameter > track thickness, the thumb "overhangs" the track.
-- | This affects the element's effective bounding box and hit testing.
-- | Overhang = max(0, (thumbDiameter - trackThickness) / 2)
-- |
-- | ## Thumb Travel
-- |
-- | The thumb center travels from:
-- | - Start: thumbDiameter / 2 (so thumb edge aligns with track start)
-- | - End: trackLength - thumbDiameter / 2 (so thumb edge aligns with track end)
-- | - Travel distance: trackLength - thumbDiameter
type SliderGeometry =
  { -- Track dimensions (orientation-agnostic)
    trackLength :: Pixel               -- ^ Track length (width if horizontal)
  , trackThickness :: Pixel            -- ^ Track thickness (height if horizontal)
  , trackRadius :: CornerRadii         -- ^ Track corner radii
    -- Thumb dimensions
  , thumbDiameter :: Pixel             -- ^ Thumb diameter
  , thumbRadius :: CornerRadii         -- ^ Thumb corner radii (circle = uniform d/2)
    -- Layout
  , orientation :: SliderOrientation   -- ^ Horizontal or vertical
  , padding :: SpacingValue            -- ^ Padding around slider
  }

-- | Default slider geometry — medium size, horizontal, pill shapes.
-- |
-- | 200×6px track, 16px thumb, pill corners on both track and thumb.
defaultGeometry :: SliderGeometry
defaultGeometry =
  { trackLength: Pixel 200.0
  , trackThickness: Pixel 6.0
  , trackRadius: uniform 3.0           -- Half of thickness = pill
  , thumbDiameter: Pixel 16.0
  , thumbRadius: uniform 8.0           -- Half of diameter = circle
  , orientation: Horizontal
  , padding: spacingZero
  }

-- | Compact slider geometry — small size for inline controls.
-- |
-- | 120×4px track, 12px thumb.
compactGeometry :: SliderGeometry
compactGeometry =
  { trackLength: Pixel 120.0
  , trackThickness: Pixel 4.0
  , trackRadius: uniform 2.0           -- Half of thickness = pill
  , thumbDiameter: Pixel 12.0
  , thumbRadius: uniform 6.0           -- Half of diameter = circle
  , orientation: Horizontal
  , padding: spacingZero
  }

-- | Large slider geometry — for primary controls and touch.
-- |
-- | 280×8px track, 24px thumb.
largeGeometry :: SliderGeometry
largeGeometry =
  { trackLength: Pixel 280.0
  , trackThickness: Pixel 8.0
  , trackRadius: uniform 4.0           -- Half of thickness = pill
  , thumbDiameter: Pixel 24.0
  , thumbRadius: uniform 12.0          -- Half of diameter = circle
  , orientation: Horizontal
  , padding: spacingSm
  }

-- | Vertical slider geometry — for volume controls, etc.
-- |
-- | Same dimensions as default but vertical orientation.
verticalGeometry :: SliderGeometry
verticalGeometry = defaultGeometry
  { orientation = Vertical
  }

-- | Color picker slider geometry — wide track for gradient visibility.
-- |
-- | 240×12px track, 18px thumb — shows gradient clearly.
colorPickerGeometry :: SliderGeometry
colorPickerGeometry =
  { trackLength: Pixel 240.0
  , trackThickness: Pixel 12.0
  , trackRadius: uniform 6.0           -- Half of thickness = pill
  , thumbDiameter: Pixel 18.0
  , thumbRadius: uniform 9.0           -- Half of diameter = circle
  , orientation: Horizontal
  , padding: spacingZero
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get track length.
getTrackLength :: SliderGeometry -> Pixel
getTrackLength g = g.trackLength

-- | Get track thickness.
getTrackThickness :: SliderGeometry -> Pixel
getTrackThickness g = g.trackThickness

-- | Get thumb diameter.
getThumbDiameter :: SliderGeometry -> Pixel
getThumbDiameter g = g.thumbDiameter

-- | Get thumb overhang — how much thumb extends beyond track bounds.
-- |
-- | Overhang = max(0, (thumbDiameter - trackThickness) / 2)
-- | This is the extra space needed in the cross-axis direction.
getThumbOverhang :: SliderGeometry -> Pixel
getThumbOverhang g = case g.thumbDiameter of
  Pixel td -> case g.trackThickness of
    Pixel tt -> Pixel (max 0.0 ((td - tt) / 2.0))

-- | Get track corner radii.
getTrackRadius :: SliderGeometry -> CornerRadii
getTrackRadius g = g.trackRadius

-- | Get thumb corner radii.
getThumbRadius :: SliderGeometry -> CornerRadii
getThumbRadius g = g.thumbRadius

-- | Get orientation.
getOrientation :: SliderGeometry -> SliderOrientation
getOrientation g = g.orientation

-- | Get outer padding.
getPadding :: SliderGeometry -> SpacingValue
getPadding g = g.padding

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track length (bounded 20-1000px).
setTrackLength :: Number -> SliderGeometry -> SliderGeometry
setTrackLength l g = g { trackLength = Pixel (Bounded.clampNumber 20.0 1000.0 l) }

-- | Set track thickness (bounded 2-100px).
setTrackThickness :: Number -> SliderGeometry -> SliderGeometry
setTrackThickness t g = g { trackThickness = Pixel (Bounded.clampNumber 2.0 100.0 t) }

-- | Set thumb diameter (bounded 8-100px).
setThumbDiameter :: Number -> SliderGeometry -> SliderGeometry
setThumbDiameter d g = g { thumbDiameter = Pixel (Bounded.clampNumber 8.0 100.0 d) }

-- | Set orientation.
setOrientation :: SliderOrientation -> SliderGeometry -> SliderGeometry
setOrientation o g = g { orientation = o }

-- | Set track to pill shape (radius = thickness/2).
setPillTrack :: SliderGeometry -> SliderGeometry
setPillTrack g = case g.trackThickness of
  Pixel t -> g { trackRadius = uniform (t / 2.0) }

-- | Set track to square shape (no radius).
setSquareTrack :: SliderGeometry -> SliderGeometry
setSquareTrack g = g { trackRadius = none }

-- | Set thumb to circle shape (radius = diameter/2).
setPillThumb :: SliderGeometry -> SliderGeometry
setPillThumb g = case g.thumbDiameter of
  Pixel d -> g { thumbRadius = uniform (d / 2.0) }

-- | Set thumb to square shape (no radius).
setSquareThumb :: SliderGeometry -> SliderGeometry
setSquareThumb g = g { thumbRadius = none }

-- | Set outer padding.
setPadding :: Number -> SliderGeometry -> SliderGeometry
setPadding p g = g { padding = spacingValue p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get effective width including thumb overhang.
-- |
-- | - Horizontal: trackLength (thumb overhang is in height)
-- | - Vertical: max(trackThickness, thumbDiameter)
getEffectiveWidth :: SliderGeometry -> Pixel
getEffectiveWidth g = case g.orientation of
  Horizontal -> g.trackLength
  Vertical -> case g.trackThickness of
    Pixel tt -> case g.thumbDiameter of
      Pixel td -> Pixel (max tt td)

-- | Get effective height including thumb overhang.
-- |
-- | - Horizontal: max(trackThickness, thumbDiameter)
-- | - Vertical: trackLength
getEffectiveHeight :: SliderGeometry -> Pixel
getEffectiveHeight g = case g.orientation of
  Horizontal -> case g.trackThickness of
    Pixel tt -> case g.thumbDiameter of
      Pixel td -> Pixel (max tt td)
  Vertical -> g.trackLength

-- | Get thumb travel distance (how far thumb center can move).
-- |
-- | Travel = trackLength - thumbDiameter
-- | (Thumb edges touch track edges at 0% and 100%)
getThumbTravelDistance :: SliderGeometry -> Pixel
getThumbTravelDistance g = case g.trackLength of
  Pixel l -> case g.thumbDiameter of
    Pixel d -> Pixel (max 0.0 (l - d))

-- | Calculate thumb center position at given progress (0.0-1.0).
-- |
-- | Returns the offset from the track start to thumb center.
-- | At progress 0.0: thumbDiameter/2 (thumb edge at track start)
-- | At progress 1.0: trackLength - thumbDiameter/2 (thumb edge at track end)
thumbPositionAtProgress :: Number -> SliderGeometry -> Pixel
thumbPositionAtProgress progress g = 
  let
    clampedProgress :: Number
    clampedProgress = Bounded.clampNumber 0.0 1.0 progress
    
    thumbRadius :: Number
    thumbRadius = case g.thumbDiameter of
      Pixel d -> d / 2.0
    
    travel :: Number
    travel = case getThumbTravelDistance g of
      Pixel t -> t
  in
    Pixel (thumbRadius + (clampedProgress * travel))
