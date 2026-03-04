-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // element // toggle // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ToggleGeometry — Spatial atoms for toggle/switch layout.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - Pixel (Dimension.Device) — Verified pixel unit
-- | - SpacingValue (Geometry.Spacing) — Bounded spacing [0-1000]
-- | - CornerRadii (Geometry.CornerRadii) — 4-corner radii
-- |
-- | ## Toggle Geometry Model
-- |
-- | A toggle/switch consists of:
-- | - Track: The background rail that the thumb slides along
-- | - Thumb: The circular handle that moves to indicate on/off
-- |
-- | ## Size Presets
-- |
-- | Standard sizes follow Material/iOS conventions:
-- | - Sm: 36×20px track, 16px thumb (compact UIs)
-- | - Md: 44×24px track, 20px thumb (default)
-- | - Lg: 52×28px track, 24px thumb (touch-friendly)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Dimension.Device (Pixel)
-- | - Hydrogen.Schema.Geometry.Spacing (SpacingValue)
-- | - Hydrogen.Schema.Geometry.CornerRadii (CornerRadii)

module Hydrogen.Schema.Element.Toggle.Geometry
  ( -- * Toggle Size Presets
    ToggleSize
      ( SizeSm
      , SizeMd
      , SizeLg
      , SizeCustom
      )
  , sizeToTrackWidth
  , sizeToTrackHeight
  , sizeToThumbDiameter
  
  -- * Toggle Geometry Record
  , ToggleGeometry
  , defaultGeometry
  , compactGeometry
  , largeGeometry
  , squareGeometry
  
  -- * Geometry Accessors
  , getTrackWidth
  , getTrackHeight
  , getThumbDiameter
  , getThumbInset
  , getTrackRadius
  , getPadding
  
  -- * Geometry Modifiers
  , setTrackWidth
  , setTrackHeight
  , setThumbDiameter
  , setThumbInset
  , setSquareCorners
  , setPillCorners
  , setPadding
  
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
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Dimension.Device.Types
  ( Pixel(Pixel)
  )

import Hydrogen.Schema.Geometry.Spacing
  ( SpacingValue(SpacingValue)
  , spacingValue
  , spacingZero
  , spacingXs
  , spacingSm
  )

import Hydrogen.Schema.Geometry.CornerRadii
  ( CornerRadii
  , uniform
  , none
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // toggle sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toggle size presets — semantic sizes for switch controls.
-- |
-- | ## Size Specifications
-- |
-- | | Size | Track W×H  | Thumb Ø | Use Case           |
-- | |------|------------|---------|---------------------|
-- | | Sm   | 36×20px    | 16px    | Compact/dense UIs   |
-- | | Md   | 44×24px    | 20px    | Default (iOS-like)  |
-- | | Lg   | 52×28px    | 24px    | Touch-friendly      |
-- |
-- | Custom sizes must maintain thumb ≤ track height for visual balance.
data ToggleSize
  = SizeSm                                     -- ^ 36×20px track, 16px thumb
  | SizeMd                                     -- ^ 44×24px track, 20px thumb
  | SizeLg                                     -- ^ 52×28px track, 24px thumb
  | SizeCustom Pixel Pixel Pixel               -- ^ Custom (width, height, thumb)

derive instance eqToggleSize :: Eq ToggleSize
derive instance ordToggleSize :: Ord ToggleSize

instance showToggleSize :: Show ToggleSize where
  show SizeSm = "SizeSm"
  show SizeMd = "SizeMd"
  show SizeLg = "SizeLg"
  show (SizeCustom w h t) = "(SizeCustom " <> show w <> " " <> show h <> " " <> show t <> ")"

-- | Get track width for size preset.
sizeToTrackWidth :: ToggleSize -> Pixel
sizeToTrackWidth = case _ of
  SizeSm -> Pixel 36.0
  SizeMd -> Pixel 44.0
  SizeLg -> Pixel 52.0
  SizeCustom w _ _ -> w

-- | Get track height for size preset.
sizeToTrackHeight :: ToggleSize -> Pixel
sizeToTrackHeight = case _ of
  SizeSm -> Pixel 20.0
  SizeMd -> Pixel 24.0
  SizeLg -> Pixel 28.0
  SizeCustom _ h _ -> h

-- | Get thumb diameter for size preset.
sizeToThumbDiameter :: ToggleSize -> Pixel
sizeToThumbDiameter = case _ of
  SizeSm -> Pixel 16.0
  SizeMd -> Pixel 20.0
  SizeLg -> Pixel 24.0
  SizeCustom _ _ t -> t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // toggle geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete toggle geometry — all spatial properties.
-- |
-- | ## Verified Bounds
-- |
-- | - Track dimensions: via Pixel (unbounded but typed)
-- | - Thumb diameter: via Pixel (should be ≤ track height)
-- | - Thumb inset: via Pixel (space between thumb edge and track edge)
-- | - Corner radii: via CornerRadii (bounded 0-1000)
-- | - Padding: via SpacingValue (bounded 0-1000)
-- |
-- | ## Thumb Position
-- |
-- | The thumb travels from left (off) to right (on):
-- | - Off position: inset from left edge
-- | - On position: inset from right edge
-- | - Travel distance: track width - thumb diameter - (2 × inset)
type ToggleGeometry =
  { -- Track dimensions
    trackWidth :: Pixel                -- ^ Track width
  , trackHeight :: Pixel               -- ^ Track height
  , trackRadius :: CornerRadii         -- ^ Track corner radii
    -- Thumb dimensions
  , thumbDiameter :: Pixel             -- ^ Thumb diameter
  , thumbInset :: Pixel                -- ^ Space between thumb and track edge
    -- Outer spacing
  , padding :: SpacingValue            -- ^ Padding around toggle
  }

-- | Default toggle geometry — medium size, pill shape.
-- |
-- | 44×24px track, 20px thumb, 2px inset, full pill corners.
defaultGeometry :: ToggleGeometry
defaultGeometry =
  { trackWidth: Pixel 44.0
  , trackHeight: Pixel 24.0
  , trackRadius: uniform 12.0    -- Half of height = pill
  , thumbDiameter: Pixel 20.0
  , thumbInset: Pixel 2.0
  , padding: spacingZero
  }

-- | Compact toggle geometry — small size.
-- |
-- | 36×20px track, 16px thumb, for dense UIs.
compactGeometry :: ToggleGeometry
compactGeometry =
  { trackWidth: Pixel 36.0
  , trackHeight: Pixel 20.0
  , trackRadius: uniform 10.0    -- Half of height = pill
  , thumbDiameter: Pixel 16.0
  , thumbInset: Pixel 2.0
  , padding: spacingZero
  }

-- | Large toggle geometry — touch-friendly.
-- |
-- | 52×28px track, 24px thumb, for mobile/accessibility.
largeGeometry :: ToggleGeometry
largeGeometry =
  { trackWidth: Pixel 52.0
  , trackHeight: Pixel 28.0
  , trackRadius: uniform 14.0    -- Half of height = pill
  , thumbDiameter: Pixel 24.0
  , thumbInset: Pixel 2.0
  , padding: spacingSm
  }

-- | Square toggle geometry — rounded corners but not pill.
-- |
-- | Same dimensions as default but with 4px radius.
squareGeometry :: ToggleGeometry
squareGeometry = defaultGeometry
  { trackRadius = uniform 4.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get track width.
getTrackWidth :: ToggleGeometry -> Pixel
getTrackWidth g = g.trackWidth

-- | Get track height.
getTrackHeight :: ToggleGeometry -> Pixel
getTrackHeight g = g.trackHeight

-- | Get thumb diameter.
getThumbDiameter :: ToggleGeometry -> Pixel
getThumbDiameter g = g.thumbDiameter

-- | Get thumb inset (gap between thumb and track edge).
getThumbInset :: ToggleGeometry -> Pixel
getThumbInset g = g.thumbInset

-- | Get track corner radii.
getTrackRadius :: ToggleGeometry -> CornerRadii
getTrackRadius g = g.trackRadius

-- | Get outer padding.
getPadding :: ToggleGeometry -> SpacingValue
getPadding g = g.padding

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track width (bounded 20-200px).
setTrackWidth :: Number -> ToggleGeometry -> ToggleGeometry
setTrackWidth w g = g { trackWidth = Pixel (Bounded.clampNumber 20.0 200.0 w) }

-- | Set track height (bounded 12-100px).
setTrackHeight :: Number -> ToggleGeometry -> ToggleGeometry
setTrackHeight h g = g { trackHeight = Pixel (Bounded.clampNumber 12.0 100.0 h) }

-- | Set thumb diameter (bounded 8-96px).
setThumbDiameter :: Number -> ToggleGeometry -> ToggleGeometry
setThumbDiameter d g = g { thumbDiameter = Pixel (Bounded.clampNumber 8.0 96.0 d) }

-- | Set thumb inset (bounded 0-16px).
setThumbInset :: Number -> ToggleGeometry -> ToggleGeometry
setThumbInset i g = g { thumbInset = Pixel (Bounded.clampNumber 0.0 16.0 i) }

-- | Set track corners to square (0 radius).
setSquareCorners :: ToggleGeometry -> ToggleGeometry
setSquareCorners g = g { trackRadius = none }

-- | Set track corners to pill shape (radius = height/2).
-- |
-- | Recalculates based on current track height.
setPillCorners :: ToggleGeometry -> ToggleGeometry
setPillCorners g = case g.trackHeight of
  Pixel h -> g { trackRadius = uniform (h / 2.0) }

-- | Set outer padding.
setPadding :: Number -> ToggleGeometry -> ToggleGeometry
setPadding p g = g { padding = spacingValue p }
