-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // element // playhead // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PlayheadGeometry — Spatial atoms for playhead layout and shape.
-- |
-- | ## Atoms Included
-- |
-- | - Button size (preset or explicit pixels)
-- | - Track dimensions (height, corner radius)
-- | - Thumb dimensions (size, shape)
-- | - Padding/spacing
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Spacing (SpacingValue, Padding)
-- | - Hydrogen.Schema.Geometry.CornerRadii (CornerRadii)
-- | - Hydrogen.Schema.Dimension.Size2D (Size2D)
-- |
-- | ## Design Philosophy
-- |
-- | Geometry describes WHERE the playhead lives, not HOW it looks.
-- | All dimensions use bounded types — no raw Numbers.

module Hydrogen.Schema.Element.Playhead.Geometry
  ( -- * Playhead Size Presets
    PlayheadSize
      ( SizeXs
      , SizeSm
      , SizeMd
      , SizeLg
      , SizeXl
      , SizeCustom
      )
  , sizeToPixels
  , sizeFromPixels
  
  -- * Playhead Geometry Record
  , PlayheadGeometry
  , defaultGeometry
  , compactGeometry
  , largeGeometry
  , scrubberGeometry
  
  -- * Geometry Accessors
  , getButtonSize
  , getTrackHeight
  , getTrackRadius
  , getThumbSize
  , getPadding
  
  -- * Geometry Modifiers
  , setButtonSize
  , setTrackHeight
  , setTrackRadius
  , setThumbSize
  , setPadding
  
  -- * Track Shape
  , TrackShape(TrackRounded, TrackSquare, TrackPill)
  , trackShapeToRadius
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
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Geometry.Spacing
  ( SpacingValue
  , spacingValue
  , spacingZero
  , spacingXs
  , spacingSm
  , spacingMd
  , unwrapSpacing
  ) as Spacing

import Hydrogen.Schema.Geometry.CornerRadii
  ( CornerRadii
  , uniform
  ) as Corner

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // playhead sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Playhead size presets — semantic sizes for media controls.
-- |
-- | Presets map to pixel values suitable for touch targets:
-- | - Xs: 24px (minimal, icons only)
-- | - Sm: 32px (compact toolbars)
-- | - Md: 40px (default, good touch target)
-- | - Lg: 48px (emphasized controls)
-- | - Xl: 64px (hero controls, TV UIs)
-- | - Custom: explicit pixel value (bounded 16-256)
data PlayheadSize
  = SizeXs          -- ^ 24px - minimal
  | SizeSm          -- ^ 32px - compact
  | SizeMd          -- ^ 40px - default
  | SizeLg          -- ^ 48px - large
  | SizeXl          -- ^ 64px - extra large
  | SizeCustom Number  -- ^ Custom size (bounded 16-256)

derive instance eqPlayheadSize :: Eq PlayheadSize
derive instance ordPlayheadSize :: Ord PlayheadSize

instance showPlayheadSize :: Show PlayheadSize where
  show SizeXs = "SizeXs"
  show SizeSm = "SizeSm"
  show SizeMd = "SizeMd"
  show SizeLg = "SizeLg"
  show SizeXl = "SizeXl"
  show (SizeCustom n) = "(SizeCustom " <> show n <> ")"

-- | Convert size preset to pixel value.
-- |
-- | Custom sizes are bounded to 16-256 pixels.
sizeToPixels :: PlayheadSize -> Number
sizeToPixels = case _ of
  SizeXs -> 24.0
  SizeSm -> 32.0
  SizeMd -> 40.0
  SizeLg -> 48.0
  SizeXl -> 64.0
  SizeCustom n -> Bounded.clampNumber 16.0 256.0 n

-- | Create a custom size from pixels.
-- |
-- | Snaps to nearest preset if within 2px, otherwise uses custom.
-- | Bounded to 16-256 pixels.
sizeFromPixels :: Number -> PlayheadSize
sizeFromPixels n
  | n <= 16.0 = SizeXs
  | n <= 26.0 = SizeXs  -- within 2px of 24
  | n <= 34.0 = SizeSm  -- within 2px of 32
  | n <= 42.0 = SizeMd  -- within 2px of 40
  | n <= 50.0 = SizeLg  -- within 2px of 48
  | n <= 66.0 = SizeXl  -- within 2px of 64
  | otherwise = SizeCustom (Bounded.clampNumber 16.0 256.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // track shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Track shape — how the progress track is rendered.
-- |
-- | - Rounded: Corner radius is half the track height (capsule ends)
-- | - Square: No corner radius
-- | - Pill: Full pill shape (radius = height)
data TrackShape
  = TrackRounded   -- ^ Rounded corners (default)
  | TrackSquare    -- ^ Square corners
  | TrackPill      -- ^ Full pill/capsule shape

derive instance eqTrackShape :: Eq TrackShape

instance showTrackShape :: Show TrackShape where
  show TrackRounded = "TrackRounded"
  show TrackSquare = "TrackSquare"
  show TrackPill = "TrackPill"

-- | Convert track shape to corner radius based on track height.
-- |
-- | Returns uniform CornerRadii.
trackShapeToRadius :: TrackShape -> Number -> Corner.CornerRadii
trackShapeToRadius shape trackHeight = case shape of
  TrackRounded -> Corner.uniform (trackHeight / 2.0)  -- Half height
  TrackSquare -> Corner.uniform 0.0                    -- No radius
  TrackPill -> Corner.uniform trackHeight              -- Full height

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // playhead geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete playhead geometry — all spatial properties.
-- |
-- | ## Bounds
-- |
-- | - Button size: 16-256 pixels (via PlayheadSize)
-- | - Track height: 2-64 pixels
-- | - Track radius: via CornerRadii (0-1000)
-- | - Thumb size: 8-128 pixels
-- | - Padding: via SpacingValue (0-1000)
type PlayheadGeometry =
  { -- Button dimensions
    buttonSize :: PlayheadSize        -- ^ Size of control buttons
    -- Track dimensions (for scrubber)
  , trackHeight :: Number             -- ^ Track height in pixels (bounded 2-64)
  , trackShape :: TrackShape          -- ^ Track corner style
    -- Thumb dimensions (for scrubber)
  , thumbSize :: Number               -- ^ Thumb diameter in pixels (bounded 8-128)
  , thumbVisible :: Boolean           -- ^ Show thumb on scrubber
    -- Spacing
  , padding :: Spacing.SpacingValue   -- ^ Internal padding
  , gap :: Spacing.SpacingValue       -- ^ Gap between elements
  }

-- | Default playhead geometry.
-- |
-- | Medium size buttons, 4px track, 16px thumb, 8px padding.
defaultGeometry :: PlayheadGeometry
defaultGeometry =
  { buttonSize: SizeMd
  , trackHeight: 4.0
  , trackShape: TrackRounded
  , thumbSize: 16.0
  , thumbVisible: true
  , padding: Spacing.spacingSm
  , gap: Spacing.spacingSm
  }

-- | Compact geometry for small UIs.
-- |
-- | Small buttons, thin track, small thumb.
compactGeometry :: PlayheadGeometry
compactGeometry =
  { buttonSize: SizeSm
  , trackHeight: 2.0
  , trackShape: TrackRounded
  , thumbSize: 12.0
  , thumbVisible: true
  , padding: Spacing.spacingXs
  , gap: Spacing.spacingXs
  }

-- | Large geometry for TV/hero UIs.
-- |
-- | Extra large buttons, thick track, large thumb.
largeGeometry :: PlayheadGeometry
largeGeometry =
  { buttonSize: SizeXl
  , trackHeight: 8.0
  , trackShape: TrackRounded
  , thumbSize: 24.0
  , thumbVisible: true
  , padding: Spacing.spacingMd
  , gap: Spacing.spacingMd
  }

-- | Scrubber-only geometry (no buttons).
-- |
-- | Just the track and thumb, minimal padding.
scrubberGeometry :: PlayheadGeometry
scrubberGeometry =
  { buttonSize: SizeXs  -- Won't be used, but must have value
  , trackHeight: 4.0
  , trackShape: TrackPill
  , thumbSize: 16.0
  , thumbVisible: true
  , padding: Spacing.spacingZero
  , gap: Spacing.spacingZero
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get button size.
getButtonSize :: PlayheadGeometry -> PlayheadSize
getButtonSize g = g.buttonSize

-- | Get track height in pixels.
getTrackHeight :: PlayheadGeometry -> Number
getTrackHeight g = Bounded.clampNumber 2.0 64.0 g.trackHeight

-- | Get track corner radii based on shape.
getTrackRadius :: PlayheadGeometry -> Corner.CornerRadii
getTrackRadius g = trackShapeToRadius g.trackShape g.trackHeight

-- | Get thumb size in pixels.
getThumbSize :: PlayheadGeometry -> Number
getThumbSize g = Bounded.clampNumber 8.0 128.0 g.thumbSize

-- | Get padding.
getPadding :: PlayheadGeometry -> Spacing.SpacingValue
getPadding g = g.padding

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button size.
setButtonSize :: PlayheadSize -> PlayheadGeometry -> PlayheadGeometry
setButtonSize size g = g { buttonSize = size }

-- | Set track height (bounded 2-64).
setTrackHeight :: Number -> PlayheadGeometry -> PlayheadGeometry
setTrackHeight h g = g { trackHeight = Bounded.clampNumber 2.0 64.0 h }

-- | Set track corner radius via shape.
setTrackRadius :: TrackShape -> PlayheadGeometry -> PlayheadGeometry
setTrackRadius shape g = g { trackShape = shape }

-- | Set thumb size (bounded 8-128).
setThumbSize :: Number -> PlayheadGeometry -> PlayheadGeometry
setThumbSize s g = g { thumbSize = Bounded.clampNumber 8.0 128.0 s }

-- | Set padding.
setPadding :: Number -> PlayheadGeometry -> PlayheadGeometry
setPadding p g = g { padding = Spacing.spacingValue p }
