-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // element // knob // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | KnobGeometry — Spatial atoms for rotational knob controls.
-- |
-- | ## Design Philosophy
-- |
-- | Knob geometry is fundamentally ANGULAR, not linear like sliders.
-- | Core concepts:
-- | - **Diameter**: Overall knob size
-- | - **Arc**: The rotation range (start angle to end angle)
-- | - **Indicator**: The pointer/notch showing current value
-- | - **Track**: The arc path around the knob
-- |
-- | ## Angular Geometry
-- |
-- | Most knobs use a 270-degree arc (-135 to +135):
-- | - Bottom center (180) is the "dead zone"
-- | - Counter-clockwise from bottom = minimum
-- | - Clockwise from bottom = maximum
-- |
-- | Full-rotation knobs (360 degrees) are used for:
-- | - Endless encoders
-- | - Pan controls (center detent)
-- | - Hue selection wheels
-- |
-- | ## Verified Atoms
-- |
-- | - Degrees (Geometry.Angle) — Angular positions
-- | - Pixel (Dimension.Device.Types) — Physical dimensions
-- | - Range (Dimension.Range) — Angular bounds
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Angle (Degrees, angular math)
-- | - Hydrogen.Schema.Dimension.Device.Types (Pixel)
-- | - Hydrogen.Schema.Bounded (clamping)

module Hydrogen.Schema.Element.Knob.Geometry
  ( -- * Knob Size Presets
    KnobSize
      ( SizeTiny
      , SizeSmall
      , SizeMedium
      , SizeLarge
      , SizeHuge
      , SizeCustom
      )
  , sizeToDiameter
  
  -- * Arc Configuration
  , ArcConfig
  , arcStandard
  , arcFull
  , arcHalf
  , arcCompact
  
  -- * Knob Geometry Record
  , KnobGeometry
  , defaultGeometry
  , compactGeometry
  , largeGeometry
  , hugeGeometry
  , dawGeometry
  , medicalGeometry
  , gameGeometry
  
  -- * Geometry Accessors
  , getDiameter
  , getRadius
  , getArcConfig
  , getStartAngle
  , getEndAngle
  , getArcSweep
  , getIndicatorLength
  , getTrackWidth
  , getCenterCapRadius
  
  -- * Geometry Modifiers
  , setSize
  , setDiameter
  , setArcConfig
  , setIndicatorLength
  , setTrackWidth
  , setCenterCapRadius
  
  -- * Computed Properties
  , angleForProgress
  , progressForAngle
  , indicatorEndpoint
  , arcPath
  , isAngleInRange
  
  -- * Re-exports
  , module Hydrogen.Schema.Geometry.Angle
  , module Hydrogen.Schema.Dimension.Device.Types
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (/)
  , (-)
  , (*)
  , (+)
  , (<>)
  , (==)
  , (&&)
  , (||)
  , (>)
  , (<)
  , (>=)
  , (<=)
  )

import Prim (Boolean, Number, String)

import Data.Number (cos, sin, pi) as Number

import Hydrogen.Schema.Geometry.Angle
  ( Degrees
  , degrees
  , unwrapDegrees
  , zero
  , half
  , quarter
  , addAngle
  , subtractAngle
  , sinAngle
  , cosAngle
  )

import Hydrogen.Schema.Dimension.Device.Types
  ( Pixel(Pixel)
  )

import Hydrogen.Schema.Bounded as Bounded

-- | Unwrap Pixel to Number (inline to avoid cross-module dependency)
unwrapPixel :: Pixel -> Number
unwrapPixel (Pixel n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // knob size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Predefined knob sizes.
-- |
-- | Size recommendations by domain:
-- | - DAW: Small (24-32px) — screen real estate precious
-- | - Game: Medium (40-48px) — balance of touch and visuals
-- | - Medical: Large-Huge (64-80px) — glove-operable, high contrast
data KnobSize
  = SizeTiny       -- ^ 20px diameter (parameter fine-tuning)
  | SizeSmall      -- ^ 28px diameter (DAW default)
  | SizeMedium     -- ^ 40px diameter (general purpose)
  | SizeLarge      -- ^ 56px diameter (touch-friendly)
  | SizeHuge       -- ^ 80px diameter (medical, accessibility)
  | SizeCustom Pixel  -- ^ Custom diameter

derive instance eqKnobSize :: Eq KnobSize
derive instance ordKnobSize :: Ord KnobSize

instance showKnobSize :: Show KnobSize where
  show SizeTiny = "tiny"
  show SizeSmall = "small"
  show SizeMedium = "medium"
  show SizeLarge = "large"
  show SizeHuge = "huge"
  show (SizeCustom p) = "custom:" <> show p

-- | Convert size preset to diameter in pixels.
sizeToDiameter :: KnobSize -> Pixel
sizeToDiameter = case _ of
  SizeTiny -> Pixel 20.0
  SizeSmall -> Pixel 28.0
  SizeMedium -> Pixel 40.0
  SizeLarge -> Pixel 56.0
  SizeHuge -> Pixel 80.0
  SizeCustom p -> p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // arc configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Arc configuration — defines the rotation range.
-- |
-- | The arc is defined by:
-- | - startAngle: Where minimum value is shown
-- | - endAngle: Where maximum value is shown
-- | - sweepDirection: Clockwise (true) or counter-clockwise (false)
-- |
-- | Standard convention (270-degree arc):
-- | - startAngle: 225 degrees (lower-left, 7 o'clock position)
-- | - endAngle: 315 degrees (lower-right, 5 o'clock position)
-- | - This leaves a 90-degree "dead zone" at the bottom
type ArcConfig =
  { startAngle :: Degrees      -- ^ Angle for minimum value
  , endAngle :: Degrees        -- ^ Angle for maximum value
  , clockwise :: Boolean       -- ^ Sweep direction
  }

-- | Standard 270-degree arc (most common).
-- |
-- | Leaves dead zone at bottom (6 o'clock).
-- | Min at 7 o'clock, max at 5 o'clock.
arcStandard :: ArcConfig
arcStandard =
  { startAngle: degrees 225.0   -- 7 o'clock (min)
  , endAngle: degrees 315.0     -- 5 o'clock (max)
  , clockwise: true
  }

-- | Full 360-degree arc (endless encoder, hue knob).
-- |
-- | No dead zone, wraps around.
-- | 12 o'clock (top) is typically the start/end point.
arcFull :: ArcConfig
arcFull =
  { startAngle: degrees 270.0   -- 12 o'clock
  , endAngle: degrees 270.0     -- Full rotation back to start
  , clockwise: true
  }

-- | Half arc (180 degrees).
-- |
-- | Min at 9 o'clock, max at 3 o'clock.
-- | Good for compact horizontal layouts.
arcHalf :: ArcConfig
arcHalf =
  { startAngle: degrees 180.0   -- 9 o'clock
  , endAngle: degrees 0.0       -- 3 o'clock
  , clockwise: true
  }

-- | Compact 240-degree arc.
-- |
-- | Slightly smaller than standard, larger dead zone.
arcCompact :: ArcConfig
arcCompact =
  { startAngle: degrees 210.0   -- 8 o'clock
  , endAngle: degrees 330.0     -- 4 o'clock
  , clockwise: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // knob geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete knob geometry record.
-- |
-- | All dimensions are in Pixel for device-independence.
-- | Angular values use Degrees for human readability.
type KnobGeometry =
  { -- Size
    size :: KnobSize             -- ^ Size preset
  , diameter :: Pixel            -- ^ Actual diameter (may override size)
    -- Arc
  , arc :: ArcConfig             -- ^ Rotation range configuration
    -- Track (the arc around the knob)
  , trackWidth :: Pixel          -- ^ Width of the arc track
  , trackInset :: Pixel          -- ^ Distance from edge to track center
    -- Indicator (the pointer/notch)
  , indicatorLength :: Pixel     -- ^ Length of indicator line
  , indicatorWidth :: Pixel      -- ^ Width of indicator line
  , indicatorInset :: Pixel      -- ^ Start distance from center
    -- Center cap
  , centerCapRadius :: Pixel     -- ^ Radius of center cap (if any)
    -- Touch target
  , touchPadding :: Pixel        -- ^ Extra touch area around knob
  }

-- | Default knob geometry (medium size, standard arc).
defaultGeometry :: KnobGeometry
defaultGeometry =
  { size: SizeMedium
  , diameter: sizeToDiameter SizeMedium
  , arc: arcStandard
  , trackWidth: Pixel 3.0
  , trackInset: Pixel 2.0
  , indicatorLength: Pixel 12.0
  , indicatorWidth: Pixel 2.0
  , indicatorInset: Pixel 6.0
  , centerCapRadius: Pixel 6.0
  , touchPadding: Pixel 8.0
  }

-- | Compact geometry for DAW/parameter panels.
compactGeometry :: KnobGeometry
compactGeometry = defaultGeometry
  { size = SizeSmall
  , diameter = sizeToDiameter SizeSmall
  , trackWidth = Pixel 2.0
  , trackInset = Pixel 1.0
  , indicatorLength = Pixel 8.0
  , indicatorWidth = Pixel 1.5
  , indicatorInset = Pixel 4.0
  , centerCapRadius = Pixel 4.0
  , touchPadding = Pixel 4.0
  }

-- | Large touch-friendly geometry.
largeGeometry :: KnobGeometry
largeGeometry = defaultGeometry
  { size = SizeLarge
  , diameter = sizeToDiameter SizeLarge
  , trackWidth = Pixel 4.0
  , trackInset = Pixel 3.0
  , indicatorLength = Pixel 18.0
  , indicatorWidth = Pixel 3.0
  , indicatorInset = Pixel 8.0
  , centerCapRadius = Pixel 10.0
  , touchPadding = Pixel 12.0
  }

-- | Huge accessibility/medical geometry.
hugeGeometry :: KnobGeometry
hugeGeometry = defaultGeometry
  { size = SizeHuge
  , diameter = sizeToDiameter SizeHuge
  , trackWidth = Pixel 6.0
  , trackInset = Pixel 4.0
  , indicatorLength = Pixel 28.0
  , indicatorWidth = Pixel 4.0
  , indicatorInset = Pixel 12.0
  , centerCapRadius = Pixel 16.0
  , touchPadding = Pixel 16.0
  }

-- | DAW-optimized geometry (small, dense).
dawGeometry :: KnobGeometry
dawGeometry = compactGeometry
  { arc = arcCompact  -- Slightly smaller arc for tighter layouts
  }

-- | Medical-grade geometry (huge, clear indicators).
medicalGeometry :: KnobGeometry
medicalGeometry = hugeGeometry
  { arc = arcStandard  -- Standard arc with clear boundaries
  , trackWidth = Pixel 8.0  -- Very visible track
  , indicatorWidth = Pixel 6.0  -- Bold indicator
  }

-- | Game UI geometry (medium with full rotation).
gameGeometry :: KnobGeometry
gameGeometry = defaultGeometry
  { arc = arcFull  -- Full rotation for hue/endless controls
  , trackWidth = Pixel 4.0
  , centerCapRadius = Pixel 8.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get knob diameter.
getDiameter :: KnobGeometry -> Pixel
getDiameter g = g.diameter

-- | Get knob radius.
getRadius :: KnobGeometry -> Pixel
getRadius g = Pixel (unwrapPixel g.diameter / 2.0)

-- | Get arc configuration.
getArcConfig :: KnobGeometry -> ArcConfig
getArcConfig g = g.arc

-- | Get start angle.
getStartAngle :: KnobGeometry -> Degrees
getStartAngle g = g.arc.startAngle

-- | Get end angle.
getEndAngle :: KnobGeometry -> Degrees
getEndAngle g = g.arc.endAngle

-- | Get arc sweep (total rotation range).
getArcSweep :: KnobGeometry -> Degrees
getArcSweep g =
  let startDeg = unwrapDegrees g.arc.startAngle
      endDeg = unwrapDegrees g.arc.endAngle
      -- Calculate sweep based on direction
      sweep = if g.arc.clockwise
              then if endDeg > startDeg
                   then endDeg - startDeg
                   else 360.0 - startDeg + endDeg
              else if startDeg > endDeg
                   then startDeg - endDeg
                   else 360.0 - endDeg + startDeg
  in degrees sweep

-- | Get indicator length.
getIndicatorLength :: KnobGeometry -> Pixel
getIndicatorLength g = g.indicatorLength

-- | Get track width.
getTrackWidth :: KnobGeometry -> Pixel
getTrackWidth g = g.trackWidth

-- | Get center cap radius.
getCenterCapRadius :: KnobGeometry -> Pixel
getCenterCapRadius g = g.centerCapRadius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set size preset (also updates diameter).
setSize :: KnobSize -> KnobGeometry -> KnobGeometry
setSize s g = g { size = s, diameter = sizeToDiameter s }

-- | Set diameter directly (size becomes Custom).
setDiameter :: Pixel -> KnobGeometry -> KnobGeometry
setDiameter d g = g { size = SizeCustom d, diameter = d }

-- | Set arc configuration.
setArcConfig :: ArcConfig -> KnobGeometry -> KnobGeometry
setArcConfig a g = g { arc = a }

-- | Set indicator length (bounded 0-diameter).
setIndicatorLength :: Pixel -> KnobGeometry -> KnobGeometry
setIndicatorLength l g = 
  let maxLen = unwrapPixel g.diameter / 2.0
      bounded = Bounded.clampNumber 0.0 maxLen (unwrapPixel l)
  in g { indicatorLength = Pixel bounded }

-- | Set track width (bounded 1-diameter/4).
setTrackWidth :: Pixel -> KnobGeometry -> KnobGeometry
setTrackWidth w g = 
  let maxWidth = unwrapPixel g.diameter / 4.0
      bounded = Bounded.clampNumber 1.0 maxWidth (unwrapPixel w)
  in g { trackWidth = Pixel bounded }

-- | Set center cap radius (bounded 0-diameter/2).
setCenterCapRadius :: Pixel -> KnobGeometry -> KnobGeometry
setCenterCapRadius r g = 
  let maxRadius = unwrapPixel g.diameter / 2.0
      bounded = Bounded.clampNumber 0.0 maxRadius (unwrapPixel r)
  in g { centerCapRadius = Pixel bounded }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate angle for a progress value [0, 1].
-- |
-- | Progress 0 -> startAngle
-- | Progress 1 -> endAngle
angleForProgress :: Number -> KnobGeometry -> Degrees
angleForProgress progress g =
  let t = Bounded.clampNumber 0.0 1.0 progress
      startDeg = unwrapDegrees g.arc.startAngle
      sweepDeg = unwrapDegrees (getArcSweep g)
      -- Interpolate along the arc
      angleDeg = if g.arc.clockwise
                 then startDeg + t * sweepDeg
                 else startDeg - t * sweepDeg
  in degrees angleDeg

-- | Calculate progress for an angle.
-- |
-- | Returns 0.0-1.0 representing position along arc.
-- | Returns Nothing if angle is in dead zone (for non-full arcs).
progressForAngle :: Degrees -> KnobGeometry -> Number
progressForAngle angle g =
  let angleDeg = unwrapDegrees angle
      startDeg = unwrapDegrees g.arc.startAngle
      sweepDeg = unwrapDegrees (getArcSweep g)
      -- Calculate offset from start
      offset = if g.arc.clockwise
               then if angleDeg >= startDeg
                    then angleDeg - startDeg
                    else 360.0 - startDeg + angleDeg
               else if angleDeg <= startDeg
                    then startDeg - angleDeg
                    else startDeg + 360.0 - angleDeg
  in Bounded.clampNumber 0.0 1.0 (offset / sweepDeg)

-- | Calculate the endpoint of the indicator line.
-- |
-- | Given a progress value, returns (x, y) offset from center.
-- | Useful for drawing the indicator or tooltip positioning.
indicatorEndpoint :: Number -> KnobGeometry -> { x :: Number, y :: Number }
indicatorEndpoint progress g =
  let angle = angleForProgress progress g
      len = unwrapPixel g.indicatorLength + unwrapPixel g.indicatorInset
      -- Convert angle to radians and calculate position
      -- Note: Degrees are measured from east (3 o'clock), going counter-clockwise
      -- Screen coordinates have Y inverted (down is positive)
      angleRad = unwrapDegrees angle * Number.pi / 180.0
      x = len * Number.cos angleRad
      y = len * Number.sin angleRad
  in { x, y }

-- | Generate SVG arc path data.
-- |
-- | Returns the "d" attribute value for an arc path from progress 0 to given progress.
-- | Useful for drawing the value arc fill.
arcPath :: Number -> KnobGeometry -> String
arcPath progress g =
  let radius = unwrapPixel g.diameter / 2.0 - unwrapPixel g.trackInset
      startAngle = g.arc.startAngle
      endAngle = angleForProgress progress g
      startRad = unwrapDegrees startAngle * Number.pi / 180.0
      endRad = unwrapDegrees endAngle * Number.pi / 180.0
      -- Start point
      x1 = radius * Number.cos startRad
      y1 = radius * Number.sin startRad
      -- End point
      x2 = radius * Number.cos endRad
      y2 = radius * Number.sin endRad
      -- Large arc flag (1 if sweep > 180 degrees)
      sweepDeg = unwrapDegrees (getArcSweep g) * progress
      largeArc = if sweepDeg > 180.0 then "1" else "0"
      -- Sweep flag (1 for clockwise)
      sweepFlag = if g.arc.clockwise then "1" else "0"
  in "M " <> show x1 <> " " <> show y1 
     <> " A " <> show radius <> " " <> show radius 
     <> " 0 " <> largeArc <> " " <> sweepFlag 
     <> " " <> show x2 <> " " <> show y2

-- | Check if an angle is within the arc range.
-- |
-- | Returns true if the angle is between startAngle and endAngle.
-- | Always returns true for full-rotation arcs.
isAngleInRange :: Degrees -> KnobGeometry -> Boolean
isAngleInRange angle g =
  let angleDeg = unwrapDegrees angle
      startDeg = unwrapDegrees g.arc.startAngle
      endDeg = unwrapDegrees g.arc.endAngle
      -- Full rotation - everything is in range
      isFull = startDeg == endDeg
      -- For clockwise arcs
      inRangeCW = if endDeg > startDeg
                  then angleDeg >= startDeg && angleDeg <= endDeg
                  else angleDeg >= startDeg || angleDeg <= endDeg
      -- For counter-clockwise arcs
      inRangeCCW = if startDeg > endDeg
                   then angleDeg <= startDeg && angleDeg >= endDeg
                   else angleDeg <= startDeg || angleDeg >= endDeg
  in isFull || (if g.arc.clockwise then inRangeCW else inRangeCCW)
