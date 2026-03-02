-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // brush // tilt // mapping
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tilt Mapping — Configuration for tilt-to-parameter modulation.
-- |
-- | ## Design Philosophy
-- |
-- | Tilt mapping defines how pen angle affects brush appearance. This enables
-- | natural media simulation: a pencil held flat creates broad, soft strokes;
-- | a marker tilted reveals its chisel edge; a calligraphy brush rotates with
-- | the hand's angle.
-- |
-- | ## Device Agnosticism
-- |
-- | Tilt data comes from many sources:
-- | - **Stylus (EMR/AES)**: Direct tiltX/tiltY from pen sensor
-- | - **Tablet Stylus**: Altitude/azimuth from internal IMU
-- | - **Smartphone/Watch**: Accelerometer pitch/roll, gyroscope heading
-- | - **VR Controllers**: Full 6DOF orientation quaternion
-- |
-- | The TiltMapping configuration works identically regardless of source —
-- | the runtime normalizes device-specific data to Altitude/Azimuth before
-- | applying the mapping.
-- |
-- | ## Key Properties
-- |
-- | - **affectsRoundness**: Flatten brush ellipse when tilted
-- | - **affectsAngle**: Rotate brush tip to match tilt direction
-- | - **affectsSize**: Expand brush footprint when tilted (pencil shading)
-- | - **affectsOpacity**: Fade stroke when tilted
-- | - **affectsHardness**: Soften edges when tilted
-- | - **simulatesPencilShading**: Full graphite side-shading simulation
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Brush.Tilt.Mapping
  ( -- * TiltMapping Record
    TiltMapping
  , defaultTiltMapping
  , tiltMappingDebugInfo
  
  -- * Presets
  , pencilShadingMapping
  , calligraphyMapping
  , airbrushMapping
  , markerMapping
  , disabledMapping
  
  -- * Queries
  , isFullyEnabled
  , isDisabled
  , affectsShape
  , affectsAppearance
  
  -- * Debug Utilities
  , showWithMapping
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , (<>)
  , (&&)
  , not
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // tilt mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for how tilt modulates brush parameters.
-- |
-- | ## Field Descriptions
-- |
-- | - `affectsRoundness`: When true, brush becomes elliptical when tilted
-- | - `roundnessMin`: Minimum roundness when pen is flat (1-100%)
-- | - `affectsAngle`: When true, brush tip rotates to match azimuth
-- | - `affectsSize`: When true, brush footprint expands when tilted
-- | - `sizeScale`: Maximum size multiplier when fully tilted (1.0-3.0)
-- | - `affectsOpacity`: When true, stroke fades when tilted
-- | - `opacityMin`: Minimum opacity when pen is flat (0.0-1.0)
-- | - `affectsHardness`: When true, edges soften when tilted
-- | - `hardnessMin`: Minimum hardness when pen is flat (0-100%)
-- | - `simulatesPencilShading`: Enables full graphite simulation
-- |
-- | ## Pencil Shading Physics
-- |
-- | When `simulatesPencilShading` is true, the brush simulates how a
-- | graphite pencil behaves when held at an angle:
-- | - Contact area increases (larger, softer strokes)
-- | - Pressure distributes over larger area (lighter deposit)
-- | - Graphite texture becomes visible (grain direction follows azimuth)
type TiltMapping =
  { affectsRoundness :: Boolean
  , roundnessMin :: Number       -- 1-100 percentage
  , affectsAngle :: Boolean
  , affectsSize :: Boolean
  , sizeScale :: Number          -- 1.0-3.0 multiplier
  , affectsOpacity :: Boolean
  , opacityMin :: Number         -- 0.0-1.0
  , affectsHardness :: Boolean
  , hardnessMin :: Number        -- 0-100 percentage
  , simulatesPencilShading :: Boolean
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default tilt mapping: angle follows tilt direction.
-- |
-- | Brush tip rotates to match the direction the pen is tilted,
-- | but shape and opacity remain constant. Suitable for general
-- | digital painting where you want directional control.
defaultTiltMapping :: TiltMapping
defaultTiltMapping =
  { affectsRoundness: false
  , roundnessMin: 10.0           -- Sensible default if enabled
  , affectsAngle: true           -- Tip follows tilt direction
  , affectsSize: false
  , sizeScale: 1.5               -- Sensible default if enabled
  , affectsOpacity: false
  , opacityMin: 0.2              -- Sensible default if enabled
  , affectsHardness: false
  , hardnessMin: 0.0             -- Sensible default if enabled
  , simulatesPencilShading: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pencil shading: tilting creates broad, soft strokes.
-- |
-- | Simulates graphite pencil behavior where holding the pencil
-- | at a low angle produces wide, textured shading strokes.
-- | Used for: sketching, shading, tonal work.
pencilShadingMapping :: TiltMapping
pencilShadingMapping =
  { affectsRoundness: true
  , roundnessMin: 15.0           -- Very flat when tilted
  , affectsAngle: true           -- Follows tilt direction
  , affectsSize: true
  , sizeScale: 2.5               -- Significant expansion when flat
  , affectsOpacity: true
  , opacityMin: 0.3              -- Lighter when tilted (spread deposit)
  , affectsHardness: true
  , hardnessMin: 10.0            -- Very soft edges when flat
  , simulatesPencilShading: true
  }

-- | Calligraphy: tilt affects stroke width via angle.
-- |
-- | Brush tip rotates with tilt direction, creating thick/thin
-- | variation based on stroke direction relative to pen angle.
-- | Used for: brush lettering, expressive calligraphy, Asian brushwork.
calligraphyMapping :: TiltMapping
calligraphyMapping =
  { affectsRoundness: true
  , roundnessMin: 20.0           -- Elliptical when tilted
  , affectsAngle: true           -- Critical for calligraphy
  , affectsSize: false
  , sizeScale: 1.0               -- Size from pressure, not tilt
  , affectsOpacity: false
  , opacityMin: 0.5              -- Sensible default if enabled
  , affectsHardness: false
  , hardnessMin: 50.0            -- Sensible default if enabled
  , simulatesPencilShading: false
  }

-- | Airbrush: tilt spreads spray pattern.
-- |
-- | Tilting the pen widens the spray cone, creating more diffuse
-- | coverage. Perpendicular = tight spot, tilted = wide spray.
-- | Used for: illustration, gradients, soft color work.
airbrushMapping :: TiltMapping
airbrushMapping =
  { affectsRoundness: true
  , roundnessMin: 30.0           -- Becomes elliptical spray pattern
  , affectsAngle: true           -- Spray direction follows tilt
  , affectsSize: true
  , sizeScale: 2.0               -- Spray cone widens when tilted
  , affectsOpacity: true
  , opacityMin: 0.4              -- More diffuse = less opacity per area
  , affectsHardness: true
  , hardnessMin: 0.0             -- Very soft spray edges when tilted
  , simulatesPencilShading: false
  }

-- | Marker: tilt reveals chisel edge.
-- |
-- | Mimics chisel-tip markers where tilting changes which part
-- | of the tip contacts the surface, revealing the wide edge.
-- | Used for: marker rendering, industrial design, bold lettering.
markerMapping :: TiltMapping
markerMapping =
  { affectsRoundness: true
  , roundnessMin: 8.0            -- Very flat chisel edge when tilted
  , affectsAngle: true           -- Chisel direction follows tilt
  , affectsSize: false
  , sizeScale: 1.0               -- Size consistent (chisel is chisel)
  , affectsOpacity: false
  , opacityMin: 0.8              -- Markers are opaque
  , affectsHardness: false
  , hardnessMin: 90.0            -- Hard edges (marker ink)
  , simulatesPencilShading: false
  }

-- | Disabled: tilt has no effect.
-- |
-- | All tilt data is ignored. Brush behaves identically regardless
-- | of pen angle. Used for precise technical work or when tilt
-- | input is unreliable/unwanted.
disabledMapping :: TiltMapping
disabledMapping =
  { affectsRoundness: false
  , roundnessMin: 10.0           -- Sensible default if enabled
  , affectsAngle: false
  , affectsSize: false
  , sizeScale: 1.5               -- Sensible default if enabled
  , affectsOpacity: false
  , opacityMin: 0.2              -- Sensible default if enabled
  , affectsHardness: false
  , hardnessMin: 0.0             -- Sensible default if enabled
  , simulatesPencilShading: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // debug
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debug info string for tilt mapping.
-- |
-- | Shows which parameters are affected and key values.
tiltMappingDebugInfo :: TiltMapping -> String
tiltMappingDebugInfo m =
  "(TiltMapping"
    <> " roundness:" <> showAffectsPercent m.affectsRoundness m.roundnessMin
    <> " angle:" <> showEnabled m.affectsAngle
    <> " size:" <> showAffectsScale m.affectsSize m.sizeScale
    <> " opacity:" <> showAffectsUnit m.affectsOpacity m.opacityMin
    <> " hardness:" <> showAffectsPercent m.affectsHardness m.hardnessMin
    <> " pencilShading:" <> showEnabled m.simulatesPencilShading
    <> ")"
  where
    showAffectsPercent :: Boolean -> Number -> String
    showAffectsPercent enabled minVal =
      if enabled
        then "min:" <> show minVal <> "%"
        else "off"
    
    showAffectsUnit :: Boolean -> Number -> String
    showAffectsUnit enabled minVal =
      if enabled
        then "min:" <> show minVal
        else "off"
    
    showAffectsScale :: Boolean -> Number -> String
    showAffectsScale enabled scaleVal =
      if enabled
        then "scale:" <> show scaleVal <> "x"
        else "off"
    
    showEnabled :: Boolean -> String
    showEnabled enabled = if not enabled then "off" else "on"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if all tilt effects are enabled.
-- |
-- | Returns true only when roundness, angle, size, opacity, hardness,
-- | AND pencil shading are all active. Used to identify "maximum tilt
-- | responsiveness" configurations.
isFullyEnabled :: TiltMapping -> Boolean
isFullyEnabled m =
  m.affectsRoundness
    && m.affectsAngle
    && m.affectsSize
    && m.affectsOpacity
    && m.affectsHardness
    && m.simulatesPencilShading

-- | Check if all tilt effects are disabled.
-- |
-- | Returns true when no tilt modulation is active. Pen angle has
-- | no effect on brush output.
isDisabled :: TiltMapping -> Boolean
isDisabled m =
  not m.affectsRoundness
    && not m.affectsAngle
    && not m.affectsSize
    && not m.affectsOpacity
    && not m.affectsHardness
    && not m.simulatesPencilShading

-- | Check if tilt affects brush shape (roundness or angle).
-- |
-- | Shape effects change the geometric form of the brush tip.
affectsShape :: TiltMapping -> Boolean
affectsShape m = m.affectsRoundness && m.affectsAngle

-- | Check if tilt affects brush appearance (opacity or hardness).
-- |
-- | Appearance effects change how paint is deposited, not tip geometry.
affectsAppearance :: TiltMapping -> Boolean
affectsAppearance m = m.affectsOpacity && m.affectsHardness

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show any value alongside its tilt mapping context.
-- |
-- | Useful for debugging when you need to see both the input value
-- | and the mapping configuration that will be applied to it.
showWithMapping :: forall a. Show a => a -> TiltMapping -> String
showWithMapping value mapping =
  show value <> " with " <> tiltMappingDebugInfo mapping
