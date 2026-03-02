-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // effects // distortion // warp
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Warp Effects — Warp, Bezier Warp, Bulge, Twirl, and Wave Warp effects.
-- |
-- | ## Effects Included
-- |
-- | - **Warp**: standard warp with 15 presets
-- | - **Bezier Warp**: 4-point bezier mesh deformation
-- | - **Bulge**: Spherical bulge distortion
-- | - **Twirl**: Rotational distortion
-- | - **Wave Warp**: Sine wave distortion
-- | - **Ripple**: Radial wave distortion
-- | - **Spherize**: Wrap around sphere
-- | - **Liquify**: Brush-based deformation

module Hydrogen.Schema.Motion.Effects.Distortion.Warp
  ( -- * Warp Effect
    WarpEffect
  , defaultWarp
  , warpWithStyle
  , warpWithBend
  
  -- * Bezier Warp Effect
  , BezierWarpEffect
  , defaultBezierWarp
  
  -- * Bulge Effect
  , BulgeEffect
  , defaultBulge
  , bulgeWithRadius
  
  -- * Twirl Effect
  , TwirlEffect
  , defaultTwirl
  , twirlWithAngle
  
  -- * Wave Warp Effect
  , WaveWarpEffect
  , WaveType(WTSine, WTSquare, WTTriangle, WTSawtooth, WTCircle, WTSemicircle, WTUncircle, WTNoise)
  , defaultWaveWarp
  , waveWarpWithHeight
  
  -- * Ripple Effect
  , RippleEffect
  , RippleConversion(RCSymmetric, RCAsymmetric)
  , defaultRipple
  , rippleWithWaves
  
  -- * Spherize Effect
  , SpherizeEffect
  , defaultSpherize
  , spherizeWithRadius
  
  -- * Liquify Effect
  , LiquifyEffect
  , LiquifyTool(LTWarp, LTTurbulence, LTTwirl, LTTwirlCCW, LTPucker, LTBloat, LTShift, LTReflection, LTReconstruction)
  , defaultLiquify
  
  -- * Serialization
  , liquifyToolToString
  , rippleConversionToString
  , waveTypeToString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , negate
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Motion.Effects.Distortion.Types (WarpStyle(WSArc))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // warp // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Warp Effect — standard warp with 15 presets.
-- |
-- | ## AE Properties
-- |
-- | - Warp Style: One of 15 warp presets
-- | - Bend: Primary bend amount (-100 to 100)
-- | - Horizontal Distortion: Horizontal distortion (-100 to 100)
-- | - Vertical Distortion: Vertical distortion (-100 to 100)
type WarpEffect =
  { warpStyle :: WarpStyle              -- ^ Warp preset
  , bend :: Number                       -- ^ Primary bend (-100 to 100)
  , horizontalDistortion :: Number       -- ^ Horizontal distortion (-100 to 100)
  , verticalDistortion :: Number         -- ^ Vertical distortion (-100 to 100)
  }

-- | Default warp: arc with no bend.
defaultWarp :: WarpEffect
defaultWarp =
  { warpStyle: WSArc
  , bend: 0.0
  , horizontalDistortion: 0.0
  , verticalDistortion: 0.0
  }

-- | Create warp with specific style.
warpWithStyle :: WarpStyle -> WarpEffect
warpWithStyle style =
  { warpStyle: style
  , bend: 50.0
  , horizontalDistortion: 0.0
  , verticalDistortion: 0.0
  }

-- | Create warp with specific bend.
warpWithBend :: Number -> WarpEffect
warpWithBend b =
  { warpStyle: WSArc
  , bend: clampNumber (-100.0) 100.0 b
  , horizontalDistortion: 0.0
  , verticalDistortion: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // bezier // warp
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bezier Warp Effect — 4-point bezier mesh deformation.
-- |
-- | ## AE Properties
-- |
-- | 4 corner points with tangent handles for bezier curve control.
type BezierWarpEffect =
  { topLeft :: Point2D                   -- ^ Top-left corner
  , topRight :: Point2D                  -- ^ Top-right corner
  , bottomLeft :: Point2D                -- ^ Bottom-left corner
  , bottomRight :: Point2D               -- ^ Bottom-right corner
  , topLeftTangent :: Point2D            -- ^ Top-left tangent
  , topRightTangent :: Point2D           -- ^ Top-right tangent
  , bottomLeftTangent :: Point2D         -- ^ Bottom-left tangent
  , bottomRightTangent :: Point2D        -- ^ Bottom-right tangent
  , quality :: Int                        -- ^ Render quality (1-10)
  }

-- | Default bezier warp (unit square, no distortion).
defaultBezierWarp :: BezierWarpEffect
defaultBezierWarp =
  { topLeft: point2D 0.0 0.0
  , topRight: point2D 100.0 0.0
  , bottomLeft: point2D 0.0 100.0
  , bottomRight: point2D 100.0 100.0
  , topLeftTangent: point2D 0.0 0.0
  , topRightTangent: point2D 0.0 0.0
  , bottomLeftTangent: point2D 0.0 0.0
  , bottomRightTangent: point2D 0.0 0.0
  , quality: 5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // bulge // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bulge Effect — Spherical bulge distortion.
-- |
-- | ## AE Properties
-- |
-- | - Horizontal Radius: Horizontal bulge size (0-1000)
-- | - Vertical Radius: Vertical bulge size (0-1000)
-- | - Bulge Center: Center point
-- | - Bulge Height: Distortion amount (-4 to 4)
-- | - Taper Radius: Edge falloff (0-100%)
-- | - Antialiasing: Edge smoothing
type BulgeEffect =
  { horizontalRadius :: Number           -- ^ Horizontal size (0-1000)
  , verticalRadius :: Number             -- ^ Vertical size (0-1000)
  , bulgeCenter :: Point2D               -- ^ Center point
  , bulgeHeight :: Number                -- ^ Distortion (-4 to 4)
  , taperRadius :: Number                -- ^ Edge falloff (0-100)
  , antialiasing :: Boolean              -- ^ Edge smoothing
  , pinAllEdges :: Boolean               -- ^ Lock edges
  }

-- | Default bulge.
defaultBulge :: BulgeEffect
defaultBulge =
  { horizontalRadius: 100.0
  , verticalRadius: 100.0
  , bulgeCenter: point2D 50.0 50.0
  , bulgeHeight: 1.0
  , taperRadius: 0.0
  , antialiasing: true
  , pinAllEdges: false
  }

-- | Create bulge with specific radius.
bulgeWithRadius :: Number -> Number -> Number -> BulgeEffect
bulgeWithRadius hRadius vRadius height =
  { horizontalRadius: clampNumber 0.0 1000.0 hRadius
  , verticalRadius: clampNumber 0.0 1000.0 vRadius
  , bulgeCenter: point2D 50.0 50.0
  , bulgeHeight: clampNumber (-4.0) 4.0 height
  , taperRadius: 0.0
  , antialiasing: true
  , pinAllEdges: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // twirl // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Twirl Effect — Rotational distortion.
-- |
-- | ## AE Properties
-- |
-- | - Angle: Twirl amount (-3600 to 3600 degrees)
-- | - Twirl Radius: Radius of twirl (0-2000)
-- | - Twirl Center: Center point
type TwirlEffect =
  { angle :: Number                      -- ^ Twirl amount (-3600 to 3600)
  , twirlRadius :: Number                -- ^ Radius (0-2000)
  , twirlCenter :: Point2D               -- ^ Center point
  }

-- | Default twirl.
defaultTwirl :: TwirlEffect
defaultTwirl =
  { angle: 0.0
  , twirlRadius: 100.0
  , twirlCenter: point2D 50.0 50.0
  }

-- | Create twirl with specific angle.
twirlWithAngle :: Number -> Number -> TwirlEffect
twirlWithAngle ang radius =
  { angle: clampNumber (-3600.0) 3600.0 ang
  , twirlRadius: clampNumber 0.0 2000.0 radius
  , twirlCenter: point2D 50.0 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // wave // warp
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wave warp type.
data WaveType
  = WTSine             -- ^ Sine wave
  | WTSquare           -- ^ Square wave
  | WTTriangle         -- ^ Triangle wave
  | WTSawtooth         -- ^ Sawtooth wave
  | WTCircle           -- ^ Circular wave
  | WTSemicircle       -- ^ Semicircle wave
  | WTUncircle         -- ^ Inverted circle
  | WTNoise            -- ^ Random noise

derive instance eqWaveType :: Eq WaveType
derive instance ordWaveType :: Ord WaveType

instance showWaveType :: Show WaveType where
  show WTSine = "sine"
  show WTSquare = "square"
  show WTTriangle = "triangle"
  show WTSawtooth = "sawtooth"
  show WTCircle = "circle"
  show WTSemicircle = "semicircle"
  show WTUncircle = "uncircle"
  show WTNoise = "noise"

-- | Wave Warp Effect — Sine wave distortion.
-- |
-- | ## AE Properties
-- |
-- | - Wave Type: Shape of wave
-- | - Wave Height: Amplitude (0-500)
-- | - Wave Width: Wavelength (1-1000)
-- | - Direction: Wave direction (0-360)
-- | - Wave Speed: Animation speed
-- | - Pinning: Edge pinning
-- | - Phase: Wave phase offset
type WaveWarpEffect =
  { waveType :: WaveType                 -- ^ Wave shape
  , waveHeight :: Number                 -- ^ Amplitude (0-500)
  , waveWidth :: Number                  -- ^ Wavelength (1-1000)
  , direction :: Number                  -- ^ Direction angle (0-360)
  , waveSpeed :: Number                  -- ^ Animation speed
  , pinning :: Int                       -- ^ Edge pinning (0-4)
  , phase :: Number                      -- ^ Phase offset (0-360)
  , antialiasing :: Boolean              -- ^ Edge smoothing
  }

-- | Default wave warp.
defaultWaveWarp :: WaveWarpEffect
defaultWaveWarp =
  { waveType: WTSine
  , waveHeight: 25.0
  , waveWidth: 100.0
  , direction: 0.0
  , waveSpeed: 1.0
  , pinning: 0
  , phase: 0.0
  , antialiasing: true
  }

-- | Create wave warp with specific height.
waveWarpWithHeight :: Number -> Number -> WaveWarpEffect
waveWarpWithHeight height width =
  { waveType: WTSine
  , waveHeight: clampNumber 0.0 500.0 height
  , waveWidth: clampNumber 1.0 1000.0 width
  , direction: 0.0
  , waveSpeed: 1.0
  , pinning: 0
  , phase: 0.0
  , antialiasing: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // ripple // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ripple conversion type.
data RippleConversion
  = RCSymmetric        -- ^ Symmetric ripples
  | RCAsymmetric       -- ^ Asymmetric ripples

derive instance eqRippleConversion :: Eq RippleConversion
derive instance ordRippleConversion :: Ord RippleConversion

instance showRippleConversion :: Show RippleConversion where
  show RCSymmetric = "symmetric"
  show RCAsymmetric = "asymmetric"

-- | Ripple Effect — Radial wave distortion.
-- |
-- | ## AE Properties
-- |
-- | - Radius: Ripple radius (0-2000)
-- | - Wavelength: Distance between ripples (1-1000)
-- | - Phase: Ripple animation phase (0-360)
-- | - Amplitude: Ripple height (-500 to 500)
-- | - Center: Ripple center point
type RippleEffect =
  { radius :: Number                     -- ^ Ripple radius (0-2000)
  , center :: Point2D                    -- ^ Center point
  , conversion :: RippleConversion       -- ^ Ripple type
  , waveSpeed :: Number                  -- ^ Animation speed (0-100)
  , waveWidth :: Number                  -- ^ Wavelength (1-1000)
  , waveHeight :: Number                 -- ^ Amplitude (-500 to 500)
  , ripplePhase :: Number                -- ^ Phase (0-360)
  }

-- | Default ripple.
defaultRipple :: RippleEffect
defaultRipple =
  { radius: 100.0
  , center: point2D 50.0 50.0
  , conversion: RCSymmetric
  , waveSpeed: 1.0
  , waveWidth: 30.0
  , waveHeight: 20.0
  , ripplePhase: 0.0
  }

-- | Create ripple with specific wave count.
rippleWithWaves :: Number -> Number -> RippleEffect
rippleWithWaves width height =
  { radius: 100.0
  , center: point2D 50.0 50.0
  , conversion: RCSymmetric
  , waveSpeed: 1.0
  , waveWidth: clampNumber 1.0 1000.0 width
  , waveHeight: clampNumber (-500.0) 500.0 height
  , ripplePhase: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // spherize // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spherize Effect — Wrap around sphere.
-- |
-- | ## AE Properties
-- |
-- | - Radius: Sphere radius (0-1000)
-- | - Center: Center of sphere
-- | - Normal: Spherize (positive) or pinch (negative)
type SpherizeEffect =
  { radius :: Number                     -- ^ Sphere radius (0-1000)
  , center :: Point2D                    -- ^ Center point
  , amount :: Number                     -- ^ Distortion amount (-100 to 100)
  }

-- | Default spherize.
defaultSpherize :: SpherizeEffect
defaultSpherize =
  { radius: 100.0
  , center: point2D 50.0 50.0
  , amount: 100.0
  }

-- | Create spherize with specific radius.
spherizeWithRadius :: Number -> Number -> SpherizeEffect
spherizeWithRadius r amt =
  { radius: clampNumber 0.0 1000.0 r
  , center: point2D 50.0 50.0
  , amount: clampNumber (-100.0) 100.0 amt
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // liquify // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Liquify tool type.
data LiquifyTool
  = LTWarp             -- ^ Push/warp
  | LTTurbulence       -- ^ Turbulent displacement
  | LTTwirl            -- ^ Twirl clockwise
  | LTTwirlCCW         -- ^ Twirl counter-clockwise
  | LTPucker           -- ^ Pucker (contract)
  | LTBloat            -- ^ Bloat (expand)
  | LTShift            -- ^ Shift pixels
  | LTReflection       -- ^ Reflect
  | LTReconstruction   -- ^ Reconstruct/restore

derive instance eqLiquifyTool :: Eq LiquifyTool
derive instance ordLiquifyTool :: Ord LiquifyTool

instance showLiquifyTool :: Show LiquifyTool where
  show LTWarp = "warp"
  show LTTurbulence = "turbulence"
  show LTTwirl = "twirl"
  show LTTwirlCCW = "twirl-ccw"
  show LTPucker = "pucker"
  show LTBloat = "bloat"
  show LTShift = "shift"
  show LTReflection = "reflection"
  show LTReconstruction = "reconstruction"

-- | Liquify Effect — Brush-based deformation.
-- |
-- | ## AE Properties
-- |
-- | Interactive brush-based distortion (like professional liquify tools).
type LiquifyEffect =
  { tool :: LiquifyTool                  -- ^ Active tool
  , brushSize :: Number                  -- ^ Brush size (1-1500)
  , brushPressure :: Number              -- ^ Brush pressure (0-100)
  , brushRate :: Number                  -- ^ Brush rate (0-100)
  , turbulentJitter :: Number            -- ^ Turbulence randomness (0-100)
  , reconstructionMode :: Int            -- ^ Reconstruction mode (0-5)
  , distortionMesh :: Array Point2D      -- ^ Mesh deformation points
  }

-- | Default liquify.
defaultLiquify :: LiquifyEffect
defaultLiquify =
  { tool: LTWarp
  , brushSize: 100.0
  , brushPressure: 50.0
  , brushRate: 50.0
  , turbulentJitter: 0.0
  , reconstructionMode: 0
  , distortionMesh: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // serialization
-- ═════════════════════════════════════════════════════════════════════════════

liquifyToolToString :: LiquifyTool -> String
liquifyToolToString = show

rippleConversionToString :: RippleConversion -> String
rippleConversionToString = show

waveTypeToString :: WaveType -> String
waveTypeToString = show
