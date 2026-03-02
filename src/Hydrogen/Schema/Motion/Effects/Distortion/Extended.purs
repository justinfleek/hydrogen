-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--          // hydrogen // schema // motion // effects // distortion // extended
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Extended Distortion Effects — Advanced distortion effects for motion graphics.
-- |
-- | ## Effects Included
-- |
-- | - **Bend It**: Bend layer around axis
-- | - **Blobbylize**: Organic blob distortion
-- | - **Flo Motion**: Flow-based motion blur
-- | - **Griddler**: Grid-based distortion
-- | - **Lens Distortion**: Lens distortion effect
-- | - **Page Turn**: Page turn effect
-- | - **Power Pin**: Advanced corner pin
-- | - **Ripple Pulse**: Expanding ripple
-- | - **Slant**: Perspective slant
-- | - **Smear**: Directional smear
-- | - **Split**: Split/duplicate effect
-- | - **Tiler**: Tiling effect

module Hydrogen.Schema.Motion.Effects.Distortion.Extended
  ( -- * Bend It Effect
    BendItEffect
  , defaultBendIt
  
  -- * Blobbylize Effect
  , BlobbylizeEffect
  , defaultBlobbylize
  
  -- * Flo Motion Effect
  , FloMotionEffect
  , defaultFloMotion
  
  -- * Griddler Effect
  , GriddlerEffect
  , defaultGriddler
  
  -- * Lens Distortion Effect
  , LensDistortionEffect
  , defaultLensDistortion
  
  -- * Page Turn Effect
  , PageTurnEffect
  , defaultPageTurn
  
  -- * Power Pin Effect
  , PowerPinEffect
  , defaultPowerPin
  
  -- * Ripple Pulse Effect
  , RipplePulseEffect
  , defaultRipplePulse
  
  -- * Slant Effect
  , SlantEffect
  , defaultSlant
  
  -- * Smear Effect
  , SmearEffect
  , defaultSmear
  
  -- * Split Effect  
  , SplitEffect
  , SplitDirection(SDHorizontal, SDVertical, SDBoth)
  , defaultSplit
  
  -- * Tiler Effect
  , TilerEffect
  , defaultTiler
  
  -- * Serialization
  , splitDirectionToString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  )

import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // bend // it
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bend It Effect — Bend layer around axis.
type BendItEffect =
  { start :: Point2D                     -- ^ Start point
  , finish :: Point2D                    -- ^ End point
  , bend :: Number                       -- ^ Bend amount (-100 to 100)
  , quality :: Int                       -- ^ Render quality (1-10)
  }

-- | Default Bend It.
defaultBendIt :: BendItEffect
defaultBendIt =
  { start: point2D 0.0 50.0
  , finish: point2D 100.0 50.0
  , bend: 0.0
  , quality: 5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // blobbylize
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blobbylize Effect — Organic blob distortion.
type BlobbylizeEffect =
  { softness :: Number                   -- ^ Blob softness (0-100)
  , cutAway :: Number                    -- ^ Cut away amount (0-100)
  , blobLayer :: Int                     -- ^ Control layer index
  , property :: Int                      -- ^ Property to use (0-3)
  }

-- | Default Blobbylize.
defaultBlobbylize :: BlobbylizeEffect
defaultBlobbylize =
  { softness: 50.0
  , cutAway: 50.0
  , blobLayer: 1
  , property: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // flo // motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flo Motion Effect — Flow-based motion blur.
type FloMotionEffect =
  { gradientLayer :: Int                 -- ^ Flow gradient layer
  , timeStep :: Number                   -- ^ Time step (0-100)
  , motionVectors :: Int                 -- ^ Vector count (1-32)
  , quality :: Int                       -- ^ Render quality (1-10)
  }

-- | Default Flo Motion.
defaultFloMotion :: FloMotionEffect
defaultFloMotion =
  { gradientLayer: 1
  , timeStep: 50.0
  , motionVectors: 8
  , quality: 5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // griddler
-- ═════════════════════════════════════════════════════════════════════════════

-- | Griddler Effect — Grid-based distortion.
type GriddlerEffect =
  { horizontalScale :: Number            -- ^ Horizontal scale (0-200)
  , verticalScale :: Number              -- ^ Vertical scale (0-200)
  , rotation :: Number                   -- ^ Grid rotation (0-360)
  , rows :: Int                          -- ^ Grid rows (1-100)
  , columns :: Int                       -- ^ Grid columns (1-100)
  , offset :: Point2D                    -- ^ Grid offset
  }

-- | Default Griddler.
defaultGriddler :: GriddlerEffect
defaultGriddler =
  { horizontalScale: 100.0
  , verticalScale: 100.0
  , rotation: 0.0
  , rows: 10
  , columns: 10
  , offset: point2D 0.0 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // lens // distortion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lens Distortion Effect — Lens distortion.
type LensDistortionEffect =
  { center :: Point2D                    -- ^ Lens center
  , size :: Number                       -- ^ Lens size (0-1000)
  , convergence :: Number                -- ^ Convergence (-100 to 100)
  }

-- | Default Lens Distortion.
defaultLensDistortion :: LensDistortionEffect
defaultLensDistortion =
  { center: point2D 50.0 50.0
  , size: 100.0
  , convergence: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // page // turn
-- ═════════════════════════════════════════════════════════════════════════════

-- | Page Turn Effect — Page turn effect.
type PageTurnEffect =
  { foldPosition :: Number               -- ^ Fold position (0-100)
  , foldRadius :: Number                 -- ^ Fold radius (0-200)
  , foldDirection :: Number              -- ^ Fold direction (0-360)
  , lightDirection :: Number             -- ^ Light angle (0-360)
  , lightIntensity :: Number             -- ^ Light strength (0-100)
  , backPageOpacity :: Number            -- ^ Back opacity (0-100)
  , backPageColor :: Boolean             -- ^ Use solid color for back
  }

-- | Default Page Turn.
defaultPageTurn :: PageTurnEffect
defaultPageTurn =
  { foldPosition: 50.0
  , foldRadius: 25.0
  , foldDirection: 0.0
  , lightDirection: 135.0
  , lightIntensity: 50.0
  , backPageOpacity: 100.0
  , backPageColor: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // power // pin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Power Pin Effect — Advanced corner pin.
type PowerPinEffect =
  { topLeft :: Point2D                   -- ^ Top-left corner
  , topRight :: Point2D                  -- ^ Top-right corner
  , bottomLeft :: Point2D                -- ^ Bottom-left corner
  , bottomRight :: Point2D               -- ^ Bottom-right corner
  , perspective :: Boolean               -- ^ Perspective mode
  , autoFocal :: Boolean                 -- ^ Auto focal length
  , focalLength :: Number                -- ^ Manual focal length
  }

-- | Default Power Pin.
defaultPowerPin :: PowerPinEffect
defaultPowerPin =
  { topLeft: point2D 0.0 0.0
  , topRight: point2D 100.0 0.0
  , bottomLeft: point2D 0.0 100.0
  , bottomRight: point2D 100.0 100.0
  , perspective: true
  , autoFocal: true
  , focalLength: 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // ripple // pulse
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ripple Pulse Effect — Expanding ripple.
type RipplePulseEffect =
  { center :: Point2D                    -- ^ Ripple center
  , radius :: Number                     -- ^ Ripple radius (0-2000)
  , amplitude :: Number                  -- ^ Wave height (0-200)
  , pulseLevel :: Number                 -- ^ Pulse intensity (0-100)
  , waveWidth :: Number                  -- ^ Wavelength (1-500)
  , phase :: Number                      -- ^ Phase offset (0-360)
  , waveSpeed :: Number                  -- ^ Animation speed
  }

-- | Default Ripple Pulse.
defaultRipplePulse :: RipplePulseEffect
defaultRipplePulse =
  { center: point2D 50.0 50.0
  , radius: 100.0
  , amplitude: 25.0
  , pulseLevel: 100.0
  , waveWidth: 50.0
  , phase: 0.0
  , waveSpeed: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // slant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slant Effect — Perspective slant.
type SlantEffect =
  { slant :: Number                      -- ^ Slant amount (-100 to 100)
  , floor :: Number                      -- ^ Floor position (0-100)
  , height :: Number                     -- ^ Height (0-200)
  , direction :: Number                  -- ^ Slant direction (0-360)
  }

-- | Default Slant.
defaultSlant :: SlantEffect
defaultSlant =
  { slant: 0.0
  , floor: 50.0
  , height: 100.0
  , direction: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // smear
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smear Effect — Directional smear.
type SmearEffect =
  { sourcePoint :: Point2D               -- ^ Source position
  , destinationPoint :: Point2D          -- ^ Destination position
  , percentSource :: Number              -- ^ Source influence (0-100)
  , percentDestination :: Number         -- ^ Destination influence (0-100)
  }

-- | Default Smear.
defaultSmear :: SmearEffect
defaultSmear =
  { sourcePoint: point2D 25.0 50.0
  , destinationPoint: point2D 75.0 50.0
  , percentSource: 50.0
  , percentDestination: 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // split
-- ═════════════════════════════════════════════════════════════════════════════

-- | Split direction.
data SplitDirection
  = SDHorizontal      -- ^ Horizontal split
  | SDVertical        -- ^ Vertical split
  | SDBoth            -- ^ Both directions

derive instance eqSplitDirection :: Eq SplitDirection
derive instance ordSplitDirection :: Ord SplitDirection

instance showSplitDirection :: Show SplitDirection where
  show SDHorizontal = "horizontal"
  show SDVertical = "vertical"
  show SDBoth = "both"

-- | Split Effect — Split/duplicate effect.
type SplitEffect =
  { splitPoint :: Point2D                -- ^ Split position
  , direction :: SplitDirection          -- ^ Split direction
  , splitWidth :: Number                 -- ^ Split gap (0-500)
  }

-- | Default Split.
defaultSplit :: SplitEffect
defaultSplit =
  { splitPoint: point2D 50.0 50.0
  , direction: SDHorizontal
  , splitWidth: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // tiler
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tiler Effect — Tiling effect.
type TilerEffect =
  { scale :: Number                      -- ^ Tile scale (1-1000)
  , offset :: Point2D                    -- ^ Tile offset
  , rotation :: Number                   -- ^ Tile rotation (0-360)
  , blendOriginal :: Number              -- ^ Original blend (0-100)
  , mirrorEdges :: Boolean               -- ^ Mirror at edges
  }

-- | Default Tiler.
defaultTiler :: TilerEffect
defaultTiler =
  { scale: 100.0
  , offset: point2D 0.0 0.0
  , rotation: 0.0
  , blendOriginal: 0.0
  , mirrorEdges: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // serialization
-- ═════════════════════════════════════════════════════════════════════════════

splitDirectionToString :: SplitDirection -> String
splitDirectionToString = show
