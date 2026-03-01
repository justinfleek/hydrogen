-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // effects // distortion // cc
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CC Effects — CyCore distortion effects from After Effects.
-- |
-- | ## Effects Included
-- |
-- | - **CC Bend It**: Bend layer around axis
-- | - **CC Blobbylize**: Organic blob distortion
-- | - **CC Flo Motion**: Flow-based motion blur
-- | - **CC Griddler**: Grid-based distortion
-- | - **CC Lens**: Lens distortion
-- | - **CC Page Turn**: Page turn effect
-- | - **CC Power Pin**: Advanced corner pin
-- | - **CC Ripple Pulse**: Expanding ripple
-- | - **CC Slant**: Perspective slant
-- | - **CC Smear**: Directional smear
-- | - **CC Split**: Split/duplicate effect
-- | - **CC Tiler**: Tiling effect

module Hydrogen.Schema.Motion.Effects.Distortion.CC
  ( -- * CC Bend It Effect
    CCBendItEffect
  , defaultCCBendIt
  
  -- * CC Blobbylize Effect
  , CCBlobbylizeEffect
  , defaultCCBlobbylize
  
  -- * CC Flo Motion Effect
  , CCFloMotionEffect
  , defaultCCFloMotion
  
  -- * CC Griddler Effect
  , CCGriddlerEffect
  , defaultCCGriddler
  
  -- * CC Lens Effect
  , CCLensEffect
  , defaultCCLens
  
  -- * CC Page Turn Effect
  , CCPageTurnEffect
  , defaultCCPageTurn
  
  -- * CC Power Pin Effect
  , CCPowerPinEffect
  , defaultCCPowerPin
  
  -- * CC Ripple Pulse Effect
  , CCRipplePulseEffect
  , defaultCCRipplePulse
  
  -- * CC Slant Effect
  , CCSlantEffect
  , defaultCCSlant
  
  -- * CC Smear Effect
  , CCSmearEffect
  , defaultCCSmear
  
  -- * CC Split Effect  
  , CCSplitEffect
  , CCSplitDirection(..)
  , defaultCCSplit
  
  -- * CC Tiler Effect
  , CCTilerEffect
  , defaultCCTiler
  
  -- * Serialization
  , ccSplitDirectionToString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  )

import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // cc // bend // it
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Bend It Effect — Bend layer around axis.
type CCBendItEffect =
  { start :: Point2D                     -- ^ Start point
  , finish :: Point2D                    -- ^ End point
  , bend :: Number                       -- ^ Bend amount (-100 to 100)
  , quality :: Int                       -- ^ Render quality (1-10)
  }

-- | Default CC Bend It.
defaultCCBendIt :: CCBendItEffect
defaultCCBendIt =
  { start: point2D 0.0 50.0
  , finish: point2D 100.0 50.0
  , bend: 0.0
  , quality: 5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // cc // blobbylize
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Blobbylize Effect — Organic blob distortion.
type CCBlobbylizeEffect =
  { softness :: Number                   -- ^ Blob softness (0-100)
  , cutAway :: Number                    -- ^ Cut away amount (0-100)
  , blobLayer :: Int                     -- ^ Control layer index
  , property :: Int                      -- ^ Property to use (0-3)
  }

-- | Default CC Blobbylize.
defaultCCBlobbylize :: CCBlobbylizeEffect
defaultCCBlobbylize =
  { softness: 50.0
  , cutAway: 50.0
  , blobLayer: 1
  , property: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // cc // flo // motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Flo Motion Effect — Flow-based motion blur.
type CCFloMotionEffect =
  { gradientLayer :: Int                 -- ^ Flow gradient layer
  , timeStep :: Number                   -- ^ Time step (0-100)
  , motionVectors :: Int                 -- ^ Vector count (1-32)
  , quality :: Int                       -- ^ Render quality (1-10)
  }

-- | Default CC Flo Motion.
defaultCCFloMotion :: CCFloMotionEffect
defaultCCFloMotion =
  { gradientLayer: 1
  , timeStep: 50.0
  , motionVectors: 8
  , quality: 5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // cc // griddler
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Griddler Effect — Grid-based distortion.
type CCGriddlerEffect =
  { horizontalScale :: Number            -- ^ Horizontal scale (0-200)
  , verticalScale :: Number              -- ^ Vertical scale (0-200)
  , rotation :: Number                   -- ^ Grid rotation (0-360)
  , rows :: Int                          -- ^ Grid rows (1-100)
  , columns :: Int                       -- ^ Grid columns (1-100)
  , offset :: Point2D                    -- ^ Grid offset
  }

-- | Default CC Griddler.
defaultCCGriddler :: CCGriddlerEffect
defaultCCGriddler =
  { horizontalScale: 100.0
  , verticalScale: 100.0
  , rotation: 0.0
  , rows: 10
  , columns: 10
  , offset: point2D 0.0 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cc // lens
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Lens Effect — Lens distortion.
type CCLensEffect =
  { center :: Point2D                    -- ^ Lens center
  , size :: Number                       -- ^ Lens size (0-1000)
  , convergence :: Number                -- ^ Convergence (-100 to 100)
  }

-- | Default CC Lens.
defaultCCLens :: CCLensEffect
defaultCCLens =
  { center: point2D 50.0 50.0
  , size: 100.0
  , convergence: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // cc // page // turn
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Page Turn Effect — Page turn effect.
type CCPageTurnEffect =
  { foldPosition :: Number               -- ^ Fold position (0-100)
  , foldRadius :: Number                 -- ^ Fold radius (0-200)
  , foldDirection :: Number              -- ^ Fold direction (0-360)
  , lightDirection :: Number             -- ^ Light angle (0-360)
  , lightIntensity :: Number             -- ^ Light strength (0-100)
  , backPageOpacity :: Number            -- ^ Back opacity (0-100)
  , backPageColor :: Boolean             -- ^ Use solid color for back
  }

-- | Default CC Page Turn.
defaultCCPageTurn :: CCPageTurnEffect
defaultCCPageTurn =
  { foldPosition: 50.0
  , foldRadius: 25.0
  , foldDirection: 0.0
  , lightDirection: 135.0
  , lightIntensity: 50.0
  , backPageOpacity: 100.0
  , backPageColor: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // cc // power // pin
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Power Pin Effect — Advanced corner pin.
type CCPowerPinEffect =
  { topLeft :: Point2D                   -- ^ Top-left corner
  , topRight :: Point2D                  -- ^ Top-right corner
  , bottomLeft :: Point2D                -- ^ Bottom-left corner
  , bottomRight :: Point2D               -- ^ Bottom-right corner
  , perspective :: Boolean               -- ^ Perspective mode
  , autoFocal :: Boolean                 -- ^ Auto focal length
  , focalLength :: Number                -- ^ Manual focal length
  }

-- | Default CC Power Pin.
defaultCCPowerPin :: CCPowerPinEffect
defaultCCPowerPin =
  { topLeft: point2D 0.0 0.0
  , topRight: point2D 100.0 0.0
  , bottomLeft: point2D 0.0 100.0
  , bottomRight: point2D 100.0 100.0
  , perspective: true
  , autoFocal: true
  , focalLength: 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // cc // ripple // pulse
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Ripple Pulse Effect — Expanding ripple.
type CCRipplePulseEffect =
  { center :: Point2D                    -- ^ Ripple center
  , radius :: Number                     -- ^ Ripple radius (0-2000)
  , amplitude :: Number                  -- ^ Wave height (0-200)
  , pulseLevel :: Number                 -- ^ Pulse intensity (0-100)
  , waveWidth :: Number                  -- ^ Wavelength (1-500)
  , phase :: Number                      -- ^ Phase offset (0-360)
  , waveSpeed :: Number                  -- ^ Animation speed
  }

-- | Default CC Ripple Pulse.
defaultCCRipplePulse :: CCRipplePulseEffect
defaultCCRipplePulse =
  { center: point2D 50.0 50.0
  , radius: 100.0
  , amplitude: 25.0
  , pulseLevel: 100.0
  , waveWidth: 50.0
  , phase: 0.0
  , waveSpeed: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cc // slant
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Slant Effect — Perspective slant.
type CCSlantEffect =
  { slant :: Number                      -- ^ Slant amount (-100 to 100)
  , floor :: Number                      -- ^ Floor position (0-100)
  , height :: Number                     -- ^ Height (0-200)
  , direction :: Number                  -- ^ Slant direction (0-360)
  }

-- | Default CC Slant.
defaultCCSlant :: CCSlantEffect
defaultCCSlant =
  { slant: 0.0
  , floor: 50.0
  , height: 100.0
  , direction: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cc // smear
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Smear Effect — Directional smear.
type CCSmearEffect =
  { sourcePoint :: Point2D               -- ^ Source position
  , destinationPoint :: Point2D          -- ^ Destination position
  , percentSource :: Number              -- ^ Source influence (0-100)
  , percentDestination :: Number         -- ^ Destination influence (0-100)
  }

-- | Default CC Smear.
defaultCCSmear :: CCSmearEffect
defaultCCSmear =
  { sourcePoint: point2D 25.0 50.0
  , destinationPoint: point2D 75.0 50.0
  , percentSource: 50.0
  , percentDestination: 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cc // split
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Split direction.
data CCSplitDirection
  = CSDHorizontal      -- ^ Horizontal split
  | CSDVertical        -- ^ Vertical split
  | CSDBoth            -- ^ Both directions

derive instance eqCCSplitDirection :: Eq CCSplitDirection
derive instance ordCCSplitDirection :: Ord CCSplitDirection

instance showCCSplitDirection :: Show CCSplitDirection where
  show CSDHorizontal = "horizontal"
  show CSDVertical = "vertical"
  show CSDBoth = "both"

-- | CC Split Effect — Split/duplicate effect.
type CCSplitEffect =
  { splitPoint :: Point2D                -- ^ Split position
  , direction :: CCSplitDirection        -- ^ Split direction
  , splitWidth :: Number                 -- ^ Split gap (0-500)
  }

-- | Default CC Split.
defaultCCSplit :: CCSplitEffect
defaultCCSplit =
  { splitPoint: point2D 50.0 50.0
  , direction: CSDHorizontal
  , splitWidth: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cc // tiler
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Tiler Effect — Tiling effect.
type CCTilerEffect =
  { scale :: Number                      -- ^ Tile scale (1-1000)
  , offset :: Point2D                    -- ^ Tile offset
  , rotation :: Number                   -- ^ Tile rotation (0-360)
  , blendOriginal :: Number              -- ^ Original blend (0-100)
  , mirrorEdges :: Boolean               -- ^ Mirror at edges
  }

-- | Default CC Tiler.
defaultCCTiler :: CCTilerEffect
defaultCCTiler =
  { scale: 100.0
  , offset: point2D 0.0 0.0
  , rotation: 0.0
  , blendOriginal: 0.0
  , mirrorEdges: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // serialization
-- ═════════════════════════════════════════════════════════════════════════════

ccSplitDirectionToString :: CCSplitDirection -> String
ccSplitDirectionToString = show
