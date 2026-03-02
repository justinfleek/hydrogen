-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // element // compound // canvas // grid // style
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Grid Styles — Extended grid style types and vanishing points.
-- |
-- | ## Grid Style Families
-- |
-- | - **Basic**: Square, Dot, Crosshair
-- | - **Isometric**: 30°, 45°, custom angle
-- | - **Perspective**: 1/2/3-point perspective
-- | - **Radial**: Polar, Hexagonal
-- | - **Composition**: Golden ratio, Rule of thirds, Diagonal
-- |
-- | ## Dependencies
-- |
-- | - Prelude (basic operations)
-- | - Schema.Geometry.Angle (Degrees)
-- | - Data.Maybe (Maybe)

module Hydrogen.Element.Compound.Canvas.Grid.Style
  ( -- * Extended Grid Styles
    ExtendedGridStyle(StyleSquare, StyleDot, StyleCrosshair, StyleIsometric, StyleIsometric30, StyleIsometric45, StylePerspective1, StylePerspective2, StylePerspective3, StylePolar, StyleHexagonal, StyleGoldenRatio, StyleRuleOfThirds, StyleDiagonal)
  , gridStyleAngle
  , isIsometricFamily
  , isPerspectiveFamily
  , isRadialFamily
  
  -- * Vanishing Points
  , VanishingPoint(VanishingPoint)
  , vanishingPoint
  , vpPosition
  , vpHorizonY
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // vanishing point
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vanishing point for perspective grids.
-- |
-- | Position is in canvas coordinates.
-- | HorizonY is the y-coordinate of the horizon line.
newtype VanishingPoint = VanishingPoint 
  { x :: Number
  , y :: Number
  , horizonY :: Number
  }

derive instance eqVanishingPoint :: Eq VanishingPoint

instance showVanishingPoint :: Show VanishingPoint where
  show (VanishingPoint vp) = "VP(" <> show vp.x <> "," <> show vp.y <> ")"

-- | Create a vanishing point.
vanishingPoint :: Number -> Number -> Number -> VanishingPoint
vanishingPoint x y horizonY = VanishingPoint { x, y, horizonY }

-- | Get vanishing point position.
vpPosition :: VanishingPoint -> { x :: Number, y :: Number }
vpPosition (VanishingPoint vp) = { x: vp.x, y: vp.y }

-- | Get horizon Y coordinate.
vpHorizonY :: VanishingPoint -> Number
vpHorizonY (VanishingPoint vp) = vp.horizonY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // extended grid styles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extended grid styles beyond the basic Types.GridStyle.
-- |
-- | Includes all professional grid types with their specific parameters.
data ExtendedGridStyle
  -- Basic grids
  = StyleSquare                                    -- ^ Standard rectangular grid
  | StyleDot                                       -- ^ Dots at intersections only
  | StyleCrosshair                                 -- ^ Small + at intersections
  
  -- Isometric family (bounded angle: 0° to 90°)
  | StyleIsometric Degrees                         -- ^ Isometric with custom angle
  | StyleIsometric30                               -- ^ Classic 30° isometric
  | StyleIsometric45                               -- ^ 45° dimetric
  
  -- Perspective family (bounded: 1-3 vanishing points)
  | StylePerspective1 VanishingPoint               -- ^ 1-point perspective
  | StylePerspective2 VanishingPoint VanishingPoint -- ^ 2-point perspective
  | StylePerspective3 VanishingPoint VanishingPoint VanishingPoint -- ^ 3-point
  
  -- Radial family (bounded divisions: 2 to 360)
  | StylePolar Int                                 -- ^ Radial with n divisions
  | StyleHexagonal                                 -- ^ Hexagonal honeycomb
  
  -- Composition grids
  | StyleGoldenRatio                               -- ^ Golden ratio (φ) divisions
  | StyleRuleOfThirds                              -- ^ 3×3 grid
  | StyleDiagonal                                  -- ^ Diagonal guidelines

derive instance eqExtendedGridStyle :: Eq ExtendedGridStyle

instance showExtendedGridStyle :: Show ExtendedGridStyle where
  show StyleSquare = "square"
  show StyleDot = "dot"
  show StyleCrosshair = "crosshair"
  show (StyleIsometric angle) = "isometric(" <> show angle <> ")"
  show StyleIsometric30 = "isometric-30"
  show StyleIsometric45 = "isometric-45"
  show (StylePerspective1 _) = "perspective-1pt"
  show (StylePerspective2 _ _) = "perspective-2pt"
  show (StylePerspective3 _ _ _) = "perspective-3pt"
  show (StylePolar n) = "polar(" <> show n <> ")"
  show StyleHexagonal = "hexagonal"
  show StyleGoldenRatio = "golden-ratio"
  show StyleRuleOfThirds = "rule-of-thirds"
  show StyleDiagonal = "diagonal"

-- | Get the angle associated with a grid style (for isometric family).
gridStyleAngle :: ExtendedGridStyle -> Maybe Degrees
gridStyleAngle (StyleIsometric angle) = Just angle
gridStyleAngle StyleIsometric30 = Just (degrees 30.0)
gridStyleAngle StyleIsometric45 = Just (degrees 45.0)
gridStyleAngle _ = Nothing

-- | Check if style is in the isometric family.
isIsometricFamily :: ExtendedGridStyle -> Boolean
isIsometricFamily (StyleIsometric _) = true
isIsometricFamily StyleIsometric30 = true
isIsometricFamily StyleIsometric45 = true
isIsometricFamily _ = false

-- | Check if style is in the perspective family.
isPerspectiveFamily :: ExtendedGridStyle -> Boolean
isPerspectiveFamily (StylePerspective1 _) = true
isPerspectiveFamily (StylePerspective2 _ _) = true
isPerspectiveFamily (StylePerspective3 _ _ _) = true
isPerspectiveFamily _ = false

-- | Check if style is in the radial family.
isRadialFamily :: ExtendedGridStyle -> Boolean
isRadialFamily (StylePolar _) = true
isRadialFamily StyleHexagonal = true
isRadialFamily _ = false
