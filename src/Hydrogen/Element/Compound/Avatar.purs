-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // avatar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Avatar — Pure Element avatar component.
-- |
-- | ## Design Philosophy
-- |
-- | This component emits **pure Element data**, not HTML/CSS.
-- | No strings. No CSS properties. Just bounded Schema atoms
-- | composed into Element shapes.
-- |
-- | An avatar is fundamentally:
-- | - An Ellipse (circle) with a solid fill for background
-- | - A Text element centered inside (for fallback initials)
-- | - Or an Image element (for user photo)
-- |
-- | ## Schema Atoms Used
-- |
-- | | Property            | Pillar     | Type                      |
-- | |---------------------|------------|---------------------------|
-- | | size                | Dimension  | Pixel                     |
-- | | backgroundColor     | Color      | RGB                       |
-- | | textColor           | Color      | RGB                       |
-- | | borderColor         | Color      | RGB                       |
-- | | borderWidth         | Dimension  | Pixel                     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Avatar as Avatar
-- |
-- | -- Simple avatar with initials
-- | Avatar.avatar
-- |   [ Avatar.size 40.0
-- |   , Avatar.backgroundColor (Color.rgb 226 232 240)
-- |   ]
-- |   "JD"
-- |
-- | -- Avatar with image
-- | Avatar.avatarImage
-- |   [ Avatar.size 40.0 ]
-- |   "/user.jpg"
-- | ```

module Hydrogen.Element.Compound.Avatar
  ( -- * Main Component
    avatar
  
  -- * Image Avatar
  , avatarImage
  
  -- * Props
  , AvatarProps
  , AvatarProp
  , defaultProps
  
  -- * Prop Builders
  , size
  , backgroundColor
  , textColor
  , borderColor
  , borderWidth
  ) where

import Prelude
  ( ($)
  , (/)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)

import Hydrogen.Element.Core (Element, ellipse, image, group)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Color.Opacity (Opacity, opacity)
import Hydrogen.Schema.Dimension.Device.Types (Pixel(Pixel))
import Hydrogen.Schema.Dimension.ObjectFit (ObjectFit(Cover))
import Hydrogen.Schema.Geometry.Shape (EllipseShape, ellipseShape, RectangleShape, rectangleShape)
import Hydrogen.Schema.Geometry.Shape.Types (PixelPoint2D, pixelPoint2D)
import Hydrogen.Schema.Geometry.Radius (cornersAll, px)
import Hydrogen.Schema.Surface.Fill (Fill, fillSolid)
import Hydrogen.Element.Core.Media (ImageSource(ImageUrl))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Avatar properties — pure bounded data, no CSS.
type AvatarProps =
  { size :: Maybe Pixel            -- ^ Circle diameter in pixels
  , backgroundColor :: Maybe RGB   -- ^ Fill color for fallback
  , textColor :: Maybe RGB         -- ^ Text color for initials (reserved)
  , borderColor :: Maybe RGB       -- ^ Stroke color
  , borderWidth :: Maybe Pixel     -- ^ Stroke width
  }

-- | Property modifier
type AvatarProp = AvatarProps -> AvatarProps

-- | Default properties
defaultProps :: AvatarProps
defaultProps =
  { size: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , borderWidth: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set avatar size (diameter in pixels)
size :: Number -> AvatarProp
size s props = props { size = Just (Pixel s) }

-- | Set fallback background color
backgroundColor :: RGB -> AvatarProp
backgroundColor c props = props { backgroundColor = Just c }

-- | Set fallback text color (for initials)
textColor :: RGB -> AvatarProp
textColor c props = props { textColor = Just c }

-- | Set border color
borderColor :: RGB -> AvatarProp
borderColor c props = props { borderColor = Just c }

-- | Set border width
borderWidth :: Number -> AvatarProp
borderWidth w props = props { borderWidth = Just (Pixel w) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an avatar as a pure Element (circle with fill).
-- |
-- | This emits an Ellipse element — no CSS, no HTML, just pure data
-- | that can be rendered to any target (WebGPU, Canvas, SVG, etc).
-- |
-- | For text initials, the caller should compose with a Text element.
-- | This function provides the circular background.
avatar :: Array AvatarProp -> Element
avatar propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Defaults
    defaultSize = Pixel 40.0
    defaultBg = rgb 226 232 240  -- Light gray
    
    -- Resolved values
    (Pixel diameterN) = fromMaybe defaultSize props.size
    radius = Pixel (diameterN / 2.0)
    bgColor = fromMaybe defaultBg props.backgroundColor
    
    -- Center point (avatar is positioned at origin, caller can transform)
    center = pixelPoint2D radius radius
    
    -- Build ellipse shape (circle when radiusX == radiusY)
    shape = ellipseShape center radius radius
    
    -- Build fill from background color
    fill = fillSolid bgColor
  in
    ellipse
      { shape: shape
      , fill: fill
      , stroke: Nothing  -- TODO: add stroke from borderColor/borderWidth
      , opacity: opacity 100
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // image avatar
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an avatar with an image.
-- |
-- | Emits an Image element with the specified URL.
-- | The image is not automatically clipped to a circle — that's handled
-- | by the rendering target or by compositing with a clip mask.
avatarImage :: Array AvatarProp -> String -> Element
avatarImage propMods url =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Defaults
    defaultSize = Pixel 40.0
    diameter = fromMaybe defaultSize props.size
    
    -- Image source
    source = ImageUrl url
    
    -- Image bounds (square centered at origin)
    bounds :: RectangleShape
    bounds = rectangleShape
      (pixelPoint2D (Pixel 0.0) (Pixel 0.0))
      diameter
      diameter
      (cornersAll (px 0.0))
  in
    image
      { source: source
      , bounds: bounds
      , fit: Cover
      , opacity: opacity 100
      }
