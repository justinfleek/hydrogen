-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // gpu // draw // params
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DrawCommand.Params — Parameter Constructor Functions
-- |
-- | This module provides smart constructors for all v1 draw command parameters.
-- | These constructors accept raw values and convert to bounded types,
-- | providing backward compatibility with existing code.
-- |
-- | For v2 typography parameters, see DrawCommand.Typography.

module Hydrogen.GPU.DrawCommand.Params
  ( -- * Rect Parameters
    rectParams
  
  -- * Image Parameters
  , imageParams
  
  -- * Video Parameters
  , videoParams
  
  -- * 3D Model Parameters
  , model3DParams
  
  -- * Quad Parameters
  , quadParams
  
  -- * Glyph Parameters
  , glyphParams
  
  -- * Path Parameters
  , pathParams
  
  -- * Particle Parameters
  , particleParams
  ) where

import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.GPU.Coordinates as Coord
import Hydrogen.GPU.DrawCommand.Types
  ( Point2D
  , RectParams
  , ImageParams
  , VideoParams
  , Model3DParams
  , QuadParams
  , GlyphParams
  , PathParams
  , PathSegment
  , ParticleParams
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // rect parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create rectangle parameters with defaults.
-- |
-- | Accepts Device.Pixel for backward compatibility, internally converts
-- | to bounded coordinate types. Depth defaults to near plane (0.0).
rectParams
  :: forall msg
   . Device.Pixel       -- x
  -> Device.Pixel       -- y
  -> Device.Pixel       -- width
  -> Device.Pixel       -- height
  -> RGB.RGBA           -- fill
  -> RectParams msg
rectParams x y w h fill =
  { x: Coord.screenXFromPixel x
  , y: Coord.screenYFromPixel y
  , width: Coord.pixelWidthFromPixel w
  , height: Coord.pixelHeightFromPixel h
  , fill
  , cornerRadius: Radius.cornersAll Radius.none
  , depth: Coord.depthValueNear
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // image parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create image parameters.
-- |
-- | Accepts raw Numbers for backward compatibility, internally clamps
-- | to bounded coordinate types.
imageParams
  :: forall msg
   . String            -- url
  -> Number            -- x
  -> Number            -- y
  -> Number            -- width
  -> Number            -- height
  -> ImageParams msg
imageParams url x y w h =
  { url
  , x: Coord.screenX x
  , y: Coord.screenY y
  , width: Coord.pixelWidth w
  , height: Coord.pixelHeight h
  , depth: Coord.depthValueNear
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // video parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create video parameters.
-- |
-- | Accepts raw Numbers for backward compatibility, internally clamps
-- | to bounded coordinate types.
videoParams
  :: forall msg
   . String            -- url
  -> Number            -- x
  -> Number            -- y
  -> Number            -- width
  -> Number            -- height
  -> VideoParams msg
videoParams url x y w h =
  { url
  , x: Coord.screenX x
  , y: Coord.screenY y
  , width: Coord.pixelWidth w
  , height: Coord.pixelHeight h
  , currentTime: Coord.normalizedX 0.0
  , playing: false
  , depth: Coord.depthValueNear
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // model3d parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create 3D model parameters.
-- |
-- | Accepts raw Numbers for backward compatibility, internally clamps
-- | to bounded coordinate types.
model3DParams
  :: forall msg
   . String            -- url
  -> Number            -- x
  -> Number            -- y
  -> Number            -- width
  -> Number            -- height
  -> Model3DParams msg
model3DParams url x y w h =
  { url
  , x: Coord.screenX x
  , y: Coord.screenY y
  , width: Coord.pixelWidth w
  , height: Coord.pixelHeight h
  , cameraDistance: 5.0
  , cameraAzimuth: 0.0
  , cameraElevation: 0.0
  , cameraFov: 45.0
  , animationProgress: Coord.normalizedX 0.0
  , depth: Coord.depthValueNear
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // quad parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create quad parameters.
quadParams
  :: forall msg
   . Point2D -> Point2D -> Point2D -> Point2D
  -> RGB.RGBA
  -> QuadParams msg
quadParams v0 v1 v2 v3 fill =
  { v0, v1, v2, v3
  , fill
  , depth: Coord.depthValueNear
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // glyph parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create glyph parameters.
-- |
-- | Accepts Device.Pixel for backward compatibility, internally converts
-- | to bounded coordinate types.
glyphParams
  :: forall msg
   . Device.Pixel       -- x
  -> Device.Pixel       -- y
  -> Int                -- glyphIndex
  -> Int                -- fontId
  -> Device.Pixel       -- fontSize
  -> RGB.RGBA           -- color
  -> GlyphParams msg
glyphParams x y glyphIndex fontId fontSize color =
  { x: Coord.screenXFromPixel x
  , y: Coord.screenYFromPixel y
  , glyphIndex
  , fontId
  , fontSize
  , color
  , depth: Coord.depthValueNear
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // path parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create path parameters.
pathParams
  :: forall msg
   . Array PathSegment
  -> PathParams msg
pathParams segments =
  { segments
  , fill: Nothing
  , stroke: Nothing
  , strokeWidth: Device.px 1.0
  , depth: Coord.depthValueNear
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // particle parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create particle parameters.
-- |
-- | Accepts Device.Pixel for backward compatibility, internally converts
-- | to bounded coordinate types.
particleParams
  :: forall msg
   . Device.Pixel       -- x
  -> Device.Pixel       -- y
  -> Device.Pixel       -- size
  -> RGB.RGBA           -- color
  -> ParticleParams msg
particleParams x y size color =
  { x: Coord.screenXFromPixel x
  , y: Coord.screenYFromPixel y
  , z: Coord.depthValueNear
  , size
  , color
  , pickId: Nothing
  , onClick: Nothing
  }
