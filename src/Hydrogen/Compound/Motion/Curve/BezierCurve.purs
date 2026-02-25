-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // component // motion // curve // beziercurve
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier Curve SVG Renderer
-- |
-- | A pure rendering component that draws a cubic bezier curve as an SVG path.
-- | Used as a building block for curve editors and easing previews.
-- |
-- | ## Features
-- |
-- | - Renders cubic bezier from control points
-- | - Configurable stroke width and color
-- | - Optional fill for area under curve
-- | - Smooth anti-aliased rendering
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Curve.BezierCurve as BezierCurve
-- |
-- | -- Inside an SVG element
-- | BezierCurve.render
-- |   { p1x: 0.42, p1y: 0.0
-- |   , p2x: 0.58, p2y: 1.0
-- |   , width: 200.0, height: 150.0
-- |   , padding: 16.0
-- |   , strokeWidth: 2.0
-- |   , strokeClass: "text-primary"
-- |   }
-- | ```
module Hydrogen.Component.Motion.Curve.BezierCurve
  ( -- * Rendering
    render
  , renderPath
  , renderWithFill
  
  -- * Types
  , Config
  , PathConfig
  
  -- * Utilities
  , toSvgPath
  , toControlPointsSvg
  ) where

import Prelude

import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Full render configuration
type Config =
  { p1x :: Number
  , p1y :: Number
  , p2x :: Number
  , p2y :: Number
  , width :: Number
  , height :: Number
  , padding :: Number
  , strokeWidth :: Number
  , strokeClass :: String
  }

-- | Path-only configuration (for use inside existing SVG)
type PathConfig =
  { p1x :: Number
  , p1y :: Number
  , p2x :: Number
  , p2y :: Number
  , width :: Number
  , height :: Number
  , padding :: Number
  }

-- | SVG coordinate point
type SvgPoint = { x :: Number, y :: Number }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // rendering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a bezier curve as an SVG path element
render :: forall w i. Config -> HH.HTML w i
render config =
  HH.element (HH.ElemName "path")
    [ HP.attr (HH.AttrName "d") (toSvgPath config)
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") (show config.strokeWidth)
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , cls [ config.strokeClass ]
    ]
    []

-- | Render just the path data (for composing with other elements)
renderPath :: forall w i. PathConfig -> Number -> String -> HH.HTML w i
renderPath config strokeWidth strokeClass =
  HH.element (HH.ElemName "path")
    [ HP.attr (HH.AttrName "d") (toSvgPathFromConfig config)
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") (show strokeWidth)
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , cls [ strokeClass ]
    ]
    []

-- | Render curve with filled area underneath
renderWithFill :: forall w i. Config -> String -> HH.HTML w i
renderWithFill config fillClass =
  let
    pathD = toSvgPath config
    -- Close the path to create a filled shape
    closedPathD = toSvgPathClosed config
  in
    HH.element (HH.ElemName "g")
      []
      [ -- Filled area
        HH.element (HH.ElemName "path")
          [ HP.attr (HH.AttrName "d") closedPathD
          , HP.attr (HH.AttrName "fill") "currentColor"
          , HP.attr (HH.AttrName "fill-opacity") "0.1"
          , HP.attr (HH.AttrName "stroke") "none"
          , cls [ fillClass ]
          ]
          []
      -- Curve stroke
      , HH.element (HH.ElemName "path")
          [ HP.attr (HH.AttrName "d") pathD
          , HP.attr (HH.AttrName "fill") "none"
          , HP.attr (HH.AttrName "stroke") "currentColor"
          , HP.attr (HH.AttrName "stroke-width") (show config.strokeWidth)
          , HP.attr (HH.AttrName "stroke-linecap") "round"
          , cls [ config.strokeClass ]
          ]
          []
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert config to SVG path data string
toSvgPath :: Config -> String
toSvgPath config = toSvgPathFromConfig
  { p1x: config.p1x
  , p1y: config.p1y
  , p2x: config.p2x
  , p2y: config.p2y
  , width: config.width
  , height: config.height
  , padding: config.padding
  }

-- | Convert PathConfig to SVG path data string
toSvgPathFromConfig :: PathConfig -> String
toSvgPathFromConfig config =
  let
    coords = toControlPointsSvg config
  in
    "M " <> show coords.start.x <> " " <> show coords.start.y <>
    " C " <> show coords.cp1.x <> " " <> show coords.cp1.y <>
    " " <> show coords.cp2.x <> " " <> show coords.cp2.y <>
    " " <> show coords.end.x <> " " <> show coords.end.y

-- | Create closed path for fill (includes baseline)
toSvgPathClosed :: Config -> String
toSvgPathClosed config =
  let
    coords = toControlPointsSvg
      { p1x: config.p1x
      , p1y: config.p1y
      , p2x: config.p2x
      , p2y: config.p2y
      , width: config.width
      , height: config.height
      , padding: config.padding
      }
    baseline = config.height - config.padding
  in
    "M " <> show coords.start.x <> " " <> show coords.start.y <>
    " C " <> show coords.cp1.x <> " " <> show coords.cp1.y <>
    " " <> show coords.cp2.x <> " " <> show coords.cp2.y <>
    " " <> show coords.end.x <> " " <> show coords.end.y <>
    " L " <> show coords.end.x <> " " <> show baseline <>
    " L " <> show coords.start.x <> " " <> show baseline <>
    " Z"

-- | Convert normalized control points to SVG coordinates
toControlPointsSvg :: PathConfig -> 
  { start :: SvgPoint
  , cp1 :: SvgPoint
  , cp2 :: SvgPoint
  , end :: SvgPoint
  }
toControlPointsSvg config =
  let
    w = config.width
    h = config.height
    p = config.padding
    innerW = w - 2.0 * p
    innerH = h - 2.0 * p
    
    -- Convert normalized (0-1) to SVG coords
    -- Y is inverted: 0 at bottom, 1 at top
    toSvgX x = p + x * innerW
    toSvgY y = h - p - y * innerH
  in
    { start: { x: toSvgX 0.0, y: toSvgY 0.0 }
    , cp1: { x: toSvgX config.p1x, y: toSvgY config.p1y }
    , cp2: { x: toSvgX config.p2x, y: toSvgY config.p2y }
    , end: { x: toSvgX 1.0, y: toSvgY 1.0 }
    }
