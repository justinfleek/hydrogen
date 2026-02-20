-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // hydrogen // icon
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Base icon component and utilities
-- |
-- | This module provides the foundation for rendering SVG icons:
-- | - IconProps for consistent icon configuration
-- | - Helper functions for creating icon components
-- | - Size and color utilities
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Icon.Icon as Icon
-- | import Hydrogen.Icon.Lucide as Lucide
-- |
-- | -- Render an icon with default size
-- | Lucide.check []
-- |
-- | -- With custom size
-- | Lucide.check [ Icon.size Icon.Lg ]
-- |
-- | -- With custom class
-- | Lucide.check [ Icon.className "text-primary" ]
-- | ```
module Hydrogen.Icon.Icon
  ( -- * Icon Props
    IconProps
  , IconProp
  , defaultProps
    -- * Prop Builders
  , size
  , className
  , strokeWidth
  , ariaLabel
  , ariaHidden
    -- * Icon Sizes
  , IconSize(..)
  , iconSizeClass
  , iconSizePx
    -- * Icon Rendering
  , icon
  , iconWith
  , svgIcon
    -- * SVG Helpers
  , svgElement
  , pathElement
  , circleElement
  , rectElement
  , lineElement
  , polylineElement
  , polygonElement
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (svgNS, svgCls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // icon props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Icon properties
type IconProps =
  { size :: IconSize
  , className :: String
  , strokeWidth :: Number
  , ariaLabel :: Maybe String
  , ariaHidden :: Boolean
  }

-- | Icon property modifier
type IconProp = IconProps -> IconProps

-- | Default icon properties
defaultProps :: IconProps
defaultProps =
  { size: Md
  , className: ""
  , strokeWidth: 2.0
  , ariaLabel: Nothing
  , ariaHidden: true
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set icon size
size :: IconSize -> IconProp
size s props = props { size = s }

-- | Add custom class
className :: String -> IconProp
className cls props = props { className = props.className <> " " <> cls }

-- | Set stroke width
strokeWidth :: Number -> IconProp
strokeWidth w props = props { strokeWidth = w }

-- | Set aria-label (makes icon accessible)
ariaLabel :: String -> IconProp
ariaLabel label props = props { ariaLabel = Just label, ariaHidden = false }

-- | Set aria-hidden
ariaHidden :: Boolean -> IconProp
ariaHidden hidden props = props { ariaHidden = hidden }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // icon sizes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Standard icon sizes
data IconSize
  = Xs    -- 12px
  | Sm    -- 16px
  | Md    -- 20px
  | Lg    -- 24px
  | Xl    -- 32px
  | Xxl   -- 40px
  | Custom String  -- Custom Tailwind class

derive instance eqIconSize :: Eq IconSize

-- | Get Tailwind size class for icon
iconSizeClass :: IconSize -> String
iconSizeClass = case _ of
  Xs -> "w-3 h-3"
  Sm -> "w-4 h-4"
  Md -> "w-5 h-5"
  Lg -> "w-6 h-6"
  Xl -> "w-8 h-8"
  Xxl -> "w-10 h-10"
  Custom cls -> cls

-- | Get size in pixels
iconSizePx :: IconSize -> Int
iconSizePx = case _ of
  Xs -> 12
  Sm -> 16
  Md -> 20
  Lg -> 24
  Xl -> 32
  Xxl -> 40
  Custom _ -> 24  -- Default fallback

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // icon rendering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an icon from SVG path data
-- |
-- | ```purescript
-- | checkIcon :: forall w i. Array IconProp -> HH.HTML w i
-- | checkIcon props = icon props "M20 6L9 17l-5-5"
-- | ```
icon :: forall w i. Array IconProp -> String -> HH.HTML w i
icon propMods pathData =
  iconWith propMods [ pathElement pathData ]

-- | Create an icon from multiple SVG children
iconWith :: forall w i. Array IconProp -> Array (HH.HTML w i) -> HH.HTML w i
iconWith propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in svgIcon props children

-- | Render an SVG icon with props
svgIcon :: forall w i. IconProps -> Array (HH.HTML w i) -> HH.HTML w i
svgIcon props children =
  HH.elementNS svgNS (HH.ElemName "svg")
    [ svgCls [ iconSizeClass props.size, props.className ]
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") (show props.strokeWidth)
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    , HP.attr (HH.AttrName "aria-hidden") (if props.ariaHidden then "true" else "false")
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // svg helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an SVG element
svgElement :: forall w i. String -> Array (HH.IProp () i) -> Array (HH.HTML w i) -> HH.HTML w i
svgElement name props = HH.elementNS svgNS (HH.ElemName name) props

-- | Create a path element
pathElement :: forall w i. String -> HH.HTML w i
pathElement d = svgElement "path" [ HP.attr (HH.AttrName "d") d ] []

-- | Create a circle element
circleElement :: forall w i. Number -> Number -> Number -> HH.HTML w i
circleElement cx cy r = svgElement "circle"
  [ HP.attr (HH.AttrName "cx") (show cx)
  , HP.attr (HH.AttrName "cy") (show cy)
  , HP.attr (HH.AttrName "r") (show r)
  ]
  []

-- | Create a rect element
rectElement :: forall w i. 
  { x :: Number, y :: Number, width :: Number, height :: Number, rx :: Maybe Number } -> 
  HH.HTML w i
rectElement r = svgElement "rect"
  ( [ HP.attr (HH.AttrName "x") (show r.x)
    , HP.attr (HH.AttrName "y") (show r.y)
    , HP.attr (HH.AttrName "width") (show r.width)
    , HP.attr (HH.AttrName "height") (show r.height)
    ] <> case r.rx of
      Just rx -> [ HP.attr (HH.AttrName "rx") (show rx) ]
      Nothing -> []
  )
  []

-- | Create a line element
lineElement :: forall w i. Number -> Number -> Number -> Number -> HH.HTML w i
lineElement x1 y1 x2 y2 = svgElement "line"
  [ HP.attr (HH.AttrName "x1") (show x1)
  , HP.attr (HH.AttrName "y1") (show y1)
  , HP.attr (HH.AttrName "x2") (show x2)
  , HP.attr (HH.AttrName "y2") (show y2)
  ]
  []

-- | Create a polyline element
polylineElement :: forall w i. String -> HH.HTML w i
polylineElement points = svgElement "polyline"
  [ HP.attr (HH.AttrName "points") points ]
  []

-- | Create a polygon element
polygonElement :: forall w i. String -> HH.HTML w i
polygonElement points = svgElement "polygon"
  [ HP.attr (HH.AttrName "points") points ]
  []
