-- | Core UI utilities and primitives
-- |
-- | This module provides foundational UI utilities:
-- | - Class name handling
-- | - Layout primitives (flex, grid)
-- | - Common patterns for Tailwind CSS
module Hydrogen.UI.Core
  ( -- * Class utilities
    classes
  , cls
  , svgCls
    -- * Layout
  , flex
  , row
  , column
  , box
  , container
  , section
    -- * SVG namespace
  , svgNS
  ) where

import Prelude

import Data.Array (filter, intercalate)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- ============================================================
-- CLASS UTILITIES
-- ============================================================

-- | Combine class names, filtering empty strings
-- |
-- | ```purescript
-- | classes ["foo", "", "bar"] == "foo bar"
-- | classes [] == ""
-- | ```
classes :: Array String -> String
classes = intercalate " " <<< filter (_ /= "")

-- | Create HP.class_ from array of class strings
-- |
-- | NOTE: This uses the DOM property `className` which does NOT work on SVG elements.
-- | For SVG elements, use `svgCls` instead.
-- |
-- | ```purescript
-- | HH.div [ cls ["container", "mx-auto"] ] [ ... ]
-- | ```
cls :: forall r i. Array String -> HH.IProp (class :: String | r) i
cls = HP.class_ <<< HH.ClassName <<< classes

-- | Create class attribute for SVG elements
-- |
-- | SVG elements have `className` as a read-only SVGAnimatedString, so we must
-- | use the `class` attribute instead of the `className` property.
-- |
-- | ```purescript
-- | HH.elementNS svgNS "svg" [ svgCls ["w-6", "h-6"] ] [ ... ]
-- | ```
svgCls :: forall r i. Array String -> HH.IProp r i
svgCls arr = HP.attr (HH.AttrName "class") (classes arr)

-- ============================================================
-- SVG NAMESPACE
-- ============================================================

-- | SVG namespace for creating SVG elements
svgNS :: HH.Namespace
svgNS = HH.Namespace "http://www.w3.org/2000/svg"

-- ============================================================
-- LAYOUT PRIMITIVES
-- ============================================================

-- | Configurable flex container
-- |
-- | ```purescript
-- | flex 
-- |   { direction: "column"
-- |   , gap: "gap-4"
-- |   , align: "center"
-- |   , justify: "between"
-- |   , className: "p-4"
-- |   }
-- |   [ child1, child2 ]
-- | ```
flex :: forall w i. 
  { direction :: String
  , gap :: String
  , align :: String
  , justify :: String
  , className :: String
  } -> 
  Array (HH.HTML w i) -> 
  HH.HTML w i
flex opts children =
  HH.div
    [ cls 
        [ "flex"
        , case opts.direction of
            "column" -> "flex-col"
            "col" -> "flex-col"
            _ -> "flex-row"
        , opts.gap
        , case opts.align of
            "center" -> "items-center"
            "end" -> "items-end"
            "stretch" -> "items-stretch"
            "baseline" -> "items-baseline"
            _ -> "items-start"
        , case opts.justify of
            "center" -> "justify-center"
            "end" -> "justify-end"
            "between" -> "justify-between"
            "around" -> "justify-around"
            "evenly" -> "justify-evenly"
            _ -> "justify-start"
        , opts.className
        ]
    ]
    children

-- | Simple flex row with gap
-- |
-- | ```purescript
-- | row "gap-4" [ item1, item2, item3 ]
-- | ```
row :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
row gap = flex { direction: "row", gap, align: "center", justify: "start", className: "" }

-- | Simple flex column with gap
-- |
-- | ```purescript
-- | column "gap-2" [ heading, paragraph, button ]
-- | ```
column :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
column gap = flex { direction: "column", gap, align: "start", justify: "start", className: "" }

-- | Generic box container with class name
-- |
-- | ```purescript
-- | box "p-4 bg-card rounded" [ content ]
-- | ```
box :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
box className = HH.div [ cls [ className ] ]

-- | Max-width centered container
-- |
-- | ```purescript
-- | container "py-8" [ pageContent ]
-- | ```
container :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
container className = HH.div [ cls [ "max-w-7xl mx-auto px-4 sm:px-6 lg:px-8", className ] ]

-- | Section wrapper
-- |
-- | ```purescript
-- | section "py-16 bg-muted" [ sectionContent ]
-- | ```
section :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
section className = HH.section [ cls [ className ] ]
