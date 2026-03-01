-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // style // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Style Types and Builders
-- |
-- | This module provides the foundational types for Hydrogen's type-safe CSS:
-- | - `Style` — A composable collection of CSS properties (monoid)
-- | - `Property` — A single CSS name/value pair
-- | - `CSSValue` — Typed representation of CSS values (px, em, %, etc.)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Style.Core as S
-- |
-- | myStyle :: S.Style
-- | myStyle = S.styles
-- |   [ S.prop "background-color" "blue"
-- |   , S.prop "padding" "16px"
-- |   ]
-- |
-- | S.render myStyle
-- | -- "background-color: blue; padding: 16px"
-- | ```

module Hydrogen.Render.Style.Core
  ( -- * Core Types
    Style
  , Property
  
  -- * Building Styles
  , styles
  , prop
  , render
  , toTuples
  
  -- * CSS Values
  , CSSValue
    ( Px
    , Pct
    , Em
    , Rem
    , Vh
    , Vw
    , Auto
    , None
    , Inherit
    , Initial
    , Unset
    , Raw
    )
  , cssValueToString
  , px
  , pct
  , em
  , rem
  , vh
  , vw
  , auto
  , none
  , inherit
  , initial
  , unset
  ) where

import Prelude
  ( class Monoid
  , class Semigroup
  , map
  , show
  , (<>)
  )

import Data.Array (intercalate)
import Data.Foldable (foldl) as Foldable

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A CSS style — a collection of CSS properties
-- |
-- | Styles are monoids: you can combine them with `<>` and they merge.
-- | Later properties override earlier ones for the same key.
newtype Style = Style (Array Property)

-- | A single CSS property — name and value
type Property =
  { name :: String
  , value :: String
  }

instance semigroupStyle :: Semigroup Style where
  append (Style a) (Style b) = Style (a <> b)

instance monoidStyle :: Monoid Style where
  mempty = Style []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // css value
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS value — typed representation of CSS property values
data CSSValue
  = Px Number
  | Pct Number
  | Em Number
  | Rem Number
  | Vh Number
  | Vw Number
  | Auto
  | None
  | Inherit
  | Initial
  | Unset
  | Raw String

-- | Convert a CSSValue to its string representation
cssValueToString :: CSSValue -> String
cssValueToString = case _ of
  Px n -> show n <> "px"
  Pct n -> show n <> "%"
  Em n -> show n <> "em"
  Rem n -> show n <> "rem"
  Vh n -> show n <> "vh"
  Vw n -> show n <> "vw"
  Auto -> "auto"
  None -> "none"
  Inherit -> "inherit"
  Initial -> "initial"
  Unset -> "unset"
  Raw s -> s

-- | Create pixel value
px :: Number -> CSSValue
px = Px

-- | Create percentage value
pct :: Number -> CSSValue
pct = Pct

-- | Create em value
em :: Number -> CSSValue
em = Em

-- | Create rem value
rem :: Number -> CSSValue
rem = Rem

-- | Create viewport height value
vh :: Number -> CSSValue
vh = Vh

-- | Create viewport width value
vw :: Number -> CSSValue
vw = Vw

-- | Auto value
auto :: CSSValue
auto = Auto

-- | None value
none :: CSSValue
none = None

-- | Inherit value
inherit :: CSSValue
inherit = Inherit

-- | Initial value
initial :: CSSValue
initial = Initial

-- | Unset value
unset :: CSSValue
unset = Unset

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // style builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a style from an array of styles (flattens them)
styles :: Array Style -> Style
styles arr = Style (flattenStyles arr)
  where
  flattenStyles :: Array Style -> Array Property
  flattenStyles = map (\(Style props) -> props) >>> intercalateArrays

  intercalateArrays :: Array (Array Property) -> Array Property
  intercalateArrays = foldlArray (\acc xs -> acc <> xs) []

-- | Create a single property
prop :: String -> String -> Style
prop name value = Style [{ name, value }]

-- | Render a style to an inline style string
-- |
-- | ```purescript
-- | S.render (S.prop "padding" "16px" <> S.prop "margin" "8px")
-- | -- "padding: 16px; margin: 8px"
-- | ```
render :: Style -> String
render (Style props) = intercalate "; " (map propToString props)
  where
  propToString :: Property -> String
  propToString p = p.name <> ": " <> p.value

-- | Get properties as array of (name, value) pairs
-- |
-- | Useful for integration with Element.styles
toTuples :: Style -> Array { name :: String, value :: String }
toTuples (Style props) = props

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Function composition (left-to-right)
infixr 9 composeFlipped as >>>

composeFlipped :: forall a b c. (a -> b) -> (b -> c) -> (a -> c)
composeFlipped f g x = g (f x)

-- | foldl for Array using Data.Foldable.foldl
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray = Foldable.foldl
