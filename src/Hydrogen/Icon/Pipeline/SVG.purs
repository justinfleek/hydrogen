-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // icon // pipeline // svg
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Icon SVG Rendering — Convert IconDefinition to SVG markup.
-- |
-- | This module provides functions to render icons as SVG elements,
-- | suitable for:
-- |
-- | - Direct SVG output for web/email/print
-- | - Integration with DOM renderers
-- | - Export to design tools (Figma, Sketch)
-- |
-- | ## Usage
-- |
-- | ```
-- | svgElement ::forall msg. IconDefinition -> IconProps -> SvgElement msg
-- | svgElement icon props = renderAsSvg icon props
-- | ```
-- |
-- | ## Output Formats
-- |
-- | - Inline SVG: Full SVG with viewBox, xmlns
-- | - Path only: Just the `<path d="..."/>` element
-- | - Symbol: Reusable `<symbol>` definition

module Hydrogen.Icon.Pipeline.SVG
  ( -- * SVG Rendering
    renderAsSvg
  , renderAsPath
  , renderAsSymbol
  , renderAsInline
  , renderThemedSvg
  
  -- * SVG Element Construction
  , SvgElement
      ( SvgElement
      )
  , SvgAttributes
  , SvgAttribute
      ( SvgAttribute
      )
  , svgElement
  , pathElement
  , symbolElement
  
  -- * SVG Attributes
  , SvgFill
      ( SvgFillNone
      , SvgFillCurrentColor
      , SvgFillColor
      , SvgFillUrl
      )
  , SvgStroke
      ( SvgStrokeNone
      , SvgStrokeCurrentColor
      , SvgStrokeColor
      )
  , defaultSvgAttributes
  , fillToString
  , strokeToString
  , svgAttr
  
  -- * ViewBox Helpers
  , viewBoxValue
  , defaultSvgViewBox
  , viewBox24x24
  , viewBox16x16
  
  -- * Size Helpers
  , sizeValue
  , sizeValueByName
  , sizeAsPixels
  , sizeXs
  , sizeSm
  , sizeMd
  , sizeLg
  , sizeXl
  , sizeXxl
  
  -- * Icon Helpers
  , iconNameString
  , iconDefaultViewBox
  , getViewBox
  , isSinglePathIcon
  , isMultiPathIcon
  , isPartedIconDef
  , iconPathCount
  
  -- * Color Helpers
  , oklchToCss
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , (<>)
  , map
  , (>)
  , (+)
  )

import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Array (head, tail) 
import Data.Array (uncons) as Array

import Hydrogen.Schema.Geometry.Path.Serialization (toSvgString) as PathSerial
import Hydrogen.Schema.Geometry.Path.Types (Path)

import Hydrogen.Icon.Types
  ( IconDefinition
  , IconPath(SinglePath, MultiPath, PartedIcon)
  , IconPart
  , IconName
  , IconProps
  , IconSize(SizeXs, SizeSm, SizeMd, SizeLg, SizeXl, SizeXxl)
  , IconStyle(StyleOutline, StyleSolid, StyleDuotone, StyleFilled)
  , IconViewBox
  , defaultViewBox
  , viewBox24
  , viewBox16
  , unIconName
  )

import Hydrogen.Icon.Brand
  ( ThemedIcon
  , applyTheme
  , IconTheme(IconTheme)
  , resolveIconColor
  )

import Hydrogen.Schema.Brand.ColorSystem (ThemedColorSystem)
import Hydrogen.Schema.Brand.Token.Color (ColorRole)
import Hydrogen.Schema.Brand.ColorSystem (PaletteMode) as Palette

import Hydrogen.Schema.Color.OKLCH (OKLCH, oklchToRecord)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // svg // element // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG element with tag name and attributes.
newtype SvgElement = SvgElement
  { tag :: String
  , attributes :: SvgAttributes
  , content :: Maybe String
  }

-- | SVG element attributes.
type SvgAttributes = Array SvgAttribute

-- | Single SVG attribute.
newtype SvgAttribute = SvgAttribute
  { name :: String
  , value :: String
  }

-- | SVG fill specification.
data SvgFill
  = SvgFillNone
  | SvgFillCurrentColor
  | SvgFillColor String
  | SvgFillUrl String

-- | SVG stroke specification.
data SvgStroke
  = SvgStrokeNone
  | SvgStrokeCurrentColor
  | SvgStrokeColor String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // svg // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render icon as complete SVG element.
-- |
-- | Includes xmlns, viewBox, and standard attributes.
renderAsSvg
  :: IconDefinition
  -> IconProps
  -> SvgElement
renderAsSvg icon props =
  svgElement
    { tag: "svg"
    , attributes: buildSvgAttributes icon props
    , content: Just (renderAsPath icon props)
    }

-- | Render icon as path element only.
-- |
-- | Returns just the `<path d="..."/>` element without SVG wrapper.
renderAsPath
  :: IconDefinition
  -> IconProps
  -> String
renderAsPath icon _props =
  "<path " <> pathAttributes icon.paths <> " />"
  where
    pathAttributes :: IconPath -> String
    pathAttributes paths =
      "d=\"" <> pathData paths <> "\""

-- | Render icon as SVG symbol.
-- |
-- | Returns `<symbol>` element for use with `<use href="#id"/>`.
renderAsSymbol
  :: IconDefinition
  -> IconProps
  -> String
renderAsSymbol icon props =
  "<symbol id=\"" <> unIconName icon.name <> "\" viewBox=\"" <> viewBoxValue icon.viewBox <> "\">"
  <> renderAsPath icon props
  <> "</symbol>"

-- | Render as inline SVG string.
-- |
-- | Full SVG markup as string, ready for embedding.
renderAsInline
  :: IconDefinition
  -> IconProps
  -> String
renderAsInline icon props =
  svgOpenTag icon props
  <> renderAsPath icon props
  <> "</svg>"

-- | Build SVG open tag with attributes.
svgOpenTag :: IconDefinition -> IconProps -> String
svgOpenTag icon props =
  "<svg"
  <> " xmlns=\"http://www.w3.org/2000/svg\""
  <> " viewBox=\"" <> viewBoxValue icon.viewBox <> "\""
  <> " width=\"" <> sizeValue props.size <> "\""
  <> " height=\"" <> sizeValue props.size <> "\""
  <> ">"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // svg // element // builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create SVG element.
svgElement :: { tag :: String, attributes :: SvgAttributes, content :: Maybe String } -> SvgElement
svgElement = SvgElement

-- | Create path element.
pathElement :: String -> SvgElement
pathElement d = SvgElement
  { tag: "path"
  , attributes: [svgAttr "d" d]
  , content: Nothing
  }

-- | Create symbol element.
symbolElement :: String -> IconViewBox -> SvgElement -> SvgElement
symbolElement id vb content = SvgElement
  { tag: "symbol"
  , attributes:
      [ svgAttr "id" id
      , svgAttr "viewBox" (viewBoxValue vb)
      ]
  , content: Just (svgContent content)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // svg // attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default SVG attributes.
defaultSvgAttributes :: SvgAttributes
defaultSvgAttributes =
  [ svgAttr "xmlns" "http://www.w3.org/2000/svg"
  , svgAttr "fill" "currentColor"
  ]

-- | Build SVG attributes from icon props.
buildSvgAttributes :: IconDefinition -> IconProps -> SvgAttributes
buildSvgAttributes icon props =
  [ svgAttr "xmlns" "http://www.w3.org/2000/svg"
  , svgAttr "viewBox" (viewBoxValue icon.viewBox)
  , svgAttr "width" (sizeValue props.size)
  , svgAttr "height" (sizeValue props.size)
  , svgAttr "fill" (fillValue props)
  , svgAttr "stroke" (strokeValue props)
  ]

-- | Convert SvgFill to string.
fillToString :: SvgFill -> String
fillToString = case _ of
  SvgFillNone -> "none"
  SvgFillCurrentColor -> "currentColor"
  SvgFillColor c -> c
  SvgFillUrl u -> "url(" <> u <> ")"

-- | Convert SvgStroke to string.
strokeToString :: SvgStroke -> String
strokeToString = case _ of
  SvgStrokeNone -> "none"
  SvgStrokeCurrentColor -> "currentColor"
  SvgStrokeColor c -> c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // svg // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create SVG attribute.
svgAttr :: String -> String -> SvgAttribute
svgAttr name value = SvgAttribute { name: name, value: value }

-- | Get viewBox string from IconViewBox.
viewBoxValue :: IconViewBox -> String
viewBoxValue vb = show vb.width <> " " <> show vb.height

-- | Get size string from IconSize.
sizeValue :: IconSize -> String
sizeValue size = show size <> "px"

-- | Get fill value from props (based on style).
fillValue :: IconProps -> String
fillValue props = case props.style of
  StyleOutline -> "none"
  StyleSolid -> "currentColor"
  StyleFilled -> "currentColor"
  StyleDuotone -> "currentColor"

-- | Get stroke value from props.
strokeValue :: IconProps -> String
strokeValue props =
  let w = props.strokeWidth
  in if w > 0.0 then "currentColor" else "none"

-- | Extract path data from IconPath.
pathData :: IconPath -> String
pathData = case _ of
  SinglePath p -> PathSerial.toSvgString p
  MultiPath paths -> multiPathData paths
  PartedIcon parts -> multiPathData (map partToPath parts)
  where
    multiPathData :: Array Path -> String
    multiPathData paths =
      case head paths of
        Nothing -> ""
        Just first -> PathSerial.toSvgString first
    
    partToPath :: IconPart -> Path
    partToPath part = part.path

-- | Get content from SVG element.
svgContent :: SvgElement -> String
svgContent (SvgElement e) = fromMaybe "" e.content

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // show // instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show instance for SvgElement.
-- |
-- | Output: "(SvgElement <tag> [<attributes>])"
-- | Per SHOW_DEBUG_CONVENTION.
instance showSvgElement :: Show SvgElement where
  show (SvgElement e) = "(SvgElement " <> e.tag <> " [" <> showAttributeCount e.attributes <> "])"
    where
      showAttributeCount :: SvgAttributes -> String
      showAttributeCount attrs = show (countAttrs attrs)
      countAttrs :: Array SvgAttribute -> Int
      countAttrs a = case head a of
        Nothing -> 0
        Just _ -> 1 + countAttrs (dropFirst a)
      dropFirst :: Array SvgAttribute -> Array SvgAttribute
      dropFirst a = case tailArray a of
        Nothing -> []
        Just t -> t

-- | Show instance for SvgAttribute.
instance showSvgAttribute :: Show SvgAttribute where
  show (SvgAttribute attr) = "(SvgAttribute " <> attr.name <> "=" <> show attr.value <> ")"

-- | Show instance for SvgFill.
instance showSvgFill :: Show SvgFill where
  show = case _ of
    SvgFillNone -> "SvgFillNone"
    SvgFillCurrentColor -> "SvgFillCurrentColor"
    SvgFillColor c -> "(SvgFillColor " <> show c <> ")"
    SvgFillUrl u -> "(SvgFillUrl " <> show u <> ")"

-- | Show instance for SvgStroke.
instance showSvgStroke :: Show SvgStroke where
  show = case _ of
    SvgStrokeNone -> "SvgStrokeNone"
    SvgStrokeCurrentColor -> "SvgStrokeCurrentColor"
    SvgStrokeColor c -> "(SvgStrokeColor " <> show c <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // themed // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render themed icon with brand colors.
-- |
-- | Applies brand color resolution to produce SVG with actual color values.
renderThemedSvg
  :: IconDefinition
  -> IconProps
  -> IconTheme
  -> SvgElement
renderThemedSvg icon props (IconTheme theme) =
  svgElement
    { tag: "svg"
    , attributes: buildThemedAttributes icon props theme
    , content: Just (renderThemedPath icon props theme)
    }

-- | Build themed SVG attributes with resolved colors.
buildThemedAttributes
  :: IconDefinition
  -> IconProps
  -> { mode :: Palette.PaletteMode, colorSystem :: ThemedColorSystem }
  -> SvgAttributes
buildThemedAttributes icon props theme =
  [ svgAttr "xmlns" "http://www.w3.org/2000/svg"
  , svgAttr "viewBox" (viewBoxValue icon.viewBox)
  , svgAttr "width" (sizeValueByName props.size)
  , svgAttr "height" (sizeValueByName props.size)
  , svgAttr "fill" (themedFill props theme)
  ]

-- | Render themed path with brand colors.
renderThemedPath
  :: IconDefinition
  -> IconProps
  -> { mode :: Palette.PaletteMode, colorSystem :: ThemedColorSystem }
  -> String
renderThemedPath icon props theme =
  "<path d=\"" <> pathData icon.paths <> "\" fill=\"" <> themedFill props theme <> "\"/>"

-- | Get themed fill color.
themedFill
  :: IconProps
  -> { mode :: Palette.PaletteMode, colorSystem :: ThemedColorSystem }
  -> String
themedFill props theme =
  let resolved = resolveIconColor props.colorRole theme.mode theme.colorSystem
  in oklchToCss resolved

-- | Convert OKLCH to CSS color string.
oklchToCss :: OKLCH -> String
oklchToCss oklch =
  let rec = oklchToRecord oklch
  in "oklch(" <> show rec.l <> " " <> show rec.c <> " " <> show rec.h <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // icon // definition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get icon name as string.
iconNameString :: IconDefinition -> String
iconNameString icon = unIconName icon.name

-- | Get default viewBox for icon.
iconDefaultViewBox :: IconDefinition -> IconViewBox
iconDefaultViewBox icon = icon.viewBox

-- | Get icon viewBox.
getViewBox :: IconDefinition -> IconViewBox
getViewBox = iconDefaultViewBox

-- | Default viewBox (24x24).
defaultSvgViewBox :: IconViewBox
defaultSvgViewBox = defaultViewBox

-- | Standard 24x24 viewBox.
viewBox24x24 :: IconViewBox
viewBox24x24 = viewBox24

-- | Standard 16x16 viewBox.
viewBox16x16 :: IconViewBox
viewBox16x16 = viewBox16

-- | Get size as pixel value.
sizeAsPixels :: IconSize -> Int
sizeAsPixels size = case size of
  SizeXs -> 12
  SizeSm -> 16
  SizeMd -> 24
  SizeLg -> 32
  SizeXl -> 48
  SizeXxl -> 64

-- | Size value as string with unit.
sizeValueByName :: IconSize -> String
sizeValueByName size = show (sizeAsPixels size) <> "px"

-- | Size 12px.
sizeXs :: IconSize
sizeXs = SizeXs

-- | Size 16px.
sizeSm :: IconSize
sizeSm = SizeSm

-- | Size 24px.
sizeMd :: IconSize
sizeMd = SizeMd

-- | Size 32px.
sizeLg :: IconSize
sizeLg = SizeLg

-- | Size 48px.
sizeXl :: IconSize
sizeXl = SizeXl

-- | Size 64px.
sizeXxl :: IconSize
sizeXxl = SizeXxl

-- | Check if icon has single path.
isSinglePathIcon :: IconDefinition -> Boolean
isSinglePathIcon icon = case icon.paths of
  SinglePath _ -> true
  _ -> false

-- | Check if icon has multiple paths.
isMultiPathIcon :: IconDefinition -> Boolean
isMultiPathIcon icon = case icon.paths of
  MultiPath _ -> true
  _ -> false

-- | Check if icon has parted paths.
isPartedIconDef :: IconDefinition -> Boolean
isPartedIconDef icon = case icon.paths of
  PartedIcon _ -> true
  _ -> false

-- | Get path count from icon.
iconPathCount :: IconDefinition -> Int
iconPathCount icon = case icon.paths of
  SinglePath _ -> 1
  MultiPath ps -> arrayLength ps
  PartedIcon ps -> arrayLength ps
  where
    arrayLength :: forall a. Array a -> Int
    arrayLength arr = lenHelper arr 0
    lenHelper :: forall a. Array a -> Int -> Int
    lenHelper a acc = case head a of
      Nothing -> acc
      Just _ -> lenHelper (fromMaybe [] (tailArray a)) (acc + 1)

-- | Tail of array (helper).
tailArray :: forall a. Array a -> Maybe (Array a)
tailArray arr = case Array.uncons arr of
  Nothing -> Nothing
  Just { tail: t } -> if arrayIsEmpty t then Nothing else Just t
  where
    arrayIsEmpty :: forall b. Array b -> Boolean
    arrayIsEmpty b = case head b of
      Nothing -> true
      Just _ -> false