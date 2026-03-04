-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // target // hyperconsole
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HyperConsole Target — TUI Rendering via CBOR
-- |
-- | Renders Hydrogen Elements to HyperConsole Widget specifications, serialized
-- | as CBOR for cross-language transport to the Haskell HyperConsole runtime.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Hydrogen (PureScript) → CBOR bytes → HyperConsole (Haskell) → Terminal
-- | ```
-- |
-- | This module defines:
-- |
-- | - `WidgetSpec` — Pure data mirroring HyperConsole.Widget
-- | - `StyleSpec` — Pure data mirroring HyperConsole.Style  
-- | - `ColorSpec` — Pure data mirroring HyperConsole.Color
-- | - CBOR encoding for cross-language serialization
-- | - Element conversion to WidgetSpec
-- |
-- | ## Wire Protocol
-- |
-- | The CBOR encoding follows a tagged union pattern:
-- |
-- | ```cbor
-- | WidgetSpec = {
-- |   "type": "text" | "vbox" | "hbox" | "bordered" | ...,
-- |   "style": StyleSpec?,
-- |   "children": [WidgetSpec]?,
-- |   ...type-specific fields
-- | }
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element as E
-- | import Hydrogen.Target.HyperConsole as THC
-- | import Hydrogen.Serialize.CBOR as CBOR
-- |
-- | -- Convert element to widget spec
-- | spec :: THC.WidgetSpec
-- | spec = THC.toWidgetSpec myElement
-- |
-- | -- Serialize to CBOR bytes for transport
-- | bytes :: CBOR.Bytes
-- | bytes = THC.serialize spec
-- | ```
module Hydrogen.Target.HyperConsole
  ( -- * Widget Specification
    WidgetSpec
      ( TextWidget
      , VBoxWidget
      , HBoxWidget
      , BorderedWidget
      , PaddedWidget
      , FixedWidget
      , EmptyWidget
      , SpaceWidget
      , FillWidget
      , RuleWidget
      , SpinnerWidget
      , ProgressWidget
      , CenteredWidget
      )
  
  -- * Style Specification
  , StyleSpec
  , defaultStyleSpec
  
  -- * Color Specification
  , ColorSpec
      ( DefaultColor
      , BlackColor
      , RedColor
      , GreenColor
      , YellowColor
      , BlueColor
      , MagentaColor
      , CyanColor
      , WhiteColor
      , BrightBlackColor
      , BrightRedColor
      , BrightGreenColor
      , BrightYellowColor
      , BrightBlueColor
      , BrightMagentaColor
      , BrightCyanColor
      , BrightWhiteColor
      , Color256
      , RGBColor
      )
  
  -- * Attribute Specification
  , AttrSpec
      ( BoldAttr
      , DimAttr
      , ItalicAttr
      , UnderlineAttr
      , BlinkAttr
      , ReverseAttr
      , StrikethroughAttr
      )
  
  -- * Constraint Specification
  , ConstraintSpec
      ( FillConstraint
      , FixedConstraint
      , MinConstraint
      , MaxConstraint
      )
  
  -- * Conversion
  , toWidgetSpec
  
  -- * Serialization
  , serialize
  , serializeToArray
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , Unit
  , map
  , show
  , unit
  , ($)
  , (<>)
  , (+)
  , (==)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))
import Hydrogen.Render.Element as E
import Hydrogen.Serialize.CBOR as CBOR

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Terminal color specification (mirrors HyperConsole.Style.Color)
-- |
-- | Supports:
-- | - Default terminal colors
-- | - 8 basic colors + 8 bright variants
-- | - 256-color palette
-- | - 24-bit RGB
data ColorSpec
  = DefaultColor
  | BlackColor
  | RedColor
  | GreenColor
  | YellowColor
  | BlueColor
  | MagentaColor
  | CyanColor
  | WhiteColor
  | BrightBlackColor
  | BrightRedColor
  | BrightGreenColor
  | BrightYellowColor
  | BrightBlueColor
  | BrightMagentaColor
  | BrightCyanColor
  | BrightWhiteColor
  | Color256 Int       -- ^ 256-color palette index (0-255)
  | RGBColor Int Int Int  -- ^ 24-bit RGB (0-255, 0-255, 0-255)

derive instance eqColorSpec :: Eq ColorSpec

instance showColorSpec :: Show ColorSpec where
  show DefaultColor = "DefaultColor"
  show BlackColor = "BlackColor"
  show RedColor = "RedColor"
  show GreenColor = "GreenColor"
  show YellowColor = "YellowColor"
  show BlueColor = "BlueColor"
  show MagentaColor = "MagentaColor"
  show CyanColor = "CyanColor"
  show WhiteColor = "WhiteColor"
  show BrightBlackColor = "BrightBlackColor"
  show BrightRedColor = "BrightRedColor"
  show BrightGreenColor = "BrightGreenColor"
  show BrightYellowColor = "BrightYellowColor"
  show BrightBlueColor = "BrightBlueColor"
  show BrightMagentaColor = "BrightMagentaColor"
  show BrightCyanColor = "BrightCyanColor"
  show BrightWhiteColor = "BrightWhiteColor"
  show (Color256 n) = "(Color256 " <> show n <> ")"
  show (RGBColor r g b) = "(RGBColor " <> show r <> " " <> show g <> " " <> show b <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // attr
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text attribute specification (mirrors HyperConsole.Style.Attr)
data AttrSpec
  = BoldAttr
  | DimAttr
  | ItalicAttr
  | UnderlineAttr
  | BlinkAttr
  | ReverseAttr
  | StrikethroughAttr

derive instance eqAttrSpec :: Eq AttrSpec

instance showAttrSpec :: Show AttrSpec where
  show BoldAttr = "BoldAttr"
  show DimAttr = "DimAttr"
  show ItalicAttr = "ItalicAttr"
  show UnderlineAttr = "UnderlineAttr"
  show BlinkAttr = "BlinkAttr"
  show ReverseAttr = "ReverseAttr"
  show StrikethroughAttr = "StrikethroughAttr"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Style specification (mirrors HyperConsole.Style.Style)
-- |
-- | Combines foreground color, background color, and text attributes.
type StyleSpec =
  { fg :: ColorSpec
  , bg :: ColorSpec
  , attrs :: Array AttrSpec
  }

-- | Default style with no colors or attributes
defaultStyleSpec :: StyleSpec
defaultStyleSpec =
  { fg: DefaultColor
  , bg: DefaultColor
  , attrs: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constraint
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout constraint specification (mirrors HyperConsole.Layout.Constraint)
data ConstraintSpec
  = FillConstraint Int     -- ^ Fill remaining space with weight
  | FixedConstraint Int    -- ^ Fixed size in cells
  | MinConstraint Int      -- ^ Minimum size
  | MaxConstraint Int      -- ^ Maximum size

derive instance eqConstraintSpec :: Eq ConstraintSpec

instance showConstraintSpec :: Show ConstraintSpec where
  show (FillConstraint w) = "(FillConstraint " <> show w <> ")"
  show (FixedConstraint n) = "(FixedConstraint " <> show n <> ")"
  show (MinConstraint n) = "(MinConstraint " <> show n <> ")"
  show (MaxConstraint n) = "(MaxConstraint " <> show n <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // widget
-- ═════════════════════════════════════════════════════════════════════════════

-- | Widget specification (mirrors HyperConsole.Widget types)
-- |
-- | Pure data description of terminal widgets. These are serialized to CBOR
-- | and interpreted by the Haskell HyperConsole runtime.
data WidgetSpec
  = TextWidget
      { text :: String
      , style :: StyleSpec
      }
  | VBoxWidget
      { children :: Array WidgetSpec
      , constraints :: Array ConstraintSpec
      }
  | HBoxWidget
      { children :: Array WidgetSpec
      , constraints :: Array ConstraintSpec
      }
  | BorderedWidget
      { child :: WidgetSpec
      , style :: StyleSpec
      , title :: Maybe String
      }
  | PaddedWidget
      { child :: WidgetSpec
      , top :: Int
      , right :: Int
      , bottom :: Int
      , left :: Int
      }
  | FixedWidget
      { child :: WidgetSpec
      , width :: Int
      , height :: Int
      }
  | CenteredWidget
      { child :: WidgetSpec
      }
  | EmptyWidget
  | SpaceWidget
      { width :: Int
      , height :: Int
      }
  | FillWidget
      { char :: String
      , style :: StyleSpec
      }
  | RuleWidget
      { char :: String
      , style :: StyleSpec
      }
  | SpinnerWidget
      { tick :: Int
      , style :: StyleSpec
      }
  | ProgressWidget
      { percent :: Number
      , filledStyle :: StyleSpec
      , emptyStyle :: StyleSpec
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // cbor // encode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Encode a ColorSpec to CBOR
encodeColor :: ColorSpec -> CBOR.CBORValue
encodeColor color = case color of
  DefaultColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "default") ]
  BlackColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "black") ]
  RedColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "red") ]
  GreenColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "green") ]
  YellowColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "yellow") ]
  BlueColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "blue") ]
  MagentaColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "magenta") ]
  CyanColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "cyan") ]
  WhiteColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "white") ]
  BrightBlackColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "bright_black") ]
  BrightRedColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "bright_red") ]
  BrightGreenColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "bright_green") ]
  BrightYellowColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "bright_yellow") ]
  BrightBlueColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "bright_blue") ]
  BrightMagentaColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "bright_magenta") ]
  BrightCyanColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "bright_cyan") ]
  BrightWhiteColor -> CBOR.encodeMap [ Tuple "type" (CBOR.encodeString "bright_white") ]
  Color256 n -> CBOR.encodeMap 
    [ Tuple "type" (CBOR.encodeString "color256")
    , Tuple "index" (CBOR.encodeInt n)
    ]
  RGBColor r g b -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "rgb")
    , Tuple "r" (CBOR.encodeInt r)
    , Tuple "g" (CBOR.encodeInt g)
    , Tuple "b" (CBOR.encodeInt b)
    ]

-- | Encode an AttrSpec to CBOR
encodeAttr :: AttrSpec -> CBOR.CBORValue
encodeAttr attr = CBOR.encodeString $ case attr of
  BoldAttr -> "bold"
  DimAttr -> "dim"
  ItalicAttr -> "italic"
  UnderlineAttr -> "underline"
  BlinkAttr -> "blink"
  ReverseAttr -> "reverse"
  StrikethroughAttr -> "strikethrough"

-- | Encode a StyleSpec to CBOR
encodeStyle :: StyleSpec -> CBOR.CBORValue
encodeStyle style = CBOR.encodeMap
  [ Tuple "fg" (encodeColor style.fg)
  , Tuple "bg" (encodeColor style.bg)
  , Tuple "attrs" (CBOR.CBORArray (map encodeAttr style.attrs))
  ]

-- | Encode a ConstraintSpec to CBOR
encodeConstraint :: ConstraintSpec -> CBOR.CBORValue
encodeConstraint constraint = case constraint of
  FillConstraint w -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "fill")
    , Tuple "weight" (CBOR.encodeInt w)
    ]
  FixedConstraint n -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "fixed")
    , Tuple "size" (CBOR.encodeInt n)
    ]
  MinConstraint n -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "min")
    , Tuple "size" (CBOR.encodeInt n)
    ]
  MaxConstraint n -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "max")
    , Tuple "size" (CBOR.encodeInt n)
    ]

-- | Encode a WidgetSpec to CBOR
encodeWidget :: WidgetSpec -> CBOR.CBORValue
encodeWidget widget = case widget of
  TextWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "text")
    , Tuple "text" (CBOR.encodeString r.text)
    , Tuple "style" (encodeStyle r.style)
    ]
  
  VBoxWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "vbox")
    , Tuple "children" (CBOR.CBORArray (map encodeWidget r.children))
    , Tuple "constraints" (CBOR.CBORArray (map encodeConstraint r.constraints))
    ]
  
  HBoxWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "hbox")
    , Tuple "children" (CBOR.CBORArray (map encodeWidget r.children))
    , Tuple "constraints" (CBOR.CBORArray (map encodeConstraint r.constraints))
    ]
  
  BorderedWidget r -> CBOR.encodeMap $
    [ Tuple "type" (CBOR.encodeString "bordered")
    , Tuple "child" (encodeWidget r.child)
    , Tuple "style" (encodeStyle r.style)
    ] <> encodeMaybeTitle r.title
  
  PaddedWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "padded")
    , Tuple "child" (encodeWidget r.child)
    , Tuple "top" (CBOR.encodeInt r.top)
    , Tuple "right" (CBOR.encodeInt r.right)
    , Tuple "bottom" (CBOR.encodeInt r.bottom)
    , Tuple "left" (CBOR.encodeInt r.left)
    ]
  
  FixedWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "fixed")
    , Tuple "child" (encodeWidget r.child)
    , Tuple "width" (CBOR.encodeInt r.width)
    , Tuple "height" (CBOR.encodeInt r.height)
    ]
  
  CenteredWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "centered")
    , Tuple "child" (encodeWidget r.child)
    ]
  
  EmptyWidget -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "empty")
    ]
  
  SpaceWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "space")
    , Tuple "width" (CBOR.encodeInt r.width)
    , Tuple "height" (CBOR.encodeInt r.height)
    ]
  
  FillWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "fill")
    , Tuple "char" (CBOR.encodeString r.char)
    , Tuple "style" (encodeStyle r.style)
    ]
  
  RuleWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "rule")
    , Tuple "char" (CBOR.encodeString r.char)
    , Tuple "style" (encodeStyle r.style)
    ]
  
  SpinnerWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "spinner")
    , Tuple "tick" (CBOR.encodeInt r.tick)
    , Tuple "style" (encodeStyle r.style)
    ]
  
  ProgressWidget r -> CBOR.encodeMap
    [ Tuple "type" (CBOR.encodeString "progress")
    , Tuple "percent" (CBOR.encodeNumber r.percent)
    , Tuple "filled_style" (encodeStyle r.filledStyle)
    , Tuple "empty_style" (encodeStyle r.emptyStyle)
    ]

-- | Encode optional title field
encodeMaybeTitle :: Maybe String -> Array (Tuple String CBOR.CBORValue)
encodeMaybeTitle maybeTitle = case maybeTitle of
  Nothing -> []
  Just title -> [ Tuple "title" (CBOR.encodeString title) ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // element // convert
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert a Hydrogen Element to a WidgetSpec
-- |
-- | This is the primary conversion function. HTML-like elements are mapped
-- | to their closest TUI equivalents:
-- |
-- | - `div` → VBox (vertical stacking by default)
-- | - `span` → HBox (inline/horizontal)
-- | - `p` → Text with newline
-- | - `button` → Bordered text
-- | - Text nodes → TextWidget
-- |
-- | Styles from `style` attributes are parsed and converted to StyleSpec.
toWidgetSpec :: forall msg. E.Element msg -> WidgetSpec
toWidgetSpec element = case element of
  E.Empty -> EmptyWidget
  
  E.Text s -> TextWidget
    { text: s
    , style: defaultStyleSpec
    }
  
  E.Element r -> convertElement r.tag r.attributes r.children
  
  E.Keyed r -> 
    let children = map (\(Tuple _ el) -> el) r.children
    in convertElement r.tag r.attributes children
  
  E.Lazy r -> toWidgetSpec (r.thunk unit)

-- | Convert an HTML-like element to WidgetSpec based on tag
convertElement 
  :: forall msg
   . String 
  -> Array (E.Attribute msg) 
  -> Array (E.Element msg) 
  -> WidgetSpec
convertElement tag attrs children = case tag of
  -- Block containers → VBox
  "div" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "section" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "article" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "main" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "header" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "footer" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "nav" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  -- Inline containers → HBox
  "span" -> HBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  -- Lists → VBox
  "ul" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "ol" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "li" -> HBoxWidget
    { children: 
        [ TextWidget { text: "• ", style: defaultStyleSpec }
        ] <> map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children + 1)
    }
  
  -- Text elements
  "p" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "h1" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [BoldAttr] }
    }
  
  "h2" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [BoldAttr] }
    }
  
  "h3" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [BoldAttr] }
    }
  
  "h4" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [BoldAttr] }
    }
  
  "h5" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [BoldAttr] }
    }
  
  "h6" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [BoldAttr] }
    }
  
  -- Interactive elements
  "button" -> BorderedWidget
    { child: TextWidget
        { text: extractTextContent children
        , style: defaultStyleSpec
        }
    , style: defaultStyleSpec
    , title: Nothing
    }
  
  "input" -> BorderedWidget
    { child: TextWidget
        { text: extractInputValue attrs
        , style: defaultStyleSpec
        }
    , style: defaultStyleSpec
    , title: Nothing
    }
  
  "textarea" -> BorderedWidget
    { child: VBoxWidget
        { children: map toWidgetSpec children
        , constraints: defaultConstraints (Array.length children)
        }
    , style: defaultStyleSpec
    , title: Nothing
    }
  
  -- Horizontal rule
  "hr" -> RuleWidget
    { char: "─"
    , style: defaultStyleSpec
    }
  
  -- Line break → empty line
  "br" -> SpaceWidget { width: 0, height: 1 }
  
  -- Emphasis styles
  "strong" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [BoldAttr] }
    }
  
  "b" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [BoldAttr] }
    }
  
  "em" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [ItalicAttr] }
    }
  
  "i" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [ItalicAttr] }
    }
  
  "u" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [UnderlineAttr] }
    }
  
  "s" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [StrikethroughAttr] }
    }
  
  "del" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [StrikethroughAttr] }
    }
  
  "code" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { fg = CyanColor }
    }
  
  "pre" -> BorderedWidget
    { child: VBoxWidget
        { children: map toWidgetSpec children
        , constraints: defaultConstraints (Array.length children)
        }
    , style: defaultStyleSpec
    , title: Nothing
    }
  
  -- Fieldset with legend
  "fieldset" -> BorderedWidget
    { child: VBoxWidget
        { children: map toWidgetSpec children
        , constraints: defaultConstraints (Array.length children)
        }
    , style: defaultStyleSpec
    , title: extractLegend children
    }
  
  -- Tables
  "table" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "thead" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "tbody" -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "tr" -> HBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }
  
  "th" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [BoldAttr] }
    }
  
  "td" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec
    }
  
  -- Links (display as underlined text)
  "a" -> TextWidget
    { text: extractTextContent children
    , style: defaultStyleSpec { attrs = [UnderlineAttr], fg = BlueColor }
    }
  
  -- Default: treat as VBox container
  _ -> VBoxWidget
    { children: map toWidgetSpec children
    , constraints: defaultConstraints (Array.length children)
    }

-- | Generate default fill constraints for N children
defaultConstraints :: Int -> Array ConstraintSpec
defaultConstraints n = Array.replicate n (FillConstraint 1)

-- | Extract text content from children
extractTextContent :: forall msg. Array (E.Element msg) -> String
extractTextContent children = 
  Array.foldl appendText "" children
  where
    appendText :: String -> E.Element msg -> String
    appendText acc el = case el of
      E.Text s -> acc <> s
      E.Element r -> acc <> extractTextContent r.children
      E.Keyed r -> acc <> extractTextContent (map (\(Tuple _ e) -> e) r.children)
      E.Lazy r -> acc <> extractTextContent [r.thunk unit]
      E.Empty -> acc

-- | Extract value from input attributes
extractInputValue :: forall msg. Array (E.Attribute msg) -> String
extractInputValue attrs = 
  Array.foldl findValue "" attrs
  where
    findValue :: String -> E.Attribute msg -> String
    findValue acc attr = case attr of
      E.Attr "value" v -> v
      E.Prop "value" v -> v
      _ -> acc

-- | Extract legend text from fieldset children
extractLegend :: forall msg. Array (E.Element msg) -> Maybe String
extractLegend children =
  Array.findMap findLegend children
  where
    findLegend :: E.Element msg -> Maybe String
    findLegend el = case el of
      E.Element r | r.tag == "legend" -> Just (extractTextContent r.children)
      _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize a WidgetSpec to CBOR bytes
-- |
-- | This is the final step for cross-language transport. The resulting bytes
-- | can be written to a pipe/socket and decoded by HyperConsole on the Haskell side.
serialize :: WidgetSpec -> CBOR.Bytes
serialize widget = CBOR.serialize (encodeWidget widget)

-- | Serialize to raw int array (for FFI boundaries)
serializeToArray :: WidgetSpec -> Array Int
serializeToArray widget = CBOR.serializeToArray (encodeWidget widget)
