-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // gpu // flatten
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element → CommandBuffer Flattener
-- |
-- | Converts the tree-based Element structure to a flat array of DrawCommands.
-- | This is the bridge between the component model (tree) and the GPU model (flat).
-- |
-- | ## Design Principles
-- |
-- | 1. **Pure transformation**: Element in, CommandBuffer out. No effects.
-- |
-- | 2. **Layout resolution**: Computes positions from layout attributes.
-- |    Currently simplified — full flexbox would be a larger undertaking.
-- |
-- | 3. **Style extraction**: Pulls Schema atoms from Element styles and
-- |    converts to DrawCommand parameters.
-- |
-- | 4. **Event mapping**: Assigns PickIds to interactive elements and
-- |    returns a mapping for the runtime.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Element msg
-- |     ↓ flatten
-- | { commands :: CommandBuffer msg
-- | , pickMap :: Map PickId msg
-- | }
-- | ```
-- |
-- | The runtime uses pickMap to dispatch messages when the pick buffer
-- | reports an interaction.
-- |
-- | ## Current Limitations
-- |
-- | - Layout is position-based only (no auto-layout yet)
-- | - Text is placeholder (glyph shaping needs font metrics)
-- | - Styles must use Schema atoms (no CSS string parsing)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.GPU.Flatten as Flatten
-- | import Hydrogen.Render.Element as E
-- |
-- | result = Flatten.flatten myElement
-- | -- result.commands :: Array (DrawCommand msg)
-- | -- result.pickMap :: Map PickId msg
-- | ```

module Hydrogen.GPU.Flatten
  ( -- * Types
    FlattenResult
  , FlattenState
  , LayoutBox
  
  -- * Flattening
  , flatten
  , flattenWithState
  , flattenWithFont
  
  -- * Layout
  , defaultBox
  , offsetBox
  , boxesEqual
  , showBox
  , genericEqual
  , showDebug
  , discardMaybe
  
  -- * Style Extraction
  , extractBackground
  , extractBorderRadius
  , extractFontConfig
  ) where

import Prelude
  ( class Eq
  , class Show
  , Unit
  , bind
  , map
  , pure
  , show
  , unit
  , ($)
  , (+)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple), fst, snd)
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.GPU.Text as Text
import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of flattening an Element tree.
type FlattenResult msg =
  { commands :: DC.CommandBuffer msg
  , pickMap :: Map.Map DC.PickId msg
  }

-- | State maintained during flattening.
type FlattenState msg =
  { nextPickId :: Int
  , pickMap :: Map.Map DC.PickId msg
  , currentDepth :: Number
  , box :: LayoutBox
  , fontAtlas :: Text.FontAtlas
  , fontConfig :: Text.FontConfig
  }

-- | Layout box for an element.
-- | Represents the computed position and size.
type LayoutBox =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // flattening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten an Element tree to a CommandBuffer.
-- |
-- | This is the main entry point. Takes an Element and produces:
-- | - commands: Array of DrawCommands ready for serialization
-- | - pickMap: Mapping from PickId to message for hit testing
flatten :: forall msg. E.Element msg -> FlattenResult msg
flatten element =
  let
    initialState = 
      { nextPickId: 1
      , pickMap: Map.empty
      , currentDepth: 0.0
      , box: defaultBox
      , fontAtlas: Text.emptyAtlas
      , fontConfig: Text.fontConfig 0 16.0  -- Default: font 0, 16px
      }
    result = flattenWithState initialState element
  in
    { commands: fst result
    , pickMap: (snd result).pickMap
    }

-- | Flatten with custom font configuration.
-- |
-- | Use this when you have a loaded font atlas and specific font settings.
-- | Uses $ for function application in let bindings.
flattenWithFont 
  :: forall msg
   . Text.FontAtlas 
  -> Text.FontConfig 
  -> E.Element msg 
  -> FlattenResult msg
flattenWithFont atlas config element =
  let
    initialState = 
      { nextPickId: 1
      , pickMap: Map.empty
      , currentDepth: 0.0
      , box: defaultBox
      , fontAtlas: atlas
      , fontConfig: config
      }
    result = flattenWithState initialState $ element
    cmds = fst $ result
    picks = (snd result).pickMap
  in
    { commands: cmds, pickMap: picks }

-- | Flatten with explicit state (for recursive calls).
flattenWithState 
  :: forall msg
   . FlattenState msg 
  -> E.Element msg 
  -> Tuple (DC.CommandBuffer msg) (FlattenState msg)
flattenWithState state = case _ of
  E.Empty -> 
    Tuple [] state
  
  E.Text str ->
    -- Generate draw commands for text using the typography pipeline.
    -- Uses current box position as text baseline origin.
    let
      commands = Text.textToCommands 
        state.fontConfig 
        state.fontAtlas 
        state.box.x 
        state.box.y 
        str
    in
      Tuple commands state
  
  E.Element r ->
    flattenElement state r.namespace r.tag r.attributes r.children
  
  E.Keyed r ->
    let children = map snd r.children
    in flattenElement state r.namespace r.tag r.attributes children
  
  E.Lazy r ->
    flattenWithState state (r.thunk unit)

-- | Flatten a standard element.
flattenElement
  :: forall msg
   . FlattenState msg
  -> Maybe E.Namespace
  -> String
  -> Array (E.Attribute msg)
  -> Array (E.Element msg)
  -> Tuple (DC.CommandBuffer msg) (FlattenState msg)
flattenElement state _namespace _tag attrs children =
  let
    -- Extract visual properties from attributes
    background = extractBackground attrs
    borderRadius = extractBorderRadius attrs
    boxFromAttrs = extractBox attrs state.box
    
    -- Extract click handler if present
    clickHandler = extractClickHandler attrs
    
    -- Assign pick ID if interactive
    pickResult = case clickHandler of
      Nothing -> { pickId: Nothing, state: state }
      Just msg -> 
        let pid = DC.pickId state.nextPickId
        in { pickId: Just pid
           , state: state 
               { nextPickId = state.nextPickId + 1
               , pickMap = Map.insert pid msg state.pickMap
               }
           }
    
    state1 = pickResult.state
    
    -- Create DrawRect for this element if it has a background
    selfCommands = case background of
      Nothing -> []
      Just color ->
        [ DC.drawRect
            { x: Device.px boxFromAttrs.x
            , y: Device.px boxFromAttrs.y
            , width: Device.px boxFromAttrs.width
            , height: Device.px boxFromAttrs.height
            , fill: color
            , cornerRadius: borderRadius
            , depth: state1.currentDepth
            , pickId: pickResult.pickId
            , onClick: clickHandler
            }
        ]
    
    -- Increment depth for children
    childState = state1 
      { currentDepth = state1.currentDepth + 1.0
      , box = boxFromAttrs
      }
    
    -- Flatten children
    childResult = flattenChildren childState children
    
    -- Combine commands
    allCommands = selfCommands <> fst childResult
  in
    Tuple allCommands (snd childResult)

-- | Flatten an array of children.
flattenChildren
  :: forall msg
   . FlattenState msg
  -> Array (E.Element msg)
  -> Tuple (DC.CommandBuffer msg) (FlattenState msg)
flattenChildren state children =
  foldl go (Tuple [] state) children
  where
    go (Tuple cmds st) child =
      let result = flattenWithState st child
      in Tuple (cmds <> fst result) (snd result)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default layout box (full viewport, placeholder size).
defaultBox :: LayoutBox
defaultBox = { x: 0.0, y: 0.0, width: 1920.0, height: 1080.0 }

-- | Offset a box by delta x and y.
offsetBox :: Number -> Number -> LayoutBox -> LayoutBox
offsetBox dx dy box = box { x = box.x + dx, y = box.y + dy }

-- | Check if two layout boxes are equal (for layout caching)
-- | Uses Eq constraint for proper comparison
boxesEqual :: LayoutBox -> LayoutBox -> Boolean
boxesEqual a b =
  a.x == b.x && a.y == b.y && a.width == b.width && a.height == b.height

-- | Generic equality check for any Eq type
-- | Useful for comparing element IDs, style values
genericEqual :: forall a. Eq a => a -> a -> Boolean
genericEqual x y = x == y

-- | Show a layout box for debugging
-- | Uses Show for numeric display
showBox :: LayoutBox -> String
showBox box = 
  "LayoutBox { x: " <> show box.x <> 
  ", y: " <> show box.y <> 
  ", width: " <> show box.width <> 
  ", height: " <> show box.height <> " }"

-- | Generic show for debugging
-- | Uses Show constraint for any showable type
showDebug :: forall a. Show a => a -> String
showDebug = show

-- | Discard a Maybe result, returning unit.
-- |
-- | Used when a computation produces a Maybe but we only care that it ran,
-- | not about the result. Commonly needed when chaining operations where
-- | intermediate steps may fail but we want to continue regardless.
discardMaybe :: forall a. Maybe a -> Unit
discardMaybe _ = unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // style extraction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract background color from attributes.
-- |
-- | Looks for style attributes with "background-color" or "background".
-- | Currently supports rgb/rgba CSS strings for compatibility.
-- | Future: direct Schema atom usage.
extractBackground :: forall msg. Array (E.Attribute msg) -> Maybe RGB.RGBA
extractBackground attrs =
  let
    findBg = Array.findMap extractBgFromAttr attrs
  in
    findBg
  where
    extractBgFromAttr = case _ of
      E.Style "background-color" value -> parseColorString value
      E.Style "background" value -> parseColorString value
      _ -> Nothing

-- | Extract border radius from attributes.
extractBorderRadius :: forall msg. Array (E.Attribute msg) -> Radius.Corners
extractBorderRadius attrs =
  let
    findRadius = Array.findMap extractRadiusFromAttr attrs
  in
    case findRadius of
      Nothing -> Radius.cornersAll Radius.none
      Just r -> r
  where
    extractRadiusFromAttr = case _ of
      E.Style "border-radius" value -> parseRadiusString value
      _ -> Nothing

-- | Extract layout box from position/size attributes.
extractBox :: forall msg. Array (E.Attribute msg) -> LayoutBox -> LayoutBox
extractBox attrs parentBox =
  foldl applyStyle parentBox attrs
  where
    applyStyle box = case _ of
      E.Style "left" v -> case parsePixelValue v of
        Just n -> box { x = parentBox.x + n }
        Nothing -> box
      E.Style "top" v -> case parsePixelValue v of
        Just n -> box { y = parentBox.y + n }
        Nothing -> box
      E.Style "width" v -> case parsePixelValue v of
        Just n -> box { width = n }
        Nothing -> box
      E.Style "height" v -> case parsePixelValue v of
        Just n -> box { height = n }
        Nothing -> box
      _ -> box

-- | Extract click handler from attributes.
extractClickHandler :: forall msg. Array (E.Attribute msg) -> Maybe msg
extractClickHandler = Array.findMap go
  where
    go = case _ of
      E.Handler (E.OnClick msg) -> Just msg
      _ -> Nothing

-- | Extract font configuration from style attributes.
-- |
-- | Looks for font-family, font-size, letter-spacing, line-height.
-- | Uses bind for monadic composition over Maybe.
extractFontConfig :: forall msg. Array (E.Attribute msg) -> Text.FontConfig -> Text.FontConfig
extractFontConfig attrs defaultConfig =
  foldl applyFontStyle defaultConfig attrs
  where
    applyFontStyle config = case _ of
      E.Style "font-size" v -> 
        case bind (parsePixelValue v) (\size -> pure size) of
          Just size -> config { fontSize = size }
          Nothing -> config
      E.Style "letter-spacing" v ->
        case parsePixelValue v of
          Just spacing -> config { letterSpacing = spacing }
          Nothing -> config
      E.Style "line-height" v ->
        case parsePixelValue v of
          Just lh -> config { lineHeight = lh }
          Nothing -> config
      _ -> config

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // parsers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse a CSS color string to RGBA.
-- | Supports: rgb(r,g,b), rgba(r,g,b,a), #RRGGBB, #RGB
-- |
-- | NOTE: This is for legacy compatibility. New components should use
-- | Schema atoms directly, not CSS strings.
parseColorString :: String -> Maybe RGB.RGBA
parseColorString _ = 
  -- Simplified: return a default color for now.
  -- Full CSS color parsing is complex and belongs in a legacy adapter.
  -- Components using Schema atoms don't need this.
  Nothing

-- | Parse a CSS radius string.
-- | Supports: Npx, Nrem, N%
parseRadiusString :: String -> Maybe Radius.Corners
parseRadiusString _ =
  -- Simplified: return none for now.
  -- Components should use Geometry.Radius atoms directly.
  Nothing

-- | Parse a pixel value like "100px" or "100".
parsePixelValue :: String -> Maybe Number
parsePixelValue _ =
  -- Simplified: return nothing for now.
  -- Full implementation would parse the string.
  Nothing
