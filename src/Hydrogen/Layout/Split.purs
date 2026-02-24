-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // split
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Split pane layout component
-- |
-- | Resizable split panes for editor layouts, IDE panels,
-- | and adjustable content areas.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.Split as Split
-- |
-- | -- Horizontal split (side by side)
-- | Split.split [ Split.direction Split.Horizontal ]
-- |   { primary: leftPanel, secondary: rightPanel }
-- |
-- | -- Vertical split (top/bottom)
-- | Split.split [ Split.direction Split.Vertical ]
-- |   { primary: topPanel, secondary: bottomPanel }
-- |
-- | -- With size constraints
-- | Split.split
-- |   [ Split.direction Split.Horizontal
-- |   , Split.initialSize 30  -- 30%
-- |   , Split.minSize 20
-- |   , Split.maxSize 80
-- |   ]
-- |   { primary: sidebar, secondary: main }
-- |
-- | -- Collapsible
-- | Split.split
-- |   [ Split.collapsible true
-- |   , Split.collapsed false
-- |   , Split.onCollapse \isCollapsed -> ...
-- |   ]
-- |   { primary: panel, secondary: content }
-- | ```
module Hydrogen.Layout.Split
  ( -- * Component
    split
  , splitPane
    -- * Props
  , SplitProps
  , SplitProp
  , SplitPanes
  , direction
  , initialSize
  , minSize
  , maxSize
  , collapsible
  , collapsed
  , gutterSize
  , persist
  , persistKey
  , onResize
  , onCollapse
  , className
    -- * Direction
  , Direction(..)
    -- * Hooks
  , useSplit
  , SplitHandle
  , setSizes
  , collapse
  , expand
  , getSizes
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // direction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Split direction
data Direction
  = Horizontal  -- ^ Side by side
  | Vertical    -- ^ Top and bottom

derive instance eqDirection :: Eq Direction

directionClass :: Direction -> String
directionClass = case _ of
  Horizontal -> "flex-row"
  Vertical -> "flex-col"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Content for split panes
type SplitPanes w i =
  { primary :: HH.HTML w i
  , secondary :: HH.HTML w i
  }

type SplitProps =
  { direction :: Direction
  , initialSize :: Number      -- Percentage (0-100)
  , minSize :: Number          -- Percentage (0-100)
  , maxSize :: Number          -- Percentage (0-100)
  , collapsible :: Boolean
  , collapsed :: Boolean
  , gutterSize :: Int          -- Pixels
  , persist :: Boolean
  , persistKey :: String
  , onResize :: Maybe (Number -> Effect Unit)
  , onCollapse :: Maybe (Boolean -> Effect Unit)
  , className :: String
  }

type SplitProp = SplitProps -> SplitProps

defaultProps :: SplitProps
defaultProps =
  { direction: Horizontal
  , initialSize: 50.0
  , minSize: 10.0
  , maxSize: 90.0
  , collapsible: false
  , collapsed: false
  , gutterSize: 4
  , persist: false
  , persistKey: "split-sizes"
  , onResize: Nothing
  , onCollapse: Nothing
  , className: ""
  }

-- | Set split direction
direction :: Direction -> SplitProp
direction d props = props { direction = d }

-- | Set initial size (percentage)
initialSize :: Number -> SplitProp
initialSize s props = props { initialSize = s }

-- | Set minimum size (percentage)
minSize :: Number -> SplitProp
minSize s props = props { minSize = s }

-- | Set maximum size (percentage)
maxSize :: Number -> SplitProp
maxSize s props = props { maxSize = s }

-- | Enable collapsible pane
collapsible :: Boolean -> SplitProp
collapsible c props = props { collapsible = c }

-- | Set collapsed state
collapsed :: Boolean -> SplitProp
collapsed c props = props { collapsed = c }

-- | Set gutter size in pixels
gutterSize :: Int -> SplitProp
gutterSize s props = props { gutterSize = s }

-- | Enable persistence to localStorage
persist :: Boolean -> SplitProp
persist p props = props { persist = p }

-- | Set persistence key
persistKey :: String -> SplitProp
persistKey k props = props { persistKey = k }

-- | Handle resize events
onResize :: (Number -> Effect Unit) -> SplitProp
onResize f props = props { onResize = Just f }

-- | Handle collapse events
onCollapse :: (Boolean -> Effect Unit) -> SplitProp
onCollapse f props = props { onCollapse = Just f }

-- | Add custom class
className :: String -> SplitProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // FFI
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Split handle for imperative control
foreign import data SplitHandle :: Type

-- | Initialize split layout
foreign import initSplit :: EffectFn1 String SplitHandle

-- | Set pane sizes
foreign import setSizesImpl :: EffectFn2 SplitHandle (Array Number) Unit

-- | Collapse primary pane
foreign import collapseImpl :: EffectFn1 SplitHandle Unit

-- | Expand primary pane
foreign import expandImpl :: EffectFn1 SplitHandle Unit

-- | Get current sizes
foreign import getSizesImpl :: EffectFn1 SplitHandle (Array Number)

-- | Hook for split initialization
useSplit :: String -> Effect SplitHandle
useSplit = runEffectFn1 initSplit

-- | Set pane sizes
setSizes :: SplitHandle -> Array Number -> Effect Unit
setSizes = runEffectFn2 setSizesImpl

-- | Collapse primary pane
collapse :: SplitHandle -> Effect Unit
collapse = runEffectFn1 collapseImpl

-- | Expand primary pane
expand :: SplitHandle -> Effect Unit
expand = runEffectFn1 expandImpl

-- | Get current sizes
getSizes :: SplitHandle -> Effect (Array Number)
getSizes = runEffectFn1 getSizesImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Split pane container
-- |
-- | Provides a resizable split layout with draggable divider.
-- | Supports horizontal and vertical orientations, min/max constraints,
-- | and optional persistence of sizes.
split :: forall w i. Array SplitProp -> SplitPanes w i -> HH.HTML w i
split propMods panes =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    primarySize = if props.collapsed then 0.0 else props.initialSize
    secondarySize = 100.0 - primarySize
    
    gutterCursor = case props.direction of
      Horizontal -> "cursor-col-resize"
      Vertical -> "cursor-row-resize"
    
    gutterOrientation = case props.direction of
      Horizontal -> "w-[" <> show props.gutterSize <> "px] h-full"
      Vertical -> "h-[" <> show props.gutterSize <> "px] w-full"
    
    primaryStyle = case props.direction of
      Horizontal -> "width: " <> show primarySize <> "%"
      Vertical -> "height: " <> show primarySize <> "%"
    
    secondaryStyle = case props.direction of
      Horizontal -> "width: " <> show secondarySize <> "%"
      Vertical -> "height: " <> show secondarySize <> "%"
  in
    HH.div
      [ cls [ "flex h-full w-full", directionClass props.direction, props.className ]
      , HP.attr (HH.AttrName "data-split") "true"
      , HP.attr (HH.AttrName "data-direction") (if props.direction == Horizontal then "horizontal" else "vertical")
      , HP.attr (HH.AttrName "data-min-size") (show props.minSize)
      , HP.attr (HH.AttrName "data-max-size") (show props.maxSize)
      , HP.attr (HH.AttrName "data-persist") (if props.persist then props.persistKey else "")
      ]
      [ -- Primary pane
        HH.div
          [ cls [ "overflow-auto shrink-0" ]
          , HP.style primaryStyle
          , HP.attr (HH.AttrName "data-split-pane") "primary"
          ]
          [ panes.primary ]
        -- Gutter
      , HH.div
          [ cls [ "flex items-center justify-center shrink-0 bg-border hover:bg-primary/20 transition-colors select-none"
                , gutterCursor, gutterOrientation
                ]
          , HP.attr (HH.AttrName "data-split-gutter") "true"
          ]
          [ HH.div 
              [ cls [ case props.direction of
                        Horizontal -> "w-0.5 h-8 rounded-full bg-muted-foreground/40"
                        Vertical -> "h-0.5 w-8 rounded-full bg-muted-foreground/40"
                    ] 
              ] 
              []
          ]
        -- Secondary pane
      , HH.div
          [ cls [ "overflow-auto flex-1 min-w-0 min-h-0" ]
          , HP.style secondaryStyle
          , HP.attr (HH.AttrName "data-split-pane") "secondary"
          ]
          [ panes.secondary ]
      ]

-- | Individual split pane wrapper
-- |
-- | Use this for more control over individual panes within a split layout.
splitPane :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
splitPane extraClass children =
  HH.div
    [ cls [ "h-full w-full overflow-auto", extraClass ] ]
    children
