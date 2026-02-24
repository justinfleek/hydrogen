-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // divider
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Content divider component
-- |
-- | Visual separators for content sections with support for
-- | horizontal/vertical orientation and text labels.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.Divider as Divider
-- |
-- | -- Horizontal divider (default)
-- | Divider.divider []
-- |
-- | -- Vertical divider
-- | Divider.divider [ Divider.orientation Divider.Vertical ]
-- |
-- | -- Divider with label
-- | Divider.dividerWithLabel [] [ HH.text "OR" ]
-- |
-- | -- Dashed divider
-- | Divider.divider [ Divider.variant Divider.Dashed ]
-- | ```
module Hydrogen.Layout.Divider
  ( -- * Components
    divider
  , dividerWithLabel
    -- * Props
  , DividerProps
  , DividerProp
  , orientation
  , variant
  , spacing
  , color
  , thickness
  , className
    -- * Orientation
  , Orientation(..)
    -- * Variant
  , Variant(..)
    -- * Spacing
  , Spacing(..)
    -- * Thickness
  , Thickness(..)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // orientation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Divider orientation
data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // variant
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Divider style variants
data Variant
  = Solid
  | Dashed
  | Dotted

derive instance eqVariant :: Eq Variant

variantClass :: Variant -> String
variantClass = case _ of
  Solid -> ""
  Dashed -> "border-dashed"
  Dotted -> "border-dotted"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // spacing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spacing around the divider
data Spacing
  = SpaceNone
  | SpaceSm
  | SpaceMd
  | SpaceLg
  | SpaceXl

derive instance eqSpacing :: Eq Spacing

spacingClass :: Orientation -> Spacing -> String
spacingClass orient space = case orient, space of
  Horizontal, SpaceNone -> ""
  Horizontal, SpaceSm -> "my-2"
  Horizontal, SpaceMd -> "my-4"
  Horizontal, SpaceLg -> "my-6"
  Horizontal, SpaceXl -> "my-8"
  Vertical, SpaceNone -> ""
  Vertical, SpaceSm -> "mx-2"
  Vertical, SpaceMd -> "mx-4"
  Vertical, SpaceLg -> "mx-6"
  Vertical, SpaceXl -> "mx-8"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // thickness
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Divider thickness
data Thickness
  = Thin       -- ^ 1px
  | Medium     -- ^ 2px
  | Thick      -- ^ 4px

derive instance eqThickness :: Eq Thickness

thicknessValue :: Thickness -> String
thicknessValue = case _ of
  Thin -> "1px"
  Medium -> "2px"
  Thick -> "4px"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type DividerProps =
  { orientation :: Orientation
  , variant :: Variant
  , spacing :: Spacing
  , color :: Maybe String
  , thickness :: Thickness
  , className :: String
  }

type DividerProp = DividerProps -> DividerProps

defaultProps :: DividerProps
defaultProps =
  { orientation: Horizontal
  , variant: Solid
  , spacing: SpaceMd
  , color: Nothing
  , thickness: Thin
  , className: ""
  }

-- | Set orientation
orientation :: Orientation -> DividerProp
orientation o props = props { orientation = o }

-- | Set variant
variant :: Variant -> DividerProp
variant v props = props { variant = v }

-- | Set spacing
spacing :: Spacing -> DividerProp
spacing s props = props { spacing = s }

-- | Set custom color class
color :: String -> DividerProp
color c props = props { color = Just c }

-- | Set thickness
thickness :: Thickness -> DividerProp
thickness t props = props { thickness = t }

-- | Add custom class
className :: String -> DividerProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simple divider line
divider :: forall w i. Array DividerProp -> HH.HTML w i
divider propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    orientClasses = case props.orientation of
      Horizontal -> "w-full h-0 border-t"
      Vertical -> "h-full w-0 border-l self-stretch"
    
    colorClass = case props.color of
      Just c -> c
      Nothing -> "border-border"
    
    spaceCls = spacingClass props.orientation props.spacing
    variantCls = variantClass props.variant
    
    thicknessStyle = case props.orientation of
      Horizontal -> "border-top-width: " <> thicknessValue props.thickness
      Vertical -> "border-left-width: " <> thicknessValue props.thickness
  in
    HH.hr
      [ cls [ "shrink-0", orientClasses, colorClass, spaceCls, variantCls, props.className ]
      , ARIA.role "separator"
      , HP.style thicknessStyle
      ]

-- | Divider with centered label
dividerWithLabel :: forall w i. Array DividerProp -> Array (HH.HTML w i) -> HH.HTML w i
dividerWithLabel propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    spaceCls = spacingClass props.orientation props.spacing
    
    colorClass = case props.color of
      Just c -> c
      Nothing -> "bg-border"
    
    variantCls = variantClass props.variant
  in
    HH.div
      [ cls [ "flex items-center", spaceCls, props.className ]
      , ARIA.role "separator"
      ]
      [ HH.div [ cls [ "flex-1 h-px", colorClass, variantCls ] ] []
      , HH.span [ cls [ "px-3 text-sm text-muted-foreground shrink-0" ] ] children
      , HH.div [ cls [ "flex-1 h-px", colorClass, variantCls ] ] []
      ]
