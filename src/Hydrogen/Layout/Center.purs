-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // center
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Centering utility component
-- |
-- | Provides flexible centering options for content including horizontal,
-- | vertical, and absolute centering with optional max-width constraints.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.Center as Center
-- |
-- | -- Horizontal center (block-level)
-- | Center.center [ Center.axis Center.Horizontal ]
-- |   [ content ]
-- |
-- | -- Absolute center (both axes)
-- | Center.center [ Center.axis Center.Both ]
-- |   [ modal ]
-- |
-- | -- Centered with max width
-- | Center.center [ Center.maxWidth "640px" ]
-- |   [ narrowContent ]
-- | ```
module Hydrogen.Layout.Center
  ( -- * Component
    center
    -- * Props
  , CenterProps
  , CenterProp
  , axis
  , maxWidth
  , maxWidthClass
  , gutters
  , intrinsic
  , className
    -- * Axis
  , Axis(..)
    -- * Max Width Presets
  , MaxWidth(..)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // axis
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Centering axis
data Axis
  = Horizontal  -- ^ Center horizontally only (mx-auto)
  | Vertical    -- ^ Center vertically only (requires flex parent)
  | Both        -- ^ Center both horizontally and vertically

derive instance eqAxis :: Eq Axis

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // max width
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Preset max-width values
data MaxWidth
  = MaxXs     -- ^ max-w-xs (320px)
  | MaxSm     -- ^ max-w-sm (384px)
  | MaxMd     -- ^ max-w-md (448px)
  | MaxLg     -- ^ max-w-lg (512px)
  | MaxXl     -- ^ max-w-xl (576px)
  | Max2xl    -- ^ max-w-2xl (672px)
  | Max3xl    -- ^ max-w-3xl (768px)
  | Max4xl    -- ^ max-w-4xl (896px)
  | Max5xl    -- ^ max-w-5xl (1024px)
  | Max6xl    -- ^ max-w-6xl (1152px)
  | Max7xl    -- ^ max-w-7xl (1280px)
  | MaxFull   -- ^ max-w-full
  | MaxProse  -- ^ max-w-prose (65ch)

derive instance eqMaxWidth :: Eq MaxWidth

maxWidthToClass :: MaxWidth -> String
maxWidthToClass = case _ of
  MaxXs -> "max-w-xs"
  MaxSm -> "max-w-sm"
  MaxMd -> "max-w-md"
  MaxLg -> "max-w-lg"
  MaxXl -> "max-w-xl"
  Max2xl -> "max-w-2xl"
  Max3xl -> "max-w-3xl"
  Max4xl -> "max-w-4xl"
  Max5xl -> "max-w-5xl"
  Max6xl -> "max-w-6xl"
  Max7xl -> "max-w-7xl"
  MaxFull -> "max-w-full"
  MaxProse -> "max-w-prose"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type CenterProps =
  { axis :: Axis
  , maxWidth :: Maybe MaxWidth
  , customMaxWidth :: Maybe String
  , gutters :: Boolean
  , intrinsic :: Boolean
  , className :: String
  }

type CenterProp = CenterProps -> CenterProps

defaultProps :: CenterProps
defaultProps =
  { axis: Horizontal
  , maxWidth: Nothing
  , customMaxWidth: Nothing
  , gutters: false
  , intrinsic: false
  , className: ""
  }

-- | Set the centering axis
axis :: Axis -> CenterProp
axis a props = props { axis = a }

-- | Set max width using preset
maxWidthClass :: MaxWidth -> CenterProp
maxWidthClass mw props = props { maxWidth = Just mw }

-- | Set custom max width (CSS value)
maxWidth :: String -> CenterProp
maxWidth mw props = props { customMaxWidth = Just mw }

-- | Add horizontal gutters (padding)
gutters :: Boolean -> CenterProp
gutters g props = props { gutters = g }

-- | Use intrinsic centering (based on content width)
intrinsic :: Boolean -> CenterProp
intrinsic i props = props { intrinsic = i }

-- | Add custom class
className :: String -> CenterProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Centering container
center :: forall w i. Array CenterProp -> Array (HH.HTML w i) -> HH.HTML w i
center propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    axisClasses = case props.axis of
      Horizontal -> "mx-auto"
      Vertical -> "flex flex-col items-center justify-center"
      Both -> "flex items-center justify-center"
    
    maxWidthCls = case props.maxWidth of
      Just mw -> maxWidthToClass mw
      Nothing -> ""
    
    gutterClass = if props.gutters then "px-4" else ""
    
    intrinsicClass = if props.intrinsic then "w-fit" else ""
    
    styleAttr = case props.customMaxWidth of
      Just mw -> [ HP.style ("max-width: " <> mw) ]
      Nothing -> []
  in
    HH.div
      ([ cls [ axisClasses, maxWidthCls, gutterClass, intrinsicClass, props.className ] ] <> styleAttr)
      children
