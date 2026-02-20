-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // container
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Responsive container component
-- |
-- | Provides max-width constrained containers with responsive padding
-- | and optional fluid mode. Based on common layout patterns.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.Container as Container
-- |
-- | -- Default container (centered, max-width, responsive padding)
-- | Container.container []
-- |   [ pageContent ]
-- |
-- | -- Narrow container for readable content
-- | Container.container [ Container.size Container.Narrow ]
-- |   [ articleContent ]
-- |
-- | -- Fluid container (full width with padding)
-- | Container.container [ Container.fluid true ]
-- |   [ fullWidthContent ]
-- |
-- | -- Custom padding
-- | Container.container [ Container.padding Container.PaddingLg ]
-- |   [ content ]
-- | ```
module Hydrogen.Layout.Container
  ( -- * Component
    container
    -- * Props
  , ContainerProps
  , ContainerProp
  , size
  , padding
  , fluid
  , centered
  , className
    -- * Size Presets
  , Size(..)
    -- * Padding Presets
  , Padding(..)
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // size
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Container size presets
data Size
  = ExtraSmall   -- ^ max-w-screen-xs (480px)
  | Small        -- ^ max-w-screen-sm (640px)
  | Medium       -- ^ max-w-screen-md (768px)
  | Large        -- ^ max-w-screen-lg (1024px)
  | ExtraLarge   -- ^ max-w-screen-xl (1280px)
  | TwoXL        -- ^ max-w-screen-2xl (1536px)
  | Full         -- ^ No max-width constraint
  | Narrow       -- ^ max-w-2xl (672px) - good for reading
  | Wide         -- ^ max-w-7xl (1280px) - default for apps

derive instance eqSize :: Eq Size

sizeClass :: Size -> String
sizeClass = case _ of
  ExtraSmall -> "max-w-screen-sm"
  Small -> "max-w-screen-sm"
  Medium -> "max-w-screen-md"
  Large -> "max-w-screen-lg"
  ExtraLarge -> "max-w-screen-xl"
  TwoXL -> "max-w-screen-2xl"
  Full -> ""
  Narrow -> "max-w-2xl"
  Wide -> "max-w-7xl"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // padding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Padding presets with responsive values
data Padding
  = PaddingNone   -- ^ No padding
  | PaddingSm     -- ^ Small padding
  | PaddingMd     -- ^ Medium padding (default)
  | PaddingLg     -- ^ Large padding
  | PaddingXl     -- ^ Extra large padding

derive instance eqPadding :: Eq Padding

paddingClass :: Padding -> String
paddingClass = case _ of
  PaddingNone -> ""
  PaddingSm -> "px-2 sm:px-3"
  PaddingMd -> "px-4 sm:px-6 lg:px-8"
  PaddingLg -> "px-6 sm:px-8 lg:px-12"
  PaddingXl -> "px-8 sm:px-12 lg:px-16"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type ContainerProps =
  { size :: Size
  , padding :: Padding
  , fluid :: Boolean
  , centered :: Boolean
  , className :: String
  }

type ContainerProp = ContainerProps -> ContainerProps

defaultProps :: ContainerProps
defaultProps =
  { size: Wide
  , padding: PaddingMd
  , fluid: false
  , centered: true
  , className: ""
  }

-- | Set the container size
size :: Size -> ContainerProp
size s props = props { size = s }

-- | Set padding
padding :: Padding -> ContainerProp
padding p props = props { padding = p }

-- | Enable fluid mode (full width)
fluid :: Boolean -> ContainerProp
fluid f props = props { fluid = f }

-- | Center the container
centered :: Boolean -> ContainerProp
centered c props = props { centered = c }

-- | Add custom class
className :: String -> ContainerProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Responsive container
-- |
-- | Provides a centered, max-width constrained container with responsive
-- | horizontal padding. The container adapts to different screen sizes.
container :: forall w i. Array ContainerProp -> Array (HH.HTML w i) -> HH.HTML w i
container propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    sizeCls = if props.fluid then "" else sizeClass props.size
    paddingCls = paddingClass props.padding
    centerCls = if props.centered then "mx-auto" else ""
    widthCls = if props.fluid then "w-full" else "w-full"
  in
    HH.div
      [ cls [ widthCls, sizeCls, paddingCls, centerCls, props.className ] ]
      children
