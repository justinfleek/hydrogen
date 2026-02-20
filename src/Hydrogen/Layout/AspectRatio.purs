-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // aspectratio
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Aspect ratio container component
-- |
-- | Maintains consistent aspect ratios for responsive content like
-- | images, videos, embeds, and other media.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.AspectRatio as AspectRatio
-- |
-- | -- 16:9 video container
-- | AspectRatio.aspectRatio [ AspectRatio.ratio AspectRatio.R16x9 ]
-- |   [ HH.video [ HP.src "video.mp4" ] [] ]
-- |
-- | -- Square image container
-- | AspectRatio.aspectRatio [ AspectRatio.ratio AspectRatio.R1x1 ]
-- |   [ HH.img [ HP.src "avatar.png" ] ]
-- |
-- | -- Custom aspect ratio
-- | AspectRatio.aspectRatio [ AspectRatio.customRatio 21 9 ]
-- |   [ content ]
-- | ```
module Hydrogen.Layout.AspectRatio
  ( -- * Component
    aspectRatio
    -- * Props
  , AspectRatioProps
  , AspectRatioProp
  , ratio
  , customRatio
  , className
    -- * Preset Ratios
  , Ratio(..)
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // ratio
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Preset aspect ratios
data Ratio
  = R1x1      -- ^ Square (1:1)
  | R4x3      -- ^ Standard (4:3)
  | R16x9     -- ^ Widescreen (16:9)
  | R21x9     -- ^ Ultrawide (21:9)
  | R2x3      -- ^ Portrait (2:3)
  | R3x2      -- ^ Photo (3:2)
  | R9x16     -- ^ Vertical video (9:16)
  | Custom Int Int  -- ^ Custom ratio (width, height)

derive instance eqRatio :: Eq Ratio

-- | Get the Tailwind class or custom style for a ratio
ratioClass :: Ratio -> String
ratioClass = case _ of
  R1x1 -> "aspect-square"
  R4x3 -> "aspect-[4/3]"
  R16x9 -> "aspect-video"
  R21x9 -> "aspect-[21/9]"
  R2x3 -> "aspect-[2/3]"
  R3x2 -> "aspect-[3/2]"
  R9x16 -> "aspect-[9/16]"
  Custom w h -> "aspect-[" <> show w <> "/" <> show h <> "]"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type AspectRatioProps =
  { ratio :: Ratio
  , className :: String
  }

type AspectRatioProp = AspectRatioProps -> AspectRatioProps

defaultProps :: AspectRatioProps
defaultProps =
  { ratio: R16x9
  , className: ""
  }

-- | Set the aspect ratio
ratio :: Ratio -> AspectRatioProp
ratio r props = props { ratio = r }

-- | Set a custom aspect ratio
customRatio :: Int -> Int -> AspectRatioProp
customRatio w h props = props { ratio = Custom w h }

-- | Add custom class
className :: String -> AspectRatioProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Aspect ratio container
-- |
-- | Children are positioned to fill the container while maintaining
-- | the specified aspect ratio. The container is responsive and will
-- | scale based on its parent width.
aspectRatio :: forall w i. Array AspectRatioProp -> Array (HH.HTML w i) -> HH.HTML w i
aspectRatio propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ "relative overflow-hidden", ratioClass props.ratio, props.className ] ]
      [ HH.div
          [ cls [ "absolute inset-0 w-full h-full" ] ]
          children
      ]
