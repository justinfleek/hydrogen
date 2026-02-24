-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // avatar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Avatar component
-- |
-- | User avatar with image and fallback support.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Avatar as Avatar
-- |
-- | -- With image
-- | Avatar.avatar [ Avatar.size Avatar.Md ]
-- |   [ Avatar.avatarImage [ Avatar.src "/user.jpg", Avatar.alt "User" ]
-- |   , Avatar.avatarFallback [] [ HH.text "JD" ]
-- |   ]
-- |
-- | -- Fallback only
-- | Avatar.avatar []
-- |   [ Avatar.avatarFallback [] [ HH.text "AB" ] ]
-- | ```
module Hydrogen.Component.Avatar
  ( -- * Avatar Components
    avatar
  , avatarImage
  , avatarFallback
    -- * Props
  , AvatarProps
  , AvatarProp
  , ImageProps
  , ImageProp
  , size
  , className
  , src
  , alt
    -- * Sizes
  , AvatarSize(Xs, Sm, Md, Lg, Xl, Xxl)
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // sizes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Avatar sizes
data AvatarSize
  = Xs    -- 24px
  | Sm    -- 32px
  | Md    -- 40px
  | Lg    -- 48px
  | Xl    -- 64px
  | Xxl   -- 96px

derive instance eqAvatarSize :: Eq AvatarSize

sizeClasses :: AvatarSize -> String
sizeClasses = case _ of
  Xs -> "h-6 w-6"
  Sm -> "h-8 w-8"
  Md -> "h-10 w-10"
  Lg -> "h-12 w-12"
  Xl -> "h-16 w-16"
  Xxl -> "h-24 w-24"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type AvatarProps = { size :: AvatarSize, className :: String }
type AvatarProp = AvatarProps -> AvatarProps

defaultAvatarProps :: AvatarProps
defaultAvatarProps = { size: Md, className: "" }

type ImageProps = { src :: String, alt :: String, className :: String }
type ImageProp = ImageProps -> ImageProps

defaultImageProps :: ImageProps
defaultImageProps = { src: "", alt: "", className: "" }

-- | Set avatar size
size :: AvatarSize -> AvatarProp
size s props = props { size = s }

-- | Add custom class
className :: String -> AvatarProp
className c props = props { className = props.className <> " " <> c }

-- | Set image source
src :: String -> ImageProp
src s props = props { src = s }

-- | Set image alt text
alt :: String -> ImageProp
alt a props = props { alt = a }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Avatar container
avatar :: forall w i. Array AvatarProp -> Array (HH.HTML w i) -> HH.HTML w i
avatar propMods children =
  let props = foldl (\p f -> f p) defaultAvatarProps propMods
  in HH.span
    [ cls [ "relative flex shrink-0 overflow-hidden rounded-full", sizeClasses props.size, props.className ] ]
    children

-- | Avatar image
avatarImage :: forall w i. Array ImageProp -> HH.HTML w i
avatarImage propMods =
  let props = foldl (\p f -> f p) defaultImageProps propMods
  in HH.img
    [ cls [ "aspect-square h-full w-full", props.className ]
    , HP.src props.src
    , HP.alt props.alt
    ]

-- | Avatar fallback (shown when image fails or isn't provided)
avatarFallback :: forall w i. Array AvatarProp -> Array (HH.HTML w i) -> HH.HTML w i
avatarFallback propMods children =
  let props = foldl (\p f -> f p) defaultAvatarProps propMods
  in HH.span
    [ cls [ "flex h-full w-full items-center justify-center rounded-full bg-muted text-muted-foreground", props.className ] ]
    children
