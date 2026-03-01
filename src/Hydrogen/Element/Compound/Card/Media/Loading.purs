-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // element // component // card // media // loading
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Media Loading — Loading strategies and placeholder types.
-- |
-- | ## Overview
-- |
-- | This module contains types for controlling media loading behavior,
-- | placeholder display during loading, and autoplay behavior for
-- | video/animation content.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)

module Hydrogen.Element.Compound.Card.Media.Loading
  ( -- * Loading Strategy
    LoadingStrategy
      ( LoadEager
      , LoadLazy
      , LoadOnHover
      )
  
  -- * Media Placeholder
  , MediaPlaceholder
      ( PlaceholderNone
      , PlaceholderColor
      , PlaceholderBlur
      , PlaceholderShimmer
      , PlaceholderSkeleton
      )
  
  -- * Autoplay Behavior
  , AutoplayBehavior
      ( AutoplayNever
      , AutoplayAlways
      , AutoplayOnHover
      , AutoplayInViewport
      )
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // loading strategy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Media loading strategy
data LoadingStrategy
  = LoadEager          -- ^ Load immediately
  | LoadLazy           -- ^ Load when entering viewport
  | LoadOnHover        -- ^ Load when card is hovered

derive instance eqLoadingStrategy :: Eq LoadingStrategy

instance showLoadingStrategy :: Show LoadingStrategy where
  show LoadEager = "eager"
  show LoadLazy = "lazy"
  show LoadOnHover = "hover"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // media placeholder
-- ═════════════════════════════════════════════════════════════════════════════

-- | Placeholder shown while media loads
data MediaPlaceholder
  = PlaceholderNone                -- ^ No placeholder
  | PlaceholderColor String        -- ^ Solid color (hex)
  | PlaceholderBlur String         -- ^ Blurred low-res image URL
  | PlaceholderShimmer             -- ^ Animated shimmer effect
  | PlaceholderSkeleton            -- ^ Skeleton loading state

derive instance eqMediaPlaceholder :: Eq MediaPlaceholder

instance showMediaPlaceholder :: Show MediaPlaceholder where
  show PlaceholderNone = "none"
  show (PlaceholderColor _) = "color"
  show (PlaceholderBlur _) = "blur"
  show PlaceholderShimmer = "shimmer"
  show PlaceholderSkeleton = "skeleton"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // autoplay behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Video/animation autoplay behavior
data AutoplayBehavior
  = AutoplayNever          -- ^ Never autoplay
  | AutoplayAlways         -- ^ Always autoplay (muted required)
  | AutoplayOnHover        -- ^ Play when hovered
  | AutoplayInViewport     -- ^ Play when scrolled into view

derive instance eqAutoplayBehavior :: Eq AutoplayBehavior

instance showAutoplayBehavior :: Show AutoplayBehavior where
  show AutoplayNever = "never"
  show AutoplayAlways = "always"
  show AutoplayOnHover = "hover"
  show AutoplayInViewport = "viewport"
