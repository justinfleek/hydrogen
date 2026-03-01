-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // carousel // render // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Render Types — Configuration types for carousel rendering.
-- |
-- | ## Design Philosophy
-- |
-- | CarouselConfig combines all sub-configurations (navigation, transition,
-- | effects, layout) into a single record. defaultConfig provides sensible
-- | defaults for all options.
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Navigation (NavigationConfig)
-- | - Carousel.Transitions (TransitionConfig)
-- | - Carousel.Effects (SlideEffects)
-- | - Carousel.Types (LayoutPath)

module Hydrogen.Element.Compound.Carousel.Render.Types
  ( -- * Config Type
    CarouselConfig
  
  -- * Default Config
  , defaultConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Carousel.Types 
  ( LayoutPath
      ( PathLinear
      )
  )
import Hydrogen.Element.Compound.Carousel.Navigation 
  ( NavigationConfig
  , defaultNavigation
  )
import Hydrogen.Element.Compound.Carousel.Transitions 
  ( TransitionConfig
  , defaultTransition
  )
import Hydrogen.Element.Compound.Carousel.Effects 
  ( SlideEffects
  , defaultEffects
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // carousel config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete carousel configuration
-- |
-- | Combines all sub-configurations into a unified record:
-- | - navigation: Arrow, dot, progress, thumbnail controls
-- | - transition: Animation timing and easing
-- | - effects: Visual effects (opacity, scale, blur, etc.)
-- | - layoutPath: Spatial arrangement of slides
-- | - loop: Whether to wrap around at ends
-- | - autoplayInterval: Auto-advance timing (0 = disabled)
-- | - cssClass: Additional CSS classes
type CarouselConfig =
  { navigation :: NavigationConfig
  , transition :: TransitionConfig
  , effects :: SlideEffects
  , layoutPath :: LayoutPath      -- spatial arrangement of slides
  , loop :: Boolean
  , autoplayInterval :: Int      -- milliseconds, 0 = no autoplay
  , cssClass :: String           -- additional CSS class
  }

-- | Default carousel configuration
-- |
-- | Provides sensible defaults:
-- | - Linear layout (traditional horizontal carousel)
-- | - Loop enabled
-- | - No autoplay
-- | - Default navigation, transition, and effects
defaultConfig :: CarouselConfig
defaultConfig =
  { navigation: defaultNavigation
  , transition: defaultTransition
  , effects: defaultEffects
  , layoutPath: PathLinear
  , loop: true
  , autoplayInterval: 0
  , cssClass: ""
  }
