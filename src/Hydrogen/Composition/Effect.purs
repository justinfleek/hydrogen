-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // composition // effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Effect Stack — Visual effects applied to composition layers.
-- |
-- | Effects modify pixels after source generation, before blending.
-- | They stack in order: first effect processes source, second processes
-- | result of first, etc.
-- |
-- | ## Categories
-- |
-- | - Blur/Sharpen: Gaussian, Directional, Radial, Box, Sharpen
-- | - Color: Brightness, Contrast, Hue/Sat, Curves, Levels, Tint
-- | - Distort: Warp, Displacement, Bulge, Pinch, Ripple, Twirl
-- | - Stylize: Glow, Shadow, Emboss, Edge, Posterize
-- | - Generate: Fill, Gradient, Noise overlay
-- | - Time: Echo, Freeze, Posterize Time
-- |
-- | All effect parameters are bounded to prevent invalid states.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - Types: Core Effect ADT and EffectCategory
-- | - Blur: Blur/sharpen spec types
-- | - Color: Color correction spec types
-- | - Distort: Distortion spec types
-- | - Stylize: Stylize effect spec types
-- | - Noise: Noise/grain spec types
-- | - StylizeEffects: Retro/digital aesthetic spec types
-- | - Constructors: Smart constructors for all effects

module Hydrogen.Composition.Effect
  ( module Types
  , module Blur
  , module Color
  , module Distort
  , module Stylize
  , module Noise
  , module StylizeEffects
  , module Constructors
  ) where

import Hydrogen.Composition.Effect.Types as Types
import Hydrogen.Composition.Effect.Blur as Blur
import Hydrogen.Composition.Effect.Color as Color
import Hydrogen.Composition.Effect.Distort as Distort
import Hydrogen.Composition.Effect.Stylize as Stylize
import Hydrogen.Composition.Effect.Noise as Noise
import Hydrogen.Composition.Effect.StylizeEffects as StylizeEffects
import Hydrogen.Composition.Effect.Constructors as Constructors
