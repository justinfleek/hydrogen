-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // tour // animation // css
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CSS Generation for Animations
-- |
-- | This module provides functions to convert animation descriptions to CSS.
-- | The generated CSS can be used for static stylesheets or inline styles.
-- |
-- | ## Output Formats
-- |
-- | - animationToCss: CSS animation property value
-- | - keyframesToCss: @keyframes rule definitions
-- |
-- | ## Notes
-- |
-- | Spring animations require JavaScript runtime and cannot be represented
-- | in pure CSS. The CSS output provides a fallback approximation.

module Hydrogen.Tour.Animation.Css
  ( -- * CSS Generation
    animationToCss
  , keyframesToCss
  ) where

import Prelude
  ( show
  , (<>)
  )

import Data.Array (intercalate, mapWithIndex)

import Hydrogen.Tour.Animation.Easing (easingToCss)
import Hydrogen.Tour.Animation.Types
  ( TourAnimation(AnimFade, AnimSlide, AnimScale, AnimSpring, AnimComposite)
  )
import Hydrogen.Tour.Types (Milliseconds(Milliseconds), Pixel(Pixel))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // css generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert animation to CSS animation property value
-- |
-- | Returns a value suitable for the `animation` CSS property.
-- | Format: "name duration easing fill-mode"
animationToCss :: TourAnimation -> String
animationToCss = case _ of
  AnimFade cfg ->
    "fade " <> durationToCss cfg.duration <> " " <> easingToCss cfg.easing <> " forwards"
  AnimSlide cfg ->
    "slide " <> durationToCss cfg.duration <> " " <> easingToCss cfg.easing <> " forwards"
  AnimScale cfg ->
    "scale " <> durationToCss cfg.duration <> " " <> easingToCss cfg.easing <> " forwards"
  AnimSpring _ ->
    -- Springs require JS, fallback to CSS transition
    "spring 300ms ease-out forwards"
  AnimComposite _ ->
    -- Composites need JS orchestration
    "composite 300ms ease-out forwards"
  where
  durationToCss :: Milliseconds -> String
  durationToCss (Milliseconds ms) = show ms <> "ms"

-- | Generate keyframe CSS for animations
-- |
-- | Returns a complete @keyframes rule that can be included in a stylesheet.
keyframesToCss :: String -> TourAnimation -> String
keyframesToCss name anim = case anim of
  AnimFade cfg ->
    "@keyframes " <> name <> " {\n" <>
    "  from { opacity: " <> show cfg.opacity.from <> "; }\n" <>
    "  to { opacity: " <> show cfg.opacity.to <> "; }\n" <>
    "}"
  AnimSlide cfg ->
    "@keyframes " <> name <> " {\n" <>
    "  from { transform: translate(" <> pxToCss cfg.translate.fromX <> ", " <> pxToCss cfg.translate.fromY <> "); }\n" <>
    "  to { transform: translate(" <> pxToCss cfg.translate.toX <> ", " <> pxToCss cfg.translate.toY <> "); }\n" <>
    "}"
  AnimScale cfg ->
    "@keyframes " <> name <> " {\n" <>
    "  from { transform: scale(" <> show cfg.scale.from <> "); transform-origin: " <> cfg.transformOrigin <> "; }\n" <>
    "  to { transform: scale(" <> show cfg.scale.to <> "); transform-origin: " <> cfg.transformOrigin <> "; }\n" <>
    "}"
  AnimSpring _ ->
    "/* Spring animations require JavaScript runtime */"
  AnimComposite cfg ->
    intercalate "\n" (mapWithIndex (\i a -> keyframesToCss (name <> "-" <> show i) a) cfg.animations)
  where
  pxToCss :: Pixel -> String
  pxToCss (Pixel p) = show p <> "px"
