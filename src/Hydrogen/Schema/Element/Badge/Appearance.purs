-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // element // badge // appearance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BadgeAppearance — Pure composition of verified Schema pillar atoms.
-- |
-- | ## Design Philosophy
-- |
-- | Badge appearance is ONLY a composition of existing verified atoms from the
-- | 38 Schema pillars. No new types are created here — everything references
-- | Lean4-verified atoms.
-- |
-- | ## Compositor Model (After Effects style)
-- |
-- | Badge renders as a composition of layers:
-- | 1. Shadow (Elevation.Shadow)
-- | 2. Fill (Surface.Fill — solid, gradient, diffusion, FBM)
-- | 3. Border (Geometry.Border — uses Geometry.Stroke, Dimension.Stroke)
-- | 4. Content (Typography atoms for text, icons)
-- | 5. Transform (Motion.Transform — 2D/3D)
-- | 6. Animation (Motion.KeyframeAnimation with Temporal.Easing)
-- | 7. Effects (Motion.Effects — blur, glow, distortion)
-- | 8. Lottie (Motion.Lottie — particle overlays)
-- |
-- | ## All imports are from existing verified pillars

module Hydrogen.Schema.Element.Badge.Appearance
  ( -- * Badge Appearance Record
    BadgeAppearance
  , defaultAppearance
  
  -- * Appearance Variants
  , primaryAppearance
  , secondaryAppearance
  , successAppearance
  , warningAppearance
  , dangerAppearance
  , glowingAppearance
  , outlineAppearance
  
  -- * Accessors
  , appFill
  , appBorder
  , appShadow
  , appTransform
  , appAnimation
  , appLottie
  , appEffects
  , appTextColor
  , appOpacity
  
  -- * Modifiers
  , setFill
  , setBorder
  , setShadow
  , setTransform
  , setAnimation
  , setLottie
  , addEffect
  , setTextColor
  , setOpacity
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array as Array

-- Surface pillar — fills
import Hydrogen.Schema.Surface.Fill 
  ( Fill
  , fillSolid
  , fillNone
  ) as Fill

-- Geometry pillar — borders (composes Stroke atoms)
import Hydrogen.Schema.Geometry.Border 
  ( Border
  , borderNone
  , borderUniform
  ) as Border

import Hydrogen.Schema.Geometry.Stroke
  ( StrokeStyle(StyleSolid)
  ) as Stroke

import Hydrogen.Schema.Dimension.Stroke
  ( strokeWidthThin
  ) as DimStroke

-- Elevation pillar — shadows
import Hydrogen.Schema.Elevation.Shadow 
  ( LayeredShadow
  , noShadow
  , elevatedShadow
  ) as Shadow

-- Color pillar
import Hydrogen.Schema.Color.RGB 
  ( RGB
  , RGBA
  , rgb
  , rgba
  ) as Color

-- Motion pillar — transforms
import Hydrogen.Schema.Motion.Transform 
  ( LayerTransform2D
  , defaultTransform2D
  ) as Transform

-- Motion pillar — keyframe animation
import Hydrogen.Schema.Motion.KeyframeAnimation
  ( KeyframeAnimation
  ) as Anim

-- Motion pillar — Lottie
import Hydrogen.Schema.Motion.Lottie
  ( LottieSource
  , LottiePlayback
  ) as Lottie

-- Motion pillar — effects stack
import Hydrogen.Schema.Motion.Effects
  ( EffectInstance
  ) as Effects

-- Motion pillar — opacity (from Transform)
import Hydrogen.Schema.Motion.Transform
  ( Opacity
  , opacityFull
  , mkOpacity
  , getOpacityValue
  ) as Opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // badge appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete badge appearance — composition of pillar atoms.
-- |
-- | Every field is a verified atom from Schema pillars.
-- | No new types are defined in this module.
type BadgeAppearance =
  { -- Surface (Surface.Fill)
    fill :: Fill.Fill
    
  -- Border (Geometry.Border → Geometry.Stroke + Dimension.Stroke + Color)
  , border :: Border.Border
    
  -- Elevation (Elevation.Shadow)
  , shadow :: Shadow.LayeredShadow
    
  -- Transform (Motion.Transform)
  , transform :: Transform.LayerTransform2D
    
  -- Animation (Motion.KeyframeAnimation)
  , animation :: Maybe Anim.KeyframeAnimation
    
  -- Lottie overlay (Motion.Lottie)
  , lottie :: Maybe { source :: Lottie.LottieSource, playback :: Lottie.LottiePlayback }
    
  -- Effects stack (Motion.Effects)
  , effects :: Array Effects.EffectInstance
    
  -- Text color (Color.RGB)
  , textColor :: Color.RGB
    
  -- Opacity (Motion.Transform.Opacity)
  , opacity :: Opacity.Opacity
  }

-- | Default badge appearance.
defaultAppearance :: BadgeAppearance
defaultAppearance =
  { fill: Fill.fillSolid (Color.rgb 59 130 246)  -- Blue 500
  , border: Border.borderNone
  , shadow: Shadow.elevatedShadow 2
  , transform: Transform.defaultTransform2D
  , animation: Nothing
  , lottie: Nothing
  , effects: []
  , textColor: Color.rgb 255 255 255  -- White
  , opacity: Opacity.opacityFull
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // appearance variants
-- ═════════════════════════════════════════════════════════════════════════════

primaryAppearance :: BadgeAppearance
primaryAppearance = defaultAppearance

secondaryAppearance :: BadgeAppearance
secondaryAppearance = defaultAppearance
  { fill = Fill.fillSolid (Color.rgb 107 114 128) }

successAppearance :: BadgeAppearance
successAppearance = defaultAppearance
  { fill = Fill.fillSolid (Color.rgb 34 197 94) }

warningAppearance :: BadgeAppearance
warningAppearance = defaultAppearance
  { fill = Fill.fillSolid (Color.rgb 245 158 11)
  , textColor = Color.rgb 0 0 0
  }

dangerAppearance :: BadgeAppearance
dangerAppearance = defaultAppearance
  { fill = Fill.fillSolid (Color.rgb 239 68 68) }

glowingAppearance :: BadgeAppearance
glowingAppearance = defaultAppearance
  { shadow = Shadow.elevatedShadow 8 }

outlineAppearance :: BadgeAppearance
outlineAppearance = defaultAppearance
  { fill = Fill.fillNone
  , border = Border.borderUniform
      { width: DimStroke.strokeWidthThin
      , style: Stroke.StyleSolid
      , color: Color.rgba 59 130 246 100
      }
  , textColor = Color.rgb 59 130 246
  , shadow = Shadow.noShadow
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

appFill :: BadgeAppearance -> Fill.Fill
appFill a = a.fill

appBorder :: BadgeAppearance -> Border.Border
appBorder a = a.border

appShadow :: BadgeAppearance -> Shadow.LayeredShadow
appShadow a = a.shadow

appTransform :: BadgeAppearance -> Transform.LayerTransform2D
appTransform a = a.transform

appAnimation :: BadgeAppearance -> Maybe Anim.KeyframeAnimation
appAnimation a = a.animation

appLottie :: BadgeAppearance -> Maybe { source :: Lottie.LottieSource, playback :: Lottie.LottiePlayback }
appLottie a = a.lottie

appEffects :: BadgeAppearance -> Array Effects.EffectInstance
appEffects a = a.effects

appTextColor :: BadgeAppearance -> Color.RGB
appTextColor a = a.textColor

appOpacity :: BadgeAppearance -> Opacity.Opacity
appOpacity a = a.opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

setFill :: Fill.Fill -> BadgeAppearance -> BadgeAppearance
setFill f a = a { fill = f }

setBorder :: Border.Border -> BadgeAppearance -> BadgeAppearance
setBorder b a = a { border = b }

setShadow :: Shadow.LayeredShadow -> BadgeAppearance -> BadgeAppearance
setShadow s a = a { shadow = s }

setTransform :: Transform.LayerTransform2D -> BadgeAppearance -> BadgeAppearance
setTransform t a = a { transform = t }

setAnimation :: Anim.KeyframeAnimation -> BadgeAppearance -> BadgeAppearance
setAnimation anim a = a { animation = Just anim }

setLottie :: Lottie.LottieSource -> Lottie.LottiePlayback -> BadgeAppearance -> BadgeAppearance
setLottie source playback a = a { lottie = Just { source, playback } }

addEffect :: Effects.EffectInstance -> BadgeAppearance -> BadgeAppearance
addEffect e a = a { effects = Array.snoc a.effects e }

setTextColor :: Color.RGB -> BadgeAppearance -> BadgeAppearance
setTextColor c a = a { textColor = c }

setOpacity :: Number -> BadgeAppearance -> BadgeAppearance
setOpacity o a = a { opacity = Opacity.mkOpacity o }
