-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // gpu // render-effect/presets
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pre-configured effect combinations for common use cases.
-- |
-- | These presets embody design system knowledge: the exact blur radius,
-- | shadow offset, and glow intensity that create polished UI. Use these
-- | as starting points, or compose them for more complex effects.

module Hydrogen.GPU.RenderEffect.Presets
  ( -- * Blur Presets
    subtleBlur
  , heavyBlur
  , backgroundBlur
  , heroBlur
  , centeredZoomBlur
  
  -- * Glow Presets
  , softGlow
  , intenseGlow
  
  -- * Shadow Presets
  , elevatedShadow
  , floatingShadow
  
  -- * Border Presets
  , linearBorder
  , spotlightBorder
  
  -- * Material Presets
  , liquidGlass
  , acrylicGlass
  , filmGrain
  , digitalNoise
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude (negate)

import Hydrogen.GPU.ComputeKernel
  ( BlurQuality(BlurQualityLow, BlurQualityHigh)
  , RadialBlurType(RadialTypeZoom)
  )

import Hydrogen.GPU.RenderEffect.Blur
  ( BlurEffect(BlurGaussian, BlurRadial)
  , GaussianBlur(GaussianBlur)
  , RadialBlur(RadialBlur)
  )

import Hydrogen.GPU.RenderEffect.Border
  ( BorderEffect(BorderConic)
  , ConicBorder(ConicBorder)
  )

import Hydrogen.GPU.RenderEffect.Material (NoiseType(NoiseWhite))

import Hydrogen.GPU.RenderEffect.Core
  ( RenderEffect(EffectBlur, EffectBorder)
  , effectSequence
  )

import Hydrogen.GPU.RenderEffect.Constructors
  ( gaussianBlur
  , outerGlow
  , pulsingGlow
  , boxShadowEffect
  , conicBorder
  , frostedGlass
  , glassEffect
  , noiseOverlay
  , grainEffect
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // blur presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preset: subtle blur (8px)
-- |
-- | Light blur for hover states, subtle depth.
subtleBlur :: RenderEffect
subtleBlur = gaussianBlur 8.0

-- | Preset: heavy blur (32px)
-- |
-- | Strong blur for modal backgrounds, image effects.
heavyBlur :: RenderEffect
heavyBlur = gaussianBlur 32.0

-- | Preset: fast background blur (uses low quality for performance)
-- |
-- | Optimized for large background areas where quality difference is minimal.
backgroundBlur :: RenderEffect
backgroundBlur = EffectBlur (BlurGaussian (GaussianBlur
  { radius: 32.0
  , quality: BlurQualityLow
  }))

-- | Preset: high quality hero blur (uses high quality for detail)
-- |
-- | Best quality for small, prominent elements where blur quality matters.
heroBlur :: RenderEffect
heroBlur = EffectBlur (BlurGaussian (GaussianBlur
  { radius: 8.0
  , quality: BlurQualityHigh
  }))

-- | Preset: zoom blur from center
-- |
-- | Radial zoom blur centered in the element. Good for focus/attention effects.
centeredZoomBlur :: Number -> RenderEffect
centeredZoomBlur amount = EffectBlur (BlurRadial (RadialBlur
  { centerX: 0.5
  , centerY: 0.5
  , amount: amount
  , blurType: RadialTypeZoom
  }))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // glow presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preset: soft glow (subtle outer glow)
-- |
-- | Subtle blue glow for selection, hover states.
softGlow :: RenderEffect
softGlow = outerGlow { r: 59, g: 130, b: 246, a: 0.5 } 12.0 0.4

-- | Preset: intense glow (vibrant pulsing)
-- |
-- | Attention-grabbing cyan pulse for notifications, CTAs.
intenseGlow :: RenderEffect
intenseGlow = pulsingGlow { r: 34, g: 211, b: 238, a: 0.8 } 8.0 24.0 1500.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // shadow presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preset: elevated shadow (Material Design elevation 8)
-- |
-- | Two-layer shadow matching Material Design's elevation 8dp.
elevatedShadow :: RenderEffect
elevatedShadow = effectSequence
  [ boxShadowEffect 0.0 1.0 3.0 0.0 { r: 0, g: 0, b: 0, a: 0.1 }
  , boxShadowEffect 0.0 4.0 6.0 (-1.0) { r: 0, g: 0, b: 0, a: 0.1 }
  ]

-- | Preset: floating shadow (high elevation)
-- |
-- | Three-layer shadow for elements that appear to float above the surface.
floatingShadow :: RenderEffect
floatingShadow = effectSequence
  [ boxShadowEffect 0.0 4.0 6.0 (-1.0) { r: 0, g: 0, b: 0, a: 0.1 }
  , boxShadowEffect 0.0 10.0 15.0 (-3.0) { r: 0, g: 0, b: 0, a: 0.1 }
  , boxShadowEffect 0.0 20.0 25.0 (-5.0) { r: 0, g: 0, b: 0, a: 0.1 }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // border presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preset: Linear-style rotating border
-- |
-- | The signature Linear app effect: a conic gradient border that
-- | rotates slowly, creating a premium, dynamic appearance.
linearBorder :: RenderEffect
linearBorder = conicBorder 1.0
  [ { r: 59, g: 130, b: 246, a: 1.0 }    -- Blue
  , { r: 139, g: 92, b: 246, a: 1.0 }    -- Purple
  , { r: 236, g: 72, b: 153, a: 1.0 }    -- Pink
  , { r: 59, g: 130, b: 246, a: 1.0 }    -- Blue (loop)
  ]
  45.0  -- 45 degrees per second

-- | Preset: mouse-tracking spotlight border
-- |
-- | Border that highlights the area near the cursor, creating
-- | an interactive, responsive feel.
spotlightBorder :: RenderEffect
spotlightBorder = EffectBorder (BorderConic (ConicBorder
  { width: 1.0
  , colors: [ { r: 255, g: 255, b: 255, a: 1.0 }
            , { r: 255, g: 255, b: 255, a: 0.0 }
            , { r: 255, g: 255, b: 255, a: 0.0 }
            ]
  , rotationSpeed: 0.0
  , blurRadius: 12.0
  , mouseTracking: true
  , spotlightAngle: 60.0
  }))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // material presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preset: liquid glass (iOS style)
-- |
-- | The signature iOS glass effect: frosted background with subtle
-- | refraction for a premium, modern appearance.
liquidGlass :: RenderEffect
liquidGlass = effectSequence
  [ frostedGlass 20.0 0.02
  , glassEffect { r: 255, g: 255, b: 255, a: 0.1 } 0.8
  ]

-- | Preset: acrylic glass (Windows style)
-- |
-- | Windows Fluent Design acrylic: heavier blur with noise texture
-- | for a distinct frosted appearance.
acrylicGlass :: RenderEffect
acrylicGlass = effectSequence
  [ frostedGlass 30.0 0.03
  , noiseOverlay NoiseWhite 1.0 0.02
  , glassEffect { r: 245, g: 245, b: 245, a: 0.05 } 0.85
  ]

-- | Preset: film grain (cinematic)
-- |
-- | Subtle animated grain for cinematic, photographic aesthetic.
filmGrain :: RenderEffect
filmGrain = grainEffect 0.1 1.0

-- | Preset: digital noise (glitch aesthetic)
-- |
-- | Heavier noise with visible grain for digital/glitch effects.
digitalNoise :: RenderEffect
digitalNoise = effectSequence
  [ noiseOverlay NoiseWhite 2.0 0.05
  , grainEffect 0.15 0.8
  ]
