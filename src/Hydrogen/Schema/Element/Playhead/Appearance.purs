-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // element // playhead // appearance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PlayheadAppearance — Visual atoms for playhead surface and effects.
-- |
-- | ## Atoms Included
-- |
-- | - Button fill (solid, gradient)
-- | - Track fill (background, progress, buffered)
-- | - Thumb fill
-- | - Glow effects (hover, active states)
-- | - Shadow (elevation)
-- | - Opacity
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Surface.Fill (Fill, fillSolid)
-- | - Hydrogen.Schema.Color.RGB (RGB, RGBA, rgb, rgba)
-- | - Hydrogen.Schema.Color.Glow (Glow, warmGlow, coolGlow)
-- | - Hydrogen.Schema.Elevation.Shadow (LayeredShadow, noShadow)
-- |
-- | ## Design Philosophy
-- |
-- | Appearance describes HOW the playhead looks, not WHERE it is.
-- | All visual atoms compose from established Schema pillars.

module Hydrogen.Schema.Element.Playhead.Appearance
  ( -- * Playhead Variant
    PlayheadVariant
      ( VariantDefault
      , VariantMinimal
      , VariantFilled
      , VariantOutlined
      , VariantGhost
      )
  
  -- * Playhead Appearance Record
  , PlayheadAppearance
  , defaultAppearance
  , minimalAppearance
  , filledAppearance
  , outlinedAppearance
  , ghostAppearance
  
  -- * Appearance Accessors
  , getButtonFill
  , getTrackBackground
  , getProgressFill
  , getBufferedFill
  , getThumbFill
  , getGlow
  , getShadow
  , getOpacity
  
  -- * Appearance Modifiers
  , setButtonFill
  , setTrackBackground
  , setProgressFill
  , setBufferedFill
  , setThumbFill
  , setGlow
  , setShadow
  , setOpacity
  , enableGlow
  , enablePulse
  
  -- * Color Presets
  , blueProgressFill
  , whiteButtonFill
  , darkButtonFill
  , transparentFill
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Surface.Fill
  ( Fill
  , fillSolid
  , fillNone
  ) as Fill

import Hydrogen.Schema.Color.RGB
  ( RGB
  , RGBA
  , rgb
  , rgba
  ) as Color

import Hydrogen.Schema.Color.Glow
  ( Glow
  , glow
  , warmGlow
  , coolGlow
  , isOff
  ) as Glow

import Hydrogen.Schema.Elevation.Shadow
  ( LayeredShadow
  , BoxShadow
  , boxShadow
  , layered
  , noShadow
  ) as Shadow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // playhead variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Playhead visual variant — semantic visual styles.
-- |
-- | - Default: Dark background, white icons
-- | - Minimal: Transparent, subtle text
-- | - Filled: Solid light background
-- | - Outlined: Transparent with border
-- | - Ghost: Fully transparent, visible on hover
data PlayheadVariant
  = VariantDefault   -- ^ Dark background, high contrast
  | VariantMinimal   -- ^ Transparent, subtle
  | VariantFilled    -- ^ Solid light background
  | VariantOutlined  -- ^ Border only
  | VariantGhost     -- ^ Invisible until hover

derive instance eqPlayheadVariant :: Eq PlayheadVariant
derive instance ordPlayheadVariant :: Ord PlayheadVariant

instance showPlayheadVariant :: Show PlayheadVariant where
  show VariantDefault = "Default"
  show VariantMinimal = "Minimal"
  show VariantFilled = "Filled"
  show VariantOutlined = "Outlined"
  show VariantGhost = "Ghost"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // playhead appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete playhead appearance — all visual properties.
-- |
-- | ## Bounded Values
-- |
-- | - opacity: 0.0-1.0 (clamped)
-- | - borderWidth: 0-10 pixels
-- | - All colors via RGB/RGBA (channels bounded 0-255)
-- | - Glow via Glow type (Kelvin bounded, spread bounded)
type PlayheadAppearance =
  { -- Variant
    variant :: PlayheadVariant        -- ^ Visual style variant
    -- Button appearance
  , buttonFill :: Fill.Fill           -- ^ Button background fill
  , buttonBorderWidth :: Number       -- ^ Button border width (bounded 0-10)
  , buttonBorderColor :: Maybe Color.RGBA -- ^ Button border color
    -- Track appearance
  , trackBackground :: Fill.Fill      -- ^ Track background fill
  , progressFill :: Fill.Fill         -- ^ Progress bar fill
  , bufferedFill :: Fill.Fill         -- ^ Buffered region fill
    -- Thumb appearance
  , thumbFill :: Fill.Fill            -- ^ Thumb/handle fill
  , thumbBorderWidth :: Number        -- ^ Thumb border width
  , thumbBorderColor :: Maybe Color.RGBA -- ^ Thumb border color
    -- Effects
  , glow :: Maybe Glow.Glow           -- ^ Optional glow effect
  , shadow :: Shadow.LayeredShadow    -- ^ Shadow layers
  , pulse :: Boolean                  -- ^ Pulse animation enabled
    -- Opacity
  , opacity :: Number                 -- ^ Overall opacity (bounded 0-1)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blue progress bar fill (blue-500)
blueProgressFill :: Fill.Fill
blueProgressFill = Fill.fillSolid (Color.rgb 59 130 246)

-- | White button fill
whiteButtonFill :: Fill.Fill
whiteButtonFill = Fill.fillSolid (Color.rgb 255 255 255)

-- | Dark button fill (gray-800 at 90% opacity)
darkButtonFill :: Fill.Fill
darkButtonFill = Fill.fillSolid (Color.rgb 31 41 55)

-- | Transparent fill
transparentFill :: Fill.Fill
transparentFill = Fill.fillNone

-- | White with alpha for track background
whiteTrackBackground :: Fill.Fill
whiteTrackBackground = Fill.fillSolid (Color.rgb 255 255 255)  -- Opacity handled separately

-- | White with alpha for buffered region
whiteBufferedFill :: Fill.Fill
whiteBufferedFill = Fill.fillSolid (Color.rgb 255 255 255)  -- 30% opacity applied in rendering

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // default presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default playhead appearance.
-- |
-- | Dark background buttons, blue progress bar, white thumb.
defaultAppearance :: PlayheadAppearance
defaultAppearance =
  { variant: VariantDefault
  , buttonFill: darkButtonFill
  , buttonBorderWidth: 0.0
  , buttonBorderColor: Nothing
  , trackBackground: whiteTrackBackground
  , progressFill: blueProgressFill
  , bufferedFill: whiteBufferedFill
  , thumbFill: whiteButtonFill
  , thumbBorderWidth: 0.0
  , thumbBorderColor: Nothing
  , glow: Nothing
  , shadow: Shadow.noShadow
  , pulse: false
  , opacity: 1.0
  }

-- | Minimal playhead appearance.
-- |
-- | Transparent buttons, subtle colors.
minimalAppearance :: PlayheadAppearance
minimalAppearance = defaultAppearance
  { variant = VariantMinimal
  , buttonFill = transparentFill
  , trackBackground = Fill.fillSolid (Color.rgb 128 128 128)
  , progressFill = Fill.fillSolid (Color.rgb 200 200 200)
  , thumbFill = Fill.fillSolid (Color.rgb 200 200 200)
  }

-- | Filled playhead appearance.
-- |
-- | Solid white/light backgrounds.
filledAppearance :: PlayheadAppearance
filledAppearance = defaultAppearance
  { variant = VariantFilled
  , buttonFill = whiteButtonFill
  }

-- | Outlined playhead appearance.
-- |
-- | Transparent with visible borders.
outlinedAppearance :: PlayheadAppearance
outlinedAppearance = defaultAppearance
  { variant = VariantOutlined
  , buttonFill = transparentFill
  , buttonBorderWidth = 2.0
  , buttonBorderColor = Just (Color.rgba 255 255 255 77)   -- ~30% alpha
  , thumbBorderWidth = 2.0
  , thumbBorderColor = Just (Color.rgba 255 255 255 128)   -- ~50% alpha
  }

-- | Ghost playhead appearance.
-- |
-- | Fully transparent, appears on hover.
ghostAppearance :: PlayheadAppearance
ghostAppearance = defaultAppearance
  { variant = VariantGhost
  , buttonFill = transparentFill
  , opacity = 0.0  -- Runtime handles hover state
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get button fill.
getButtonFill :: PlayheadAppearance -> Fill.Fill
getButtonFill a = a.buttonFill

-- | Get track background fill.
getTrackBackground :: PlayheadAppearance -> Fill.Fill
getTrackBackground a = a.trackBackground

-- | Get progress bar fill.
getProgressFill :: PlayheadAppearance -> Fill.Fill
getProgressFill a = a.progressFill

-- | Get buffered region fill.
getBufferedFill :: PlayheadAppearance -> Fill.Fill
getBufferedFill a = a.bufferedFill

-- | Get thumb fill.
getThumbFill :: PlayheadAppearance -> Fill.Fill
getThumbFill a = a.thumbFill

-- | Get glow effect.
getGlow :: PlayheadAppearance -> Maybe Glow.Glow
getGlow a = a.glow

-- | Get shadow layers.
getShadow :: PlayheadAppearance -> Shadow.LayeredShadow
getShadow a = a.shadow

-- | Get opacity (bounded 0-1).
getOpacity :: PlayheadAppearance -> Number
getOpacity a = Bounded.clampNumber 0.0 1.0 a.opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button fill.
setButtonFill :: Fill.Fill -> PlayheadAppearance -> PlayheadAppearance
setButtonFill fill a = a { buttonFill = fill }

-- | Set track background fill.
setTrackBackground :: Fill.Fill -> PlayheadAppearance -> PlayheadAppearance
setTrackBackground fill a = a { trackBackground = fill }

-- | Set progress bar fill.
setProgressFill :: Fill.Fill -> PlayheadAppearance -> PlayheadAppearance
setProgressFill fill a = a { progressFill = fill }

-- | Set buffered region fill.
setBufferedFill :: Fill.Fill -> PlayheadAppearance -> PlayheadAppearance
setBufferedFill fill a = a { bufferedFill = fill }

-- | Set thumb fill.
setThumbFill :: Fill.Fill -> PlayheadAppearance -> PlayheadAppearance
setThumbFill fill a = a { thumbFill = fill }

-- | Set glow effect.
setGlow :: Glow.Glow -> PlayheadAppearance -> PlayheadAppearance
setGlow g a = a { glow = Just g }

-- | Set shadow layers.
setShadow :: Shadow.LayeredShadow -> PlayheadAppearance -> PlayheadAppearance
setShadow s a = a { shadow = s }

-- | Set opacity (automatically bounded 0-1).
setOpacity :: Number -> PlayheadAppearance -> PlayheadAppearance
setOpacity o a = a { opacity = Bounded.clampNumber 0.0 1.0 o }

-- | Enable glow effect with default blue glow.
-- |
-- | Cool glow at 200 nits, 20px spread.
enableGlow :: PlayheadAppearance -> PlayheadAppearance
enableGlow a = a { glow = Just (Glow.coolGlow 200.0 20.0) }

-- | Enable pulse animation.
enablePulse :: PlayheadAppearance -> PlayheadAppearance
enablePulse a = a { pulse = true }
