-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // reactive // hover-effect/style
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverStyle — Style changes applied on hover.
-- |
-- | ## Design Philosophy
-- |
-- | Describes visual property changes that occur during hover:
-- | - Opacity adjustments
-- | - Background color changes
-- | - Border color changes
-- | - Shadow intensity changes
-- | - Filter effects (brightness, saturation)
-- |
-- | ## Layered Shadows on Hover
-- |
-- | Research finding: best hover shadows use multiple layers:
-- | - Base shadow stays constant
-- | - Additional "lift" shadow appears on hover
-- | - Creates more realistic depth perception

module Hydrogen.Schema.Reactive.HoverEffect.Style
  ( HoverStyle(HoverStyle)
  , OpacityChange(OpacityAbsolute, OpacityRelative, OpacityUnchanged)
  , hoverStyle
  , identityStyle
  , defaultHoverStyle
  , subtleHoverStyle
  , prominentHoverStyle
  , glowHoverStyle
  , dimHoverStyle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // opacity change
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opacity change modes
data OpacityChange
  = OpacityAbsolute Number  -- ^ Set to specific opacity (0.0-1.0)
  | OpacityRelative Number  -- ^ Multiply current opacity
  | OpacityUnchanged        -- ^ Keep current opacity

derive instance eqOpacityChange :: Eq OpacityChange

instance showOpacityChange :: Show OpacityChange where
  show (OpacityAbsolute v) = "opacity:" <> show v
  show (OpacityRelative v) = "opacity*" <> show v
  show OpacityUnchanged = "opacity:unchanged"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hover style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Style changes on hover
newtype HoverStyle = HoverStyle
  { opacity :: OpacityChange        -- ^ Opacity adjustment
  , brightness :: Number            -- ^ Filter brightness (1.0 = normal)
  , saturation :: Number            -- ^ Filter saturation (1.0 = normal)
  , contrast :: Number              -- ^ Filter contrast (1.0 = normal)
  , shadowIntensity :: Number       -- ^ Shadow opacity multiplier (1.0 = normal)
  , shadowSpread :: Number          -- ^ Additional shadow spread in pixels
  , backgroundLighten :: Number     -- ^ Background lightness adjustment (-100 to 100)
  , borderLighten :: Number         -- ^ Border lightness adjustment (-100 to 100)
  }

derive instance eqHoverStyle :: Eq HoverStyle

instance showHoverStyle :: Show HoverStyle where
  show (HoverStyle s) = 
    "HoverStyle(brightness:" <> show s.brightness <> 
    ", shadowIntensity:" <> show s.shadowIntensity <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create hover style with common options
hoverStyle 
  :: { brightness :: Number, shadowIntensity :: Number }
  -> HoverStyle
hoverStyle { brightness: b, shadowIntensity: si } = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: b
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: si
  , shadowSpread: 0.0
  , backgroundLighten: 0.0
  , borderLighten: 0.0
  }

-- | Identity style (no visual changes)
identityStyle :: HoverStyle
identityStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.0
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: 1.0
  , shadowSpread: 0.0
  , backgroundLighten: 0.0
  , borderLighten: 0.0
  }

-- | Default hover style (subtle brightness increase + shadow lift)
-- |
-- | Research finding: 5-10% brightness increase is perceptible
-- | but not jarring. Shadow increase of 20-30% adds depth.
defaultHoverStyle :: HoverStyle
defaultHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.05
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: 1.25
  , shadowSpread: 2.0
  , backgroundLighten: 3.0
  , borderLighten: 0.0
  }

-- | Subtle hover style (minimal change)
subtleHoverStyle :: HoverStyle
subtleHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.02
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: 1.1
  , shadowSpread: 1.0
  , backgroundLighten: 2.0
  , borderLighten: 0.0
  }

-- | Prominent hover style (more noticeable)
prominentHoverStyle :: HoverStyle
prominentHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.1
  , saturation: 1.05
  , contrast: 1.0
  , shadowIntensity: 1.5
  , shadowSpread: 4.0
  , backgroundLighten: 5.0
  , borderLighten: 5.0
  }

-- | Glow hover style (emissive appearance)
glowHoverStyle :: HoverStyle
glowHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.15
  , saturation: 1.1
  , contrast: 1.0
  , shadowIntensity: 2.0
  , shadowSpread: 8.0
  , backgroundLighten: 0.0
  , borderLighten: 10.0
  }

-- | Dim hover style (for secondary elements)
dimHoverStyle :: HoverStyle
dimHoverStyle = HoverStyle
  { opacity: OpacityRelative 0.7
  , brightness: 0.95
  , saturation: 0.9
  , contrast: 1.0
  , shadowIntensity: 0.8
  , shadowSpread: 0.0
  , backgroundLighten: (negate 3.0)
  , borderLighten: 0.0
  }
