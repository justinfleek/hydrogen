-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // element // accordion // appearance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AccordionAppearance — Pure composition of verified Schema pillar atoms.
-- |
-- | ## Design Philosophy
-- |
-- | Accordion appearance is ONLY a composition of existing verified atoms from
-- | the 38 Schema pillars. No new types are created here — everything references
-- | Lean4-verified atoms.
-- |
-- | ## Compositor Model (After Effects style)
-- |
-- | Accordion renders as a composition of layers:
-- | 1. Container fill and border
-- | 2. Item separator lines
-- | 3. Trigger background (default, hover, focus states)
-- | 4. Chevron icon (rotates on expand)
-- | 5. Content area background
-- |
-- | ## Component Structure
-- |
-- | ```
-- | ┌─────────────────────────────────────────┐  ← Container (fill, border)
-- | │ ┌─────────────────────────────────────┐ │
-- | │ │ ▼ Trigger                     [>]  │ │  ← TriggerAppearance
-- | │ └─────────────────────────────────────┘ │
-- | │ ┌─────────────────────────────────────┐ │
-- | │ │   Content (expanded)               │ │  ← ContentAppearance
-- | │ └─────────────────────────────────────┘ │
-- | │─────────────────────────────────────────│  ← Separator
-- | │ ┌─────────────────────────────────────┐ │
-- | │ │ ▶ Trigger 2 (collapsed)       [>]  │ │
-- | │ └─────────────────────────────────────┘ │
-- | └─────────────────────────────────────────┘
-- | ```

module Hydrogen.Schema.Element.Accordion.Appearance
  ( -- * Accordion Appearance Record
    AccordionAppearance
  , defaultAppearance
  
  -- * Trigger Appearance
  , TriggerAppearance
  , defaultTriggerAppearance
  
  -- * Content Appearance
  , ContentAppearance
  , defaultContentAppearance
  
  -- * Chevron Appearance
  , ChevronAppearance
  , defaultChevronAppearance
  
  -- * Separator Appearance
  , SeparatorAppearance
  , defaultSeparatorAppearance
  
  -- * Appearance Variants
  , minimalAppearance
  , borderedAppearance
  , cardAppearance
  , elevatedAppearance
  
  -- * Container Accessors
  , appContainerFill
  , appContainerBorder
  , appContainerShadow
  , appSeparator
  
  -- * Trigger Accessors
  , triggerFill
  , triggerHoverFill
  , triggerFocusFill
  , triggerTextColor
  
  -- * Content Accessors
  , contentFill
  , contentTextColor
  
  -- * Chevron Accessors
  , chevronColor
  , chevronRotation
  
  -- * Container Modifiers
  , setContainerFill
  , setContainerBorder
  , setContainerShadow
  , setSeparator
  
  -- * Trigger Modifiers
  , setTriggerFill
  , setTriggerHoverFill
  , setTriggerFocusFill
  , setTriggerTextColor
  
  -- * Content Modifiers
  , setContentFill
  , setContentTextColor
  
  -- * Chevron Modifiers
  , setChevronColor
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Surface pillar — fills
import Hydrogen.Schema.Surface.Fill 
  ( Fill
  , fillSolid
  , fillNone
  ) as Fill

-- Geometry pillar — borders
import Hydrogen.Schema.Geometry.Border 
  ( Border
  , borderNone
  , borderSimple
  ) as Border

import Hydrogen.Schema.Geometry.Radius
  ( Corners
  , cornersAll
  , none
  ) as Radius

import Hydrogen.Schema.Geometry.Stroke
  ( StrokeStyle(StyleSolid)
  ) as Stroke

import Hydrogen.Schema.Dimension.Stroke
  ( strokeWidthThin
  , strokeWidthHairline
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

-- Motion pillar — transforms (for chevron rotation)
import Hydrogen.Schema.Motion.Transform 
  ( LayerTransform2D
  , defaultTransform2D
  ) as Transform

-- Motion pillar — opacity
import Hydrogen.Schema.Motion.Transform
  ( Opacity
  , opacityFull
  ) as Opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // trigger appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Appearance for the trigger (clickable header).
-- |
-- | Supports three states: default, hover, focus.
type TriggerAppearance =
  { fill :: Fill.Fill              -- ^ Default background
  , hoverFill :: Fill.Fill         -- ^ Background on hover
  , focusFill :: Fill.Fill         -- ^ Background on focus
  , textColor :: Color.RGB         -- ^ Text color
  , hoverTextColor :: Color.RGB    -- ^ Text color on hover
  }

-- | Default trigger appearance — transparent, darkens on hover.
defaultTriggerAppearance :: TriggerAppearance
defaultTriggerAppearance =
  { fill: Fill.fillNone
  , hoverFill: Fill.fillSolid (Color.rgb 245 245 245)  -- Gray 100
  , focusFill: Fill.fillSolid (Color.rgb 239 246 255)  -- Blue 50
  , textColor: Color.rgb 17 24 39                       -- Gray 900
  , hoverTextColor: Color.rgb 17 24 39
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // content appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Appearance for the content area (collapsible body).
type ContentAppearance =
  { fill :: Fill.Fill              -- ^ Background fill
  , textColor :: Color.RGB         -- ^ Text color
  }

-- | Default content appearance — transparent with standard text.
defaultContentAppearance :: ContentAppearance
defaultContentAppearance =
  { fill: Fill.fillNone
  , textColor: Color.rgb 55 65 81  -- Gray 700
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // chevron appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Appearance for the chevron icon.
-- |
-- | The chevron rotates 90° when expanded (rotation handled by animation).
type ChevronAppearance =
  { color :: Color.RGB             -- ^ Stroke color
  , hoverColor :: Color.RGB        -- ^ Stroke color on hover
  , collapsedRotation :: Number    -- ^ Rotation in degrees when collapsed
  , expandedRotation :: Number     -- ^ Rotation in degrees when expanded
  }

-- | Default chevron appearance — gray, rotates 90° on expand.
defaultChevronAppearance :: ChevronAppearance
defaultChevronAppearance =
  { color: Color.rgb 107 114 128   -- Gray 500
  , hoverColor: Color.rgb 55 65 81 -- Gray 700
  , collapsedRotation: 0.0         -- Points right when collapsed
  , expandedRotation: 90.0         -- Points down when expanded
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // separator appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Appearance for separators between items.
type SeparatorAppearance =
  { color :: Color.RGBA            -- ^ Line color (with alpha)
  , visible :: Boolean             -- ^ Whether separator is visible
  }

-- | Default separator — light gray line.
defaultSeparatorAppearance :: SeparatorAppearance
defaultSeparatorAppearance =
  { color: Color.rgba 229 231 235 100  -- Gray 200, full opacity
  , visible: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // accordion appearance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete accordion appearance — composition of pillar atoms.
-- |
-- | Every field is a verified atom from Schema pillars.
type AccordionAppearance =
  { -- Container
    containerFill :: Fill.Fill
  , containerBorder :: Border.Border
  , containerShadow :: Shadow.LayeredShadow
  
  -- Separator between items
  , separator :: SeparatorAppearance
  
  -- Component appearances
  , trigger :: TriggerAppearance
  , content :: ContentAppearance
  , chevron :: ChevronAppearance
  
  -- Opacity
  , opacity :: Opacity.Opacity
  }

-- | Default accordion appearance — minimal, clean.
defaultAppearance :: AccordionAppearance
defaultAppearance =
  { containerFill: Fill.fillNone
  , containerBorder: Border.borderNone
  , containerShadow: Shadow.noShadow
  , separator: defaultSeparatorAppearance
  , trigger: defaultTriggerAppearance
  , content: defaultContentAppearance
  , chevron: defaultChevronAppearance
  , opacity: Opacity.opacityFull
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // appearance variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimal appearance — no borders, subtle separators.
minimalAppearance :: AccordionAppearance
minimalAppearance = defaultAppearance

-- | Bordered appearance — has container border, no shadow.
borderedAppearance :: AccordionAppearance
borderedAppearance = defaultAppearance
  { containerBorder = Border.borderSimple
      { width: DimStroke.strokeWidthThin
      , style: Stroke.StyleSolid
      , color: Color.rgba 229 231 235 100  -- Gray 200
      , corners: Radius.cornersAll Radius.none
      }
  }

-- | Card appearance — filled background, rounded corners implied.
cardAppearance :: AccordionAppearance
cardAppearance = defaultAppearance
  { containerFill = Fill.fillSolid (Color.rgb 255 255 255)  -- White
  , containerBorder = Border.borderSimple
      { width: DimStroke.strokeWidthHairline
      , style: Stroke.StyleSolid
      , color: Color.rgba 229 231 235 100
      , corners: Radius.cornersAll Radius.none
      }
  , containerShadow = Shadow.elevatedShadow 1
  }

-- | Elevated appearance — shadow, card-like.
elevatedAppearance :: AccordionAppearance
elevatedAppearance = defaultAppearance
  { containerFill = Fill.fillSolid (Color.rgb 255 255 255)
  , containerShadow = Shadow.elevatedShadow 4
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // container accessors
-- ═════════════════════════════════════════════════════════════════════════════

appContainerFill :: AccordionAppearance -> Fill.Fill
appContainerFill a = a.containerFill

appContainerBorder :: AccordionAppearance -> Border.Border
appContainerBorder a = a.containerBorder

appContainerShadow :: AccordionAppearance -> Shadow.LayeredShadow
appContainerShadow a = a.containerShadow

appSeparator :: AccordionAppearance -> SeparatorAppearance
appSeparator a = a.separator

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // trigger accessors
-- ═════════════════════════════════════════════════════════════════════════════

triggerFill :: AccordionAppearance -> Fill.Fill
triggerFill a = a.trigger.fill

triggerHoverFill :: AccordionAppearance -> Fill.Fill
triggerHoverFill a = a.trigger.hoverFill

triggerFocusFill :: AccordionAppearance -> Fill.Fill
triggerFocusFill a = a.trigger.focusFill

triggerTextColor :: AccordionAppearance -> Color.RGB
triggerTextColor a = a.trigger.textColor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // content accessors
-- ═════════════════════════════════════════════════════════════════════════════

contentFill :: AccordionAppearance -> Fill.Fill
contentFill a = a.content.fill

contentTextColor :: AccordionAppearance -> Color.RGB
contentTextColor a = a.content.textColor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // chevron accessors
-- ═════════════════════════════════════════════════════════════════════════════

chevronColor :: AccordionAppearance -> Color.RGB
chevronColor a = a.chevron.color

chevronRotation :: AccordionAppearance -> { collapsed :: Number, expanded :: Number }
chevronRotation a = 
  { collapsed: a.chevron.collapsedRotation
  , expanded: a.chevron.expandedRotation
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // container modifiers
-- ═════════════════════════════════════════════════════════════════════════════

setContainerFill :: Fill.Fill -> AccordionAppearance -> AccordionAppearance
setContainerFill f a = a { containerFill = f }

setContainerBorder :: Border.Border -> AccordionAppearance -> AccordionAppearance
setContainerBorder b a = a { containerBorder = b }

setContainerShadow :: Shadow.LayeredShadow -> AccordionAppearance -> AccordionAppearance
setContainerShadow s a = a { containerShadow = s }

setSeparator :: SeparatorAppearance -> AccordionAppearance -> AccordionAppearance
setSeparator s a = a { separator = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // trigger modifiers
-- ═════════════════════════════════════════════════════════════════════════════

setTriggerFill :: Fill.Fill -> AccordionAppearance -> AccordionAppearance
setTriggerFill f a = a { trigger = a.trigger { fill = f } }

setTriggerHoverFill :: Fill.Fill -> AccordionAppearance -> AccordionAppearance
setTriggerHoverFill f a = a { trigger = a.trigger { hoverFill = f } }

setTriggerFocusFill :: Fill.Fill -> AccordionAppearance -> AccordionAppearance
setTriggerFocusFill f a = a { trigger = a.trigger { focusFill = f } }

setTriggerTextColor :: Color.RGB -> AccordionAppearance -> AccordionAppearance
setTriggerTextColor c a = a { trigger = a.trigger { textColor = c } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // content modifiers
-- ═════════════════════════════════════════════════════════════════════════════

setContentFill :: Fill.Fill -> AccordionAppearance -> AccordionAppearance
setContentFill f a = a { content = a.content { fill = f } }

setContentTextColor :: Color.RGB -> AccordionAppearance -> AccordionAppearance
setContentTextColor c a = a { content = a.content { textColor = c } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // chevron modifiers
-- ═════════════════════════════════════════════════════════════════════════════

setChevronColor :: Color.RGB -> AccordionAppearance -> AccordionAppearance
setChevronColor c a = a { chevron = a.chevron { color = c } }

