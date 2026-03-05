-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // element // accordion // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AccordionGeometry — Spatial and size atoms for accordion layout.
-- |
-- | ## Design Philosophy
-- |
-- | Accordion geometry describes the spatial arrangement of trigger/content
-- | pairs in a vertical stack. Each item has configurable padding, borders,
-- | and sizing.
-- |
-- | ## Layout Model
-- |
-- | ```
-- | ┌────────────────────────────┐
-- | │ ▼ Trigger 1 (header)       │ ← TriggerGeometry
-- | ├────────────────────────────┤
-- | │   Content 1 (body)         │ ← ContentGeometry (when expanded)
-- | ├────────────────────────────┤ ← ItemGeometry (border)
-- | │ ▶ Trigger 2 (header)       │
-- | ├────────────────────────────┤
-- | │ ▶ Trigger 3 (header)       │
-- | └────────────────────────────┘
-- |              ↑
-- |     AccordionGeometry (container)
-- | ```
-- |
-- | ## Verified Atoms
-- |
-- | - Pixel (Dimension.Device) — padding, border width, gap
-- | - Size2D (Geometry.Size) — min/max dimensions

module Hydrogen.Schema.Element.Accordion.Geometry
  ( -- * Accordion Container Geometry
    AccordionGeometry
  , defaultAccordionGeometry
  
  -- * Item Geometry
  , AccordionItemGeometry
  , defaultItemGeometry
  , BorderPosition
      ( BorderTop
      , BorderBottom
      , BorderBoth
      , BorderNone
      )
  
  -- * Trigger Geometry
  , TriggerGeometry
  , defaultTriggerGeometry
  
  -- * Content Geometry
  , ContentGeometry
  , defaultContentGeometry
  
  -- * Chevron Icon Geometry
  , ChevronGeometry
  , defaultChevronGeometry
  
  -- * Accessors
  , getItemGap
  , getItemBorderWidth
  , getTriggerPadding
  , getContentPadding
  , getChevronSize
  
  -- * Modifiers
  , setItemGap
  , setItemBorderWidth
  , setTriggerPaddingX
  , setTriggerPaddingY
  , setContentPaddingX
  , setContentPaddingY
  , setChevronSize
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Prim (Number)

import Hydrogen.Schema.Dimension.Device.Types (Pixel(Pixel)) as Dim
import Hydrogen.Schema.Dimension.Device.Operations (px) as Dim

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // accordion geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container geometry for the entire accordion.
-- |
-- | The accordion is a vertical stack of items with optional gap.
type AccordionGeometry =
  { width :: Number              -- ^ Container width (pixels, 0 = auto)
  , minWidth :: Number           -- ^ Minimum width (pixels)
  , maxWidth :: Number           -- ^ Maximum width (pixels, 0 = none)
  , itemGap :: Dim.Pixel         -- ^ Gap between items
  }

-- | Default accordion geometry — full width, no gap.
defaultAccordionGeometry :: AccordionGeometry
defaultAccordionGeometry =
  { width: 0.0                   -- Auto width
  , minWidth: 0.0
  , maxWidth: 0.0                -- No max
  , itemGap: Dim.px 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // item geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geometry for a single accordion item (trigger + content pair).
type AccordionItemGeometry =
  { borderWidth :: Dim.Pixel     -- ^ Border width between items
  , borderPosition :: BorderPosition
  }

-- | Where the border appears on an item.
data BorderPosition
  = BorderTop
  | BorderBottom
  | BorderBoth
  | BorderNone

derive instance eqBorderPosition :: Eq BorderPosition

instance showBorderPosition :: Show BorderPosition where
  show BorderTop = "top"
  show BorderBottom = "bottom"
  show BorderBoth = "both"
  show BorderNone = "none"

-- | Default item geometry — 1px bottom border.
defaultItemGeometry :: AccordionItemGeometry
defaultItemGeometry =
  { borderWidth: Dim.px 1.0
  , borderPosition: BorderBottom
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // trigger geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geometry for the trigger (clickable header).
type TriggerGeometry =
  { paddingX :: Dim.Pixel       -- ^ Horizontal padding
  , paddingY :: Dim.Pixel       -- ^ Vertical padding
  , height :: Number             -- ^ Height (pixels, 0 = auto)
  , minHeight :: Number          -- ^ Minimum height
  }

-- | Default trigger geometry.
defaultTriggerGeometry :: TriggerGeometry
defaultTriggerGeometry =
  { paddingX: Dim.px 0.0
  , paddingY: Dim.px 16.0
  , height: 0.0                  -- Auto height
  , minHeight: 44.0              -- Touch target minimum
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // content geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geometry for the content area (collapsible body).
type ContentGeometry =
  { paddingX :: Dim.Pixel       -- ^ Horizontal padding
  , paddingY :: Dim.Pixel       -- ^ Vertical padding
  , paddingBottom :: Dim.Pixel  -- ^ Extra bottom padding
  }

-- | Default content geometry.
defaultContentGeometry :: ContentGeometry
defaultContentGeometry =
  { paddingX: Dim.px 0.0
  , paddingY: Dim.px 0.0
  , paddingBottom: Dim.px 16.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // chevron geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geometry for the chevron icon in the trigger.
type ChevronGeometry =
  { size :: Dim.Pixel           -- ^ Icon size (width and height)
  , strokeWidth :: Number        -- ^ Stroke width for the chevron
  }

-- | Default chevron geometry.
defaultChevronGeometry :: ChevronGeometry
defaultChevronGeometry =
  { size: Dim.px 16.0
  , strokeWidth: 2.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get gap between items.
getItemGap :: AccordionGeometry -> Dim.Pixel
getItemGap geo = geo.itemGap

-- | Get item border width.
getItemBorderWidth :: AccordionItemGeometry -> Dim.Pixel
getItemBorderWidth geo = geo.borderWidth

-- | Get trigger padding as (x, y).
getTriggerPadding :: TriggerGeometry -> { x :: Dim.Pixel, y :: Dim.Pixel }
getTriggerPadding geo = { x: geo.paddingX, y: geo.paddingY }

-- | Get content padding as (x, y).
getContentPadding :: ContentGeometry -> { x :: Dim.Pixel, y :: Dim.Pixel }
getContentPadding geo = { x: geo.paddingX, y: geo.paddingY }

-- | Get chevron size.
getChevronSize :: ChevronGeometry -> Dim.Pixel
getChevronSize geo = geo.size

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set gap between items.
setItemGap :: Dim.Pixel -> AccordionGeometry -> AccordionGeometry
setItemGap gap geo = geo { itemGap = gap }

-- | Set item border width.
setItemBorderWidth :: Dim.Pixel -> AccordionItemGeometry -> AccordionItemGeometry
setItemBorderWidth w geo = geo { borderWidth = w }

-- | Set trigger horizontal padding.
setTriggerPaddingX :: Dim.Pixel -> TriggerGeometry -> TriggerGeometry
setTriggerPaddingX px geo = geo { paddingX = px }

-- | Set trigger vertical padding.
setTriggerPaddingY :: Dim.Pixel -> TriggerGeometry -> TriggerGeometry
setTriggerPaddingY py geo = geo { paddingY = py }

-- | Set content horizontal padding.
setContentPaddingX :: Dim.Pixel -> ContentGeometry -> ContentGeometry
setContentPaddingX px geo = geo { paddingX = px }

-- | Set content vertical padding.
setContentPaddingY :: Dim.Pixel -> ContentGeometry -> ContentGeometry
setContentPaddingY py geo = geo { paddingY = py }

-- | Set chevron size.
setChevronSize :: Dim.Pixel -> ChevronGeometry -> ChevronGeometry
setChevronSize s geo = geo { size = s }
