-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // icons3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen 3D icon set
-- |
-- | Soft isometric 3D icons designed for modern SaaS landing pages and feature
-- | sections. Built on the Icon3D infrastructure with multi-color brand support.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Icon.Icons3D as Icon3D
-- | import Hydrogen.Icon.Icon3D as I3D
-- |
-- | -- Basic usage
-- | Icon3D.check []
-- |
-- | -- With size
-- | Icon3D.check [ I3D.size I3D.Lg ]
-- |
-- | -- With soft material (default for SaaS style)
-- | Icon3D.check [ I3D.material I3D.soft ]
-- |
-- | -- With animation
-- | Icon3D.check [ I3D.animate I3D.Float ]
-- |
-- | -- With custom color
-- | Icon3D.check [ I3D.color "#10b981" ]
-- | ```
module Hydrogen.Icon.Icons3D
  ( -- * Multi-Color Icons (Brand Palette)
    -- | These icons use multiple brand colors for a premium look.
    -- | Set colors via `I3D.palette` or `I3D.style`.
    folderMulti
  , fileMulti
  , homeMulti
  , settingsMulti
  , bellMulti
  , lockMulti
  , mailMulti
  , calendarMulti
  , cameraMulti
  , searchMulti
  , downloadMulti
  , uploadMulti
  , userMulti
  , heartMulti
  , starMulti
  , playMulti
  , micMulti
  , globeMulti
  , terminalMulti
  , cloudMulti
  , alertMulti
  , checkMulti
  , clockMulti
  , chartMulti
  , rocketMulti
    -- * Single-Color Icons (Classic)
    -- * Actions
  , check
  , x
  , plus
  , minus
  , edit
  , trash
  , copy
  , save
  , download
  , upload
  , search
  , filter
  , refresh
    -- * Arrows
  , arrowUp
  , arrowDown
  , arrowLeft
  , arrowRight
  , chevronUp
  , chevronDown
  , chevronLeft
  , chevronRight
  , externalLink
    -- * Status
  , alertCircle
  , alertTriangle
  , info
  , helpCircle
  , checkCircle
  , xCircle
  , clock
  , loader
    -- * Objects
  , file
  , folder
  , folderOpen
  , image
  , calendar
  , mail
  , link
  , globe
  , home
  , settings
  , user
  , users
  , heart
  , star
  , bookmark
  , bell
  , lock
  , unlock
  , key
  , eye
    -- * Media
  , play
  , pause
  , stop
  , volume
  , mic
  , camera
    -- * Layout
  , menu
  , moreHorizontal
  , moreVertical
  , grid
  , list
    -- * Data
  , barChart
  , pieChart
  , trendingUp
  , trendingDown
    -- * Misc
  , sun
  , moon
  , zap
  , cloud
  , wifi
  , power
  , terminal
  , code
  ) where

import Prelude

import Halogen.HTML as HH
import Hydrogen.Icon.Icon3D 
  ( Icon3DProp
  , icon3D
  , icon3DWith
  , iconMulti
  , iconPart
  , primitiveBox
  , primitiveRoundedBox
  , primitiveSphere
  , primitiveCylinder
  , primitiveCapsule
  , primitiveCone
  , primitiveTorus
  , zero3
  , vec3
  , euler
  , BrandSlot(..)
  , MaterialVariant(..)
  )
import Data.Number (pi)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // actions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Checkmark icon — rounded tick mark with soft depth
check :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
check props = icon3DWith props
  [ -- Short arm of checkmark
    primitiveBox 
      { x: 0.15, y: 0.08, z: 0.08 }
      { x: -0.12, y: -0.05, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.7 }
  , -- Long arm of checkmark
    primitiveBox
      { x: 0.35, y: 0.08, z: 0.08 }
      { x: 0.12, y: 0.08, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.5 }
  ]

-- | 3D X / Close icon — crossed bars
x :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
x props = icon3DWith props
  [ -- First diagonal bar
    primitiveBox
      { x: 0.45, y: 0.08, z: 0.08 }
      { x: 0.0, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.785 }
  , -- Second diagonal bar
    primitiveBox
      { x: 0.45, y: 0.08, z: 0.08 }
      { x: 0.0, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.785 }
  ]

-- | 3D Plus icon — crossed perpendicular bars
plus :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
plus props = icon3DWith props
  [ -- Horizontal bar
    primitiveBox
      { x: 0.4, y: 0.1, z: 0.1 }
      zero3
      zero3
  , -- Vertical bar
    primitiveBox
      { x: 0.1, y: 0.4, z: 0.1 }
      zero3
      zero3
  ]

-- | 3D Minus icon — single horizontal bar
minus :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
minus props = icon3D props $
  primitiveBox
    { x: 0.4, y: 0.1, z: 0.1 }
    zero3
    zero3

-- | 3D Edit / Pencil icon — stylized pencil shape
edit :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
edit props = icon3DWith props
  [ -- Pencil body
    primitiveBox
      { x: 0.08, y: 0.35, z: 0.08 }
      { x: 0.0, y: 0.05, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.3 }
  , -- Pencil tip
    primitiveCone
      0.06 0.12
      { x: -0.12, y: -0.15, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.3 }
  , -- Eraser cap
    primitiveBox
      { x: 0.1, y: 0.06, z: 0.1 }
      { x: 0.15, y: 0.25, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.3 }
  ]

-- | 3D Trash / Delete icon — bin with lid
trash :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
trash props = icon3DWith props
  [ -- Bin body (slightly tapered cylinder)
    primitiveCylinder
      0.12 0.15 0.3
      { x: 0.0, y: -0.05, z: 0.0 }
      zero3
  , -- Lid
    primitiveBox
      { x: 0.35, y: 0.04, z: 0.12 }
      { x: 0.0, y: 0.18, z: 0.0 }
      zero3
  , -- Handle
    primitiveBox
      { x: 0.08, y: 0.06, z: 0.08 }
      { x: 0.0, y: 0.24, z: 0.0 }
      zero3
  ]

-- | 3D Copy icon — stacked documents
copy :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
copy props = icon3DWith props
  [ -- Back document
    primitiveBox
      { x: 0.25, y: 0.32, z: 0.03 }
      { x: 0.05, y: 0.05, z: -0.03 }
      zero3
  , -- Front document
    primitiveBox
      { x: 0.25, y: 0.32, z: 0.03 }
      { x: -0.05, y: -0.05, z: 0.03 }
      zero3
  ]

-- | 3D Save icon — floppy disk with label
save :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
save props = icon3DWith props
  [ -- Disk body
    primitiveBox
      { x: 0.35, y: 0.35, z: 0.06 }
      zero3
      zero3
  , -- Label area (slightly raised)
    primitiveBox
      { x: 0.2, y: 0.12, z: 0.02 }
      { x: 0.0, y: 0.08, z: 0.04 }
      zero3
  , -- Metal slider
    primitiveBox
      { x: 0.12, y: 0.08, z: 0.01 }
      { x: 0.0, y: -0.1, z: 0.035 }
      zero3
  ]

-- | 3D Download icon — arrow pointing into tray
download :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
download props = icon3DWith props
  [ -- Arrow shaft
    primitiveBox
      { x: 0.08, y: 0.25, z: 0.08 }
      { x: 0.0, y: 0.05, z: 0.0 }
      zero3
  , -- Arrow head
    primitiveCone
      0.15 0.12
      { x: 0.0, y: -0.1, z: 0.0 }
      { x: pi, y: 0.0, z: 0.0 }
  , -- Tray
    primitiveBox
      { x: 0.4, y: 0.06, z: 0.15 }
      { x: 0.0, y: -0.22, z: 0.0 }
      zero3
  ]

-- | 3D Upload icon — arrow pointing out of tray
upload :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
upload props = icon3DWith props
  [ -- Arrow shaft
    primitiveBox
      { x: 0.08, y: 0.25, z: 0.08 }
      { x: 0.0, y: 0.0, z: 0.0 }
      zero3
  , -- Arrow head
    primitiveCone
      0.15 0.12
      { x: 0.0, y: 0.18, z: 0.0 }
      zero3
  , -- Tray
    primitiveBox
      { x: 0.4, y: 0.06, z: 0.15 }
      { x: 0.0, y: -0.22, z: 0.0 }
      zero3
  ]

-- | 3D Search icon — magnifying glass
search :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
search props = icon3DWith props
  [ -- Glass ring
    primitiveTorus
      0.15 0.03
      { x: -0.05, y: 0.05, z: 0.0 }
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  , -- Handle
    primitiveCylinder
      0.035 0.035 0.2
      { x: 0.12, y: -0.12, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.785 }
  ]

-- | 3D Filter icon — funnel shape
filter :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
filter props = icon3DWith props
  [ -- Funnel top (wide cylinder)
    primitiveCylinder
      0.25 0.1 0.15
      { x: 0.0, y: 0.1, z: 0.0 }
      zero3
  , -- Funnel stem (narrow cylinder)
    primitiveCylinder
      0.05 0.05 0.2
      { x: 0.0, y: -0.12, z: 0.0 }
      zero3
  ]

-- | 3D Refresh icon — circular arrows
refresh :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
refresh props = icon3DWith props
  [ -- Circular arc (approximated with torus segment)
    primitiveTorus
      0.18 0.035
      zero3
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  , -- Arrow head 1
    primitiveCone
      0.06 0.1
      { x: 0.18, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: -pi / 2.0 }
  , -- Arrow head 2
    primitiveCone
      0.06 0.1
      { x: -0.18, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: pi / 2.0 }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // arrows
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Arrow up icon
arrowUp :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
arrowUp props = icon3DWith props
  [ -- Arrow shaft
    primitiveBox
      { x: 0.08, y: 0.3, z: 0.08 }
      { x: 0.0, y: -0.05, z: 0.0 }
      zero3
  , -- Arrow head
    primitiveCone
      0.15 0.15
      { x: 0.0, y: 0.18, z: 0.0 }
      zero3
  ]

-- | 3D Arrow down icon
arrowDown :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
arrowDown props = icon3DWith props
  [ -- Arrow shaft
    primitiveBox
      { x: 0.08, y: 0.3, z: 0.08 }
      { x: 0.0, y: 0.05, z: 0.0 }
      zero3
  , -- Arrow head
    primitiveCone
      0.15 0.15
      { x: 0.0, y: -0.18, z: 0.0 }
      { x: pi, y: 0.0, z: 0.0 }
  ]

-- | 3D Arrow left icon
arrowLeft :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
arrowLeft props = icon3DWith props
  [ -- Arrow shaft
    primitiveBox
      { x: 0.3, y: 0.08, z: 0.08 }
      { x: 0.05, y: 0.0, z: 0.0 }
      zero3
  , -- Arrow head
    primitiveCone
      0.15 0.15
      { x: -0.18, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: pi / 2.0 }
  ]

-- | 3D Arrow right icon
arrowRight :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
arrowRight props = icon3DWith props
  [ -- Arrow shaft
    primitiveBox
      { x: 0.3, y: 0.08, z: 0.08 }
      { x: -0.05, y: 0.0, z: 0.0 }
      zero3
  , -- Arrow head
    primitiveCone
      0.15 0.15
      { x: 0.18, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: -pi / 2.0 }
  ]

-- | 3D Chevron up icon
chevronUp :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
chevronUp props = icon3DWith props
  [ -- Left arm
    primitiveBox
      { x: 0.22, y: 0.06, z: 0.06 }
      { x: -0.08, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.5 }
  , -- Right arm
    primitiveBox
      { x: 0.22, y: 0.06, z: 0.06 }
      { x: 0.08, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.5 }
  ]

-- | 3D Chevron down icon
chevronDown :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
chevronDown props = icon3DWith props
  [ -- Left arm
    primitiveBox
      { x: 0.22, y: 0.06, z: 0.06 }
      { x: -0.08, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.5 }
  , -- Right arm
    primitiveBox
      { x: 0.22, y: 0.06, z: 0.06 }
      { x: 0.08, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.5 }
  ]

-- | 3D Chevron left icon
chevronLeft :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
chevronLeft props = icon3DWith props
  [ -- Top arm
    primitiveBox
      { x: 0.06, y: 0.22, z: 0.06 }
      { x: 0.0, y: 0.08, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.5 }
  , -- Bottom arm
    primitiveBox
      { x: 0.06, y: 0.22, z: 0.06 }
      { x: 0.0, y: -0.08, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.5 }
  ]

-- | 3D Chevron right icon
chevronRight :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
chevronRight props = icon3DWith props
  [ -- Top arm
    primitiveBox
      { x: 0.06, y: 0.22, z: 0.06 }
      { x: 0.0, y: 0.08, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.5 }
  , -- Bottom arm
    primitiveBox
      { x: 0.06, y: 0.22, z: 0.06 }
      { x: 0.0, y: -0.08, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.5 }
  ]

-- | 3D External link icon — arrow pointing out of box
externalLink :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
externalLink props = icon3DWith props
  [ -- Box frame bottom
    primitiveBox
      { x: 0.3, y: 0.05, z: 0.05 }
      { x: -0.05, y: -0.15, z: 0.0 }
      zero3
  , -- Box frame left
    primitiveBox
      { x: 0.05, y: 0.3, z: 0.05 }
      { x: -0.2, y: 0.0, z: 0.0 }
      zero3
  , -- Arrow shaft
    primitiveBox
      { x: 0.25, y: 0.05, z: 0.05 }
      { x: 0.05, y: 0.05, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.785 }
  , -- Arrow head
    primitiveCone
      0.08 0.1
      { x: 0.17, y: 0.17, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.785 }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // status
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Alert circle icon — sphere with exclamation
alertCircle :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
alertCircle props = icon3DWith props
  [ -- Circle (sphere)
    primitiveSphere 0.25 zero3
  , -- Exclamation line
    primitiveBox
      { x: 0.04, y: 0.15, z: 0.04 }
      { x: 0.0, y: 0.02, z: 0.26 }
      zero3
  , -- Exclamation dot
    primitiveSphere 0.03 { x: 0.0, y: -0.1, z: 0.26 }
  ]

-- | 3D Alert triangle icon — pyramid with exclamation
alertTriangle :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
alertTriangle props = icon3DWith props
  [ -- Triangle base (cone inverted)
    primitiveCone
      0.28 0.35
      { x: 0.0, y: -0.05, z: 0.0 }
      zero3
  , -- Exclamation line
    primitiveBox
      { x: 0.035, y: 0.12, z: 0.035 }
      { x: 0.0, y: 0.05, z: 0.0 }
      zero3
  , -- Exclamation dot
    primitiveSphere 0.025 { x: 0.0, y: -0.08, z: 0.0 }
  ]

-- | 3D Info icon — sphere with "i"
info :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
info props = icon3DWith props
  [ -- Circle (sphere)
    primitiveSphere 0.25 zero3
  , -- Info dot
    primitiveSphere 0.03 { x: 0.0, y: 0.1, z: 0.26 }
  , -- Info line
    primitiveBox
      { x: 0.04, y: 0.12, z: 0.04 }
      { x: 0.0, y: -0.03, z: 0.26 }
      zero3
  ]

-- | 3D Help circle icon — sphere with question mark
helpCircle :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
helpCircle props = icon3DWith props
  [ -- Circle (sphere)
    primitiveSphere 0.25 zero3
  , -- Question curve (approximated with torus segment)
    primitiveTorus
      0.06 0.025
      { x: 0.0, y: 0.06, z: 0.26 }
      { x: 0.3, y: 0.0, z: 0.0 }
  , -- Question stem
    primitiveBox
      { x: 0.03, y: 0.06, z: 0.03 }
      { x: 0.0, y: -0.02, z: 0.26 }
      zero3
  , -- Question dot
    primitiveSphere 0.025 { x: 0.0, y: -0.1, z: 0.26 }
  ]

-- | 3D Check circle icon — sphere with checkmark
checkCircle :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
checkCircle props = icon3DWith props
  [ -- Circle (sphere)
    primitiveSphere 0.25 zero3
  , -- Check short arm
    primitiveBox
      { x: 0.1, y: 0.035, z: 0.035 }
      { x: -0.06, y: -0.02, z: 0.26 }
      { x: 0.0, y: 0.0, z: 0.6 }
  , -- Check long arm
    primitiveBox
      { x: 0.18, y: 0.035, z: 0.035 }
      { x: 0.06, y: 0.04, z: 0.26 }
      { x: 0.0, y: 0.0, z: -0.4 }
  ]

-- | 3D X circle icon — sphere with X
xCircle :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
xCircle props = icon3DWith props
  [ -- Circle (sphere)
    primitiveSphere 0.25 zero3
  , -- X bar 1
    primitiveBox
      { x: 0.2, y: 0.035, z: 0.035 }
      { x: 0.0, y: 0.0, z: 0.26 }
      { x: 0.0, y: 0.0, z: 0.785 }
  , -- X bar 2
    primitiveBox
      { x: 0.2, y: 0.035, z: 0.035 }
      { x: 0.0, y: 0.0, z: 0.26 }
      { x: 0.0, y: 0.0, z: -0.785 }
  ]

-- | 3D Clock icon — circular clock face
clock :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
clock props = icon3DWith props
  [ -- Clock face (flat cylinder)
    primitiveCylinder
      0.25 0.25 0.06
      zero3
      zero3
  , -- Hour hand
    primitiveBox
      { x: 0.03, y: 0.1, z: 0.02 }
      { x: 0.0, y: 0.04, z: 0.04 }
      zero3
  , -- Minute hand
    primitiveBox
      { x: 0.025, y: 0.14, z: 0.02 }
      { x: 0.04, y: 0.02, z: 0.04 }
      { x: 0.0, y: 0.0, z: -0.5 }
  , -- Center dot
    primitiveSphere 0.03 { x: 0.0, y: 0.0, z: 0.04 }
  ]

-- | 3D Loader icon — circular loading indicator
loader :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
loader props = icon3DWith props
  [ -- Ring
    primitiveTorus
      0.2 0.04
      zero3
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  , -- Indicator ball
    primitiveSphere 0.06 { x: 0.2, y: 0.0, z: 0.0 }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // objects
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D File icon — document with folded corner
file :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
file props = icon3DWith props
  [ -- Document body
    primitiveBox
      { x: 0.28, y: 0.38, z: 0.04 }
      { x: 0.0, y: -0.02, z: 0.0 }
      zero3
  , -- Folded corner
    primitiveBox
      { x: 0.1, y: 0.1, z: 0.04 }
      { x: 0.09, y: 0.16, z: 0.02 }
      { x: 0.0, y: 0.0, z: 0.785 }
  ]

-- | 3D Folder icon — file folder with tab
folder :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
folder props = icon3DWith props
  [ -- Folder body
    primitiveBox
      { x: 0.4, y: 0.28, z: 0.08 }
      { x: 0.0, y: -0.04, z: 0.0 }
      zero3
  , -- Folder tab
    primitiveBox
      { x: 0.15, y: 0.06, z: 0.08 }
      { x: -0.1, y: 0.15, z: 0.0 }
      zero3
  ]

-- | 3D Folder open icon — open file folder
folderOpen :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
folderOpen props = icon3DWith props
  [ -- Folder back
    primitiveBox
      { x: 0.4, y: 0.28, z: 0.04 }
      { x: 0.0, y: -0.02, z: -0.04 }
      zero3
  , -- Folder front (tilted)
    primitiveBox
      { x: 0.4, y: 0.2, z: 0.04 }
      { x: 0.0, y: -0.08, z: 0.04 }
      { x: -0.3, y: 0.0, z: 0.0 }
  , -- Folder tab
    primitiveBox
      { x: 0.15, y: 0.06, z: 0.04 }
      { x: -0.1, y: 0.15, z: -0.04 }
      zero3
  ]

-- | 3D Image icon — picture frame with mountain/sun
image :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
image props = icon3DWith props
  [ -- Frame
    primitiveBox
      { x: 0.4, y: 0.32, z: 0.04 }
      zero3
      zero3
  , -- Sun (small sphere)
    primitiveSphere 0.05 { x: 0.1, y: 0.08, z: 0.03 }
  , -- Mountain (small cone)
    primitiveCone
      0.12 0.15
      { x: -0.05, y: -0.06, z: 0.03 }
      zero3
  ]

-- | 3D Calendar icon — date book
calendar :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
calendar props = icon3DWith props
  [ -- Calendar body
    primitiveBox
      { x: 0.35, y: 0.35, z: 0.06 }
      { x: 0.0, y: -0.03, z: 0.0 }
      zero3
  , -- Top bar
    primitiveBox
      { x: 0.35, y: 0.06, z: 0.07 }
      { x: 0.0, y: 0.15, z: 0.005 }
      zero3
  , -- Left ring
    primitiveCylinder
      0.025 0.025 0.08
      { x: -0.1, y: 0.19, z: 0.0 }
      zero3
  , -- Right ring
    primitiveCylinder
      0.025 0.025 0.08
      { x: 0.1, y: 0.19, z: 0.0 }
      zero3
  ]

-- | 3D Mail icon — envelope
mail :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
mail props = icon3DWith props
  [ -- Envelope body
    primitiveBox
      { x: 0.4, y: 0.26, z: 0.1 }
      { x: 0.0, y: -0.03, z: 0.0 }
      zero3
  , -- Envelope flap (triangular approximation)
    primitiveBox
      { x: 0.32, y: 0.12, z: 0.05 }
      { x: 0.0, y: 0.12, z: 0.04 }
      { x: 0.2, y: 0.0, z: 0.0 }
  ]

-- | 3D Link icon — chain links
link :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
link props = icon3DWith props
  [ -- Link 1
    primitiveTorus
      0.1 0.03
      { x: -0.08, y: 0.05, z: 0.0 }
      { x: pi / 2.0, y: 0.4, z: 0.0 }
  , -- Link 2
    primitiveTorus
      0.1 0.03
      { x: 0.08, y: -0.05, z: 0.0 }
      { x: pi / 2.0, y: 0.4, z: 0.0 }
  ]

-- | 3D Globe icon — sphere with latitude/longitude lines
globe :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
globe props = icon3DWith props
  [ -- Globe sphere
    primitiveSphere 0.25 zero3
  , -- Equator ring
    primitiveTorus
      0.26 0.015
      zero3
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  , -- Meridian ring
    primitiveTorus
      0.26 0.015
      zero3
      zero3
  ]

-- | 3D Home icon — house shape
home :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
home props = icon3DWith props
  [ -- House body
    primitiveBox
      { x: 0.3, y: 0.22, z: 0.2 }
      { x: 0.0, y: -0.09, z: 0.0 }
      zero3
  , -- Roof
    primitiveCone
      0.25 0.18
      { x: 0.0, y: 0.13, z: 0.0 }
      zero3
  , -- Door
    primitiveBox
      { x: 0.08, y: 0.14, z: 0.02 }
      { x: 0.0, y: -0.13, z: 0.11 }
      zero3
  ]

-- | 3D Settings icon — gear/cog
settings :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
settings props = icon3DWith props
  [ -- Gear body (cylinder)
    primitiveCylinder
      0.2 0.2 0.08
      zero3
      zero3
  , -- Center hole (smaller cylinder would be subtracted in real 3D)
    primitiveSphere 0.08 zero3
  , -- Gear teeth represented by boxes around perimeter
    primitiveBox { x: 0.08, y: 0.08, z: 0.08 } { x: 0.22, y: 0.0, z: 0.0 } zero3
  , primitiveBox { x: 0.08, y: 0.08, z: 0.08 } { x: -0.22, y: 0.0, z: 0.0 } zero3
  , primitiveBox { x: 0.08, y: 0.08, z: 0.08 } { x: 0.0, y: 0.22, z: 0.0 } zero3
  , primitiveBox { x: 0.08, y: 0.08, z: 0.08 } { x: 0.0, y: -0.22, z: 0.0 } zero3
  , primitiveBox { x: 0.08, y: 0.08, z: 0.08 } { x: 0.155, y: 0.155, z: 0.0 } { x: 0.0, y: 0.0, z: 0.785 }
  , primitiveBox { x: 0.08, y: 0.08, z: 0.08 } { x: -0.155, y: -0.155, z: 0.0 } { x: 0.0, y: 0.0, z: 0.785 }
  , primitiveBox { x: 0.08, y: 0.08, z: 0.08 } { x: 0.155, y: -0.155, z: 0.0 } { x: 0.0, y: 0.0, z: -0.785 }
  , primitiveBox { x: 0.08, y: 0.08, z: 0.08 } { x: -0.155, y: 0.155, z: 0.0 } { x: 0.0, y: 0.0, z: -0.785 }
  ]

-- | 3D User icon — person silhouette
user :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
user props = icon3DWith props
  [ -- Head
    primitiveSphere 0.12 { x: 0.0, y: 0.15, z: 0.0 }
  , -- Body (rounded torso)
    primitiveCylinder
      0.08 0.18 0.25
      { x: 0.0, y: -0.12, z: 0.0 }
      zero3
  ]

-- | 3D Users icon — multiple people
users :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
users props = icon3DWith props
  [ -- Person 1 (front)
    primitiveSphere 0.1 { x: -0.1, y: 0.12, z: 0.05 }
  , primitiveCylinder 0.06 0.14 0.2 { x: -0.1, y: -0.1, z: 0.05 } zero3
  , -- Person 2 (back)
    primitiveSphere 0.1 { x: 0.1, y: 0.14, z: -0.05 }
  , primitiveCylinder 0.06 0.14 0.2 { x: 0.1, y: -0.08, z: -0.05 } zero3
  ]

-- | 3D Heart icon — heart shape
heart :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
heart props = icon3DWith props
  [ -- Left lobe
    primitiveSphere 0.14 { x: -0.1, y: 0.08, z: 0.0 }
  , -- Right lobe
    primitiveSphere 0.14 { x: 0.1, y: 0.08, z: 0.0 }
  , -- Bottom point (cone)
    primitiveCone
      0.2 0.25
      { x: 0.0, y: -0.1, z: 0.0 }
      { x: pi, y: 0.0, z: 0.0 }
  ]

-- | 3D Star icon — 5-pointed star (approximated)
star :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
star props = icon3DWith props
  [ -- Center
    primitiveSphere 0.1 zero3
  , -- Top point
    primitiveCone 0.08 0.2 { x: 0.0, y: 0.2, z: 0.0 } zero3
  , -- Bottom left point
    primitiveCone 0.08 0.2 { x: -0.19, y: -0.1, z: 0.0 } { x: 0.0, y: 0.0, z: 2.2 }
  , -- Bottom right point
    primitiveCone 0.08 0.2 { x: 0.19, y: -0.1, z: 0.0 } { x: 0.0, y: 0.0, z: -2.2 }
  , -- Top left point
    primitiveCone 0.08 0.2 { x: -0.12, y: 0.16, z: 0.0 } { x: 0.0, y: 0.0, z: 1.2 }
  , -- Top right point
    primitiveCone 0.08 0.2 { x: 0.12, y: 0.16, z: 0.0 } { x: 0.0, y: 0.0, z: -1.2 }
  ]

-- | 3D Bookmark icon — ribbon marker
bookmark :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
bookmark props = icon3DWith props
  [ -- Main body
    primitiveBox
      { x: 0.2, y: 0.35, z: 0.04 }
      { x: 0.0, y: 0.03, z: 0.0 }
      zero3
  , -- Left bottom triangle
    primitiveBox
      { x: 0.1, y: 0.12, z: 0.04 }
      { x: -0.05, y: -0.2, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.3 }
  , -- Right bottom triangle
    primitiveBox
      { x: 0.1, y: 0.12, z: 0.04 }
      { x: 0.05, y: -0.2, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.3 }
  ]

-- | 3D Bell icon — notification bell
bell :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
bell props = icon3DWith props
  [ -- Bell body (dome)
    primitiveSphere 0.18 { x: 0.0, y: 0.02, z: 0.0 }
  , -- Bell bottom rim
    primitiveTorus
      0.2 0.04
      { x: 0.0, y: -0.12, z: 0.0 }
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  , -- Clapper
    primitiveSphere 0.05 { x: 0.0, y: -0.2, z: 0.0 }
  , -- Top loop
    primitiveSphere 0.04 { x: 0.0, y: 0.2, z: 0.0 }
  ]

-- | 3D Lock icon — padlock
lock :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
lock props = icon3DWith props
  [ -- Lock body
    primitiveBox
      { x: 0.26, y: 0.22, z: 0.1 }
      { x: 0.0, y: -0.08, z: 0.0 }
      zero3
  , -- Shackle
    primitiveTorus
      0.1 0.03
      { x: 0.0, y: 0.1, z: 0.0 }
      zero3
  , -- Keyhole
    primitiveSphere 0.03 { x: 0.0, y: -0.05, z: 0.06 }
  ]

-- | 3D Unlock icon — open padlock
unlock :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
unlock props = icon3DWith props
  [ -- Lock body
    primitiveBox
      { x: 0.26, y: 0.22, z: 0.1 }
      { x: 0.0, y: -0.08, z: 0.0 }
      zero3
  , -- Shackle (shifted)
    primitiveTorus
      0.1 0.03
      { x: 0.05, y: 0.15, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.3 }
  , -- Keyhole
    primitiveSphere 0.03 { x: 0.0, y: -0.05, z: 0.06 }
  ]

-- | 3D Key icon — key shape
key :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
key props = icon3DWith props
  [ -- Key head (ring)
    primitiveTorus
      0.1 0.03
      { x: -0.12, y: 0.1, z: 0.0 }
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  , -- Key shaft
    primitiveBox
      { x: 0.3, y: 0.05, z: 0.05 }
      { x: 0.08, y: -0.05, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.5 }
  , -- Key teeth
    primitiveBox { x: 0.06, y: 0.08, z: 0.05 } { x: 0.18, y: -0.12, z: 0.0 } zero3
  , primitiveBox { x: 0.05, y: 0.06, z: 0.05 } { x: 0.23, y: -0.14, z: 0.0 } zero3
  ]

-- | 3D Eye icon — eye with pupil
eye :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
eye props = icon3DWith props
  [ -- Eye shape (elongated sphere)
    primitiveSphere 0.2 zero3
  , -- Iris
    primitiveSphere 0.1 { x: 0.0, y: 0.0, z: 0.15 }
  , -- Pupil
    primitiveSphere 0.05 { x: 0.0, y: 0.0, z: 0.22 }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // media
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Play icon — play button triangle
play :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
play props = icon3D props $
  primitiveCone
    0.25 0.35
    zero3
    { x: 0.0, y: 0.0, z: -pi / 2.0 }

-- | 3D Pause icon — two vertical bars
pause :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
pause props = icon3DWith props
  [ -- Left bar
    primitiveBox
      { x: 0.1, y: 0.35, z: 0.08 }
      { x: -0.1, y: 0.0, z: 0.0 }
      zero3
  , -- Right bar
    primitiveBox
      { x: 0.1, y: 0.35, z: 0.08 }
      { x: 0.1, y: 0.0, z: 0.0 }
      zero3
  ]

-- | 3D Stop icon — square
stop :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
stop props = icon3D props $
  primitiveBox
    { x: 0.3, y: 0.3, z: 0.08 }
    zero3
    zero3

-- | 3D Volume icon — speaker with sound waves
volume :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
volume props = icon3DWith props
  [ -- Speaker body
    primitiveBox
      { x: 0.1, y: 0.15, z: 0.1 }
      { x: -0.12, y: 0.0, z: 0.0 }
      zero3
  , -- Speaker cone
    primitiveCone
      0.08 0.15
      { x: -0.02, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: -pi / 2.0 }
  , -- Sound wave 1 (inner)
    primitiveTorus
      0.12 0.02
      { x: 0.1, y: 0.0, z: 0.0 }
      { x: 0.0, y: pi / 2.0, z: 0.0 }
  , -- Sound wave 2 (outer)
    primitiveTorus
      0.2 0.02
      { x: 0.15, y: 0.0, z: 0.0 }
      { x: 0.0, y: pi / 2.0, z: 0.0 }
  ]

-- | 3D Mic icon — microphone
mic :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
mic props = icon3DWith props
  [ -- Mic head
    primitiveSphere 0.12 { x: 0.0, y: 0.12, z: 0.0 }
  , -- Mic body
    primitiveCylinder
      0.08 0.08 0.15
      { x: 0.0, y: 0.0, z: 0.0 }
      zero3
  , -- Stand
    primitiveCylinder
      0.03 0.03 0.12
      { x: 0.0, y: -0.15, z: 0.0 }
      zero3
  , -- Base
    primitiveCylinder
      0.1 0.1 0.03
      { x: 0.0, y: -0.22, z: 0.0 }
      zero3
  ]

-- | 3D Camera icon — camera body with lens
camera :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
camera props = icon3DWith props
  [ -- Camera body
    primitiveBox
      { x: 0.38, y: 0.22, z: 0.15 }
      { x: 0.0, y: -0.02, z: 0.0 }
      zero3
  , -- Viewfinder
    primitiveBox
      { x: 0.12, y: 0.06, z: 0.08 }
      { x: 0.0, y: 0.13, z: 0.0 }
      zero3
  , -- Lens
    primitiveCylinder
      0.1 0.1 0.08
      { x: 0.0, y: 0.0, z: 0.1 }
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // layout
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Menu icon — hamburger menu (three bars)
menu :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
menu props = icon3DWith props
  [ -- Top bar
    primitiveBox
      { x: 0.35, y: 0.06, z: 0.06 }
      { x: 0.0, y: 0.12, z: 0.0 }
      zero3
  , -- Middle bar
    primitiveBox
      { x: 0.35, y: 0.06, z: 0.06 }
      zero3
      zero3
  , -- Bottom bar
    primitiveBox
      { x: 0.35, y: 0.06, z: 0.06 }
      { x: 0.0, y: -0.12, z: 0.0 }
      zero3
  ]

-- | 3D More horizontal icon — three dots horizontal
moreHorizontal :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
moreHorizontal props = icon3DWith props
  [ primitiveSphere 0.06 { x: -0.15, y: 0.0, z: 0.0 }
  , primitiveSphere 0.06 zero3
  , primitiveSphere 0.06 { x: 0.15, y: 0.0, z: 0.0 }
  ]

-- | 3D More vertical icon — three dots vertical
moreVertical :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
moreVertical props = icon3DWith props
  [ primitiveSphere 0.06 { x: 0.0, y: 0.15, z: 0.0 }
  , primitiveSphere 0.06 zero3
  , primitiveSphere 0.06 { x: 0.0, y: -0.15, z: 0.0 }
  ]

-- | 3D Grid icon — 2x2 grid of squares
grid :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
grid props = icon3DWith props
  [ primitiveBox { x: 0.14, y: 0.14, z: 0.06 } { x: -0.1, y: 0.1, z: 0.0 } zero3
  , primitiveBox { x: 0.14, y: 0.14, z: 0.06 } { x: 0.1, y: 0.1, z: 0.0 } zero3
  , primitiveBox { x: 0.14, y: 0.14, z: 0.06 } { x: -0.1, y: -0.1, z: 0.0 } zero3
  , primitiveBox { x: 0.14, y: 0.14, z: 0.06 } { x: 0.1, y: -0.1, z: 0.0 } zero3
  ]

-- | 3D List icon — list with bullets
list :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
list props = icon3DWith props
  [ -- Bullet 1
    primitiveSphere 0.04 { x: -0.15, y: 0.12, z: 0.0 }
  , -- Line 1
    primitiveBox { x: 0.22, y: 0.04, z: 0.04 } { x: 0.06, y: 0.12, z: 0.0 } zero3
  , -- Bullet 2
    primitiveSphere 0.04 { x: -0.15, y: 0.0, z: 0.0 }
  , -- Line 2
    primitiveBox { x: 0.22, y: 0.04, z: 0.04 } { x: 0.06, y: 0.0, z: 0.0 } zero3
  , -- Bullet 3
    primitiveSphere 0.04 { x: -0.15, y: -0.12, z: 0.0 }
  , -- Line 3
    primitiveBox { x: 0.22, y: 0.04, z: 0.04 } { x: 0.06, y: -0.12, z: 0.0 } zero3
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // data
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Bar chart icon — vertical bar graph
barChart :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
barChart props = icon3DWith props
  [ -- Bar 1 (short)
    primitiveBox
      { x: 0.08, y: 0.15, z: 0.08 }
      { x: -0.15, y: -0.1, z: 0.0 }
      zero3
  , -- Bar 2 (tall)
    primitiveBox
      { x: 0.08, y: 0.35, z: 0.08 }
      { x: 0.0, y: 0.0, z: 0.0 }
      zero3
  , -- Bar 3 (medium)
    primitiveBox
      { x: 0.08, y: 0.25, z: 0.08 }
      { x: 0.15, y: -0.05, z: 0.0 }
      zero3
  ]

-- | 3D Pie chart icon — segmented circle
pieChart :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
pieChart props = icon3DWith props
  [ -- Main pie (cylinder)
    primitiveCylinder
      0.25 0.25 0.08
      zero3
      zero3
  , -- Segment line 1
    primitiveBox
      { x: 0.26, y: 0.02, z: 0.09 }
      { x: 0.0, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.5 }
  , -- Segment line 2
    primitiveBox
      { x: 0.26, y: 0.02, z: 0.09 }
      { x: 0.0, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.8 }
  ]

-- | 3D Trending up icon — upward arrow with line
trendingUp :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
trendingUp props = icon3DWith props
  [ -- Trend line
    primitiveBox
      { x: 0.4, y: 0.04, z: 0.04 }
      { x: -0.02, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.4 }
  , -- Arrow head
    primitiveCone
      0.08 0.12
      { x: 0.17, y: 0.14, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.4 }
  ]

-- | 3D Trending down icon — downward arrow with line
trendingDown :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
trendingDown props = icon3DWith props
  [ -- Trend line
    primitiveBox
      { x: 0.4, y: 0.04, z: 0.04 }
      { x: -0.02, y: 0.0, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.4 }
  , -- Arrow head
    primitiveCone
      0.08 0.12
      { x: 0.17, y: -0.14, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.4 + pi }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // misc
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D Sun icon — sun with rays
sun :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
sun props = icon3DWith props
  [ -- Sun center
    primitiveSphere 0.12 zero3
  , -- Rays (8 directions)
    primitiveBox { x: 0.08, y: 0.03, z: 0.03 } { x: 0.22, y: 0.0, z: 0.0 } zero3
  , primitiveBox { x: 0.08, y: 0.03, z: 0.03 } { x: -0.22, y: 0.0, z: 0.0 } zero3
  , primitiveBox { x: 0.03, y: 0.08, z: 0.03 } { x: 0.0, y: 0.22, z: 0.0 } zero3
  , primitiveBox { x: 0.03, y: 0.08, z: 0.03 } { x: 0.0, y: -0.22, z: 0.0 } zero3
  , primitiveBox { x: 0.06, y: 0.03, z: 0.03 } { x: 0.16, y: 0.16, z: 0.0 } { x: 0.0, y: 0.0, z: 0.785 }
  , primitiveBox { x: 0.06, y: 0.03, z: 0.03 } { x: -0.16, y: -0.16, z: 0.0 } { x: 0.0, y: 0.0, z: 0.785 }
  , primitiveBox { x: 0.06, y: 0.03, z: 0.03 } { x: 0.16, y: -0.16, z: 0.0 } { x: 0.0, y: 0.0, z: -0.785 }
  , primitiveBox { x: 0.06, y: 0.03, z: 0.03 } { x: -0.16, y: 0.16, z: 0.0 } { x: 0.0, y: 0.0, z: -0.785 }
  ]

-- | 3D Moon icon — crescent moon
moon :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
moon props = icon3DWith props
  [ -- Moon body (main sphere)
    primitiveSphere 0.22 zero3
  -- The crescent effect would be achieved via material/shader in real 3D
  -- Here we approximate with overlapping sphere positions
  ]

-- | 3D Zap icon — lightning bolt
zap :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
zap props = icon3DWith props
  [ -- Top bolt
    primitiveBox
      { x: 0.15, y: 0.2, z: 0.06 }
      { x: 0.0, y: 0.1, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.3 }
  , -- Bottom bolt
    primitiveBox
      { x: 0.15, y: 0.2, z: 0.06 }
      { x: 0.0, y: -0.1, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.3 }
  ]

-- | 3D Cloud icon — fluffy cloud
cloud :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
cloud props = icon3DWith props
  [ -- Main cloud body
    primitiveSphere 0.18 { x: 0.0, y: 0.0, z: 0.0 }
  , -- Left puff
    primitiveSphere 0.12 { x: -0.15, y: -0.03, z: 0.0 }
  , -- Right puff
    primitiveSphere 0.14 { x: 0.14, y: -0.02, z: 0.0 }
  , -- Top puff
    primitiveSphere 0.1 { x: 0.05, y: 0.1, z: 0.0 }
  ]

-- | 3D Wifi icon — wifi signal arcs
wifi :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
wifi props = icon3DWith props
  [ -- Base dot
    primitiveSphere 0.05 { x: 0.0, y: -0.15, z: 0.0 }
  , -- Arc 1 (inner)
    primitiveTorus
      0.1 0.025
      { x: 0.0, y: -0.05, z: 0.0 }
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  , -- Arc 2 (middle)
    primitiveTorus
      0.18 0.025
      { x: 0.0, y: 0.03, z: 0.0 }
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  , -- Arc 3 (outer)
    primitiveTorus
      0.26 0.025
      { x: 0.0, y: 0.11, z: 0.0 }
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  ]

-- | 3D Power icon — power button symbol
power :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
power props = icon3DWith props
  [ -- Circle arc
    primitiveTorus
      0.18 0.035
      { x: 0.0, y: -0.02, z: 0.0 }
      { x: pi / 2.0, y: 0.0, z: 0.0 }
  , -- Center line
    primitiveBox
      { x: 0.05, y: 0.2, z: 0.05 }
      { x: 0.0, y: 0.1, z: 0.0 }
      zero3
  ]

-- | 3D Terminal icon — command prompt
terminal :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
terminal props = icon3DWith props
  [ -- Terminal window
    primitiveBox
      { x: 0.4, y: 0.3, z: 0.04 }
      zero3
      zero3
  , -- Prompt chevron (>)
    primitiveBox
      { x: 0.08, y: 0.03, z: 0.02 }
      { x: -0.12, y: 0.02, z: 0.03 }
      { x: 0.0, y: 0.0, z: -0.5 }
  , primitiveBox
      { x: 0.08, y: 0.03, z: 0.02 }
      { x: -0.12, y: -0.04, z: 0.03 }
      { x: 0.0, y: 0.0, z: 0.5 }
  , -- Cursor line
    primitiveBox
      { x: 0.12, y: 0.03, z: 0.02 }
      { x: 0.0, y: -0.01, z: 0.03 }
      zero3
  ]

-- | 3D Code icon — angle brackets < >
code :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
code props = icon3DWith props
  [ -- Left bracket top
    primitiveBox
      { x: 0.12, y: 0.04, z: 0.04 }
      { x: -0.12, y: 0.08, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.5 }
  , -- Left bracket bottom
    primitiveBox
      { x: 0.12, y: 0.04, z: 0.04 }
      { x: -0.12, y: -0.08, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.5 }
  , -- Right bracket top
    primitiveBox
      { x: 0.12, y: 0.04, z: 0.04 }
      { x: 0.12, y: 0.08, z: 0.0 }
      { x: 0.0, y: 0.0, z: -0.5 }
  , -- Right bracket bottom
    primitiveBox
      { x: 0.12, y: 0.04, z: 0.04 }
      { x: 0.12, y: -0.08, z: 0.0 }
      { x: 0.0, y: 0.0, z: 0.5 }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // multi-color icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Multi-color folder — body uses Primary, tab uses Accent, glossy finish
folderMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
folderMulti props = iconMulti props
  [ -- Folder body (Primary, soft material)
    iconPart Primary SoftVariant $
      primitiveRoundedBox
        (vec3 0.42 0.30 0.10)
        0.03
        (vec3 0.0 (-0.04) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Folder tab (Accent, glossy)
    iconPart Accent GlossyVariant $
      primitiveRoundedBox
        (vec3 0.16 0.07 0.10)
        0.02
        (vec3 (-0.10) 0.16 0.0)
        (euler 0.0 0.0 0.0)
  , -- Inner shadow/depth (Secondary)
    iconPart Secondary MatteVariant $
      primitiveBox
        (vec3 0.36 0.22 0.02)
        (vec3 0.0 (-0.02) 0.04)
        (euler 0.0 0.0 0.0)
  ]

-- | Multi-color file — document body with colored corner fold
fileMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
fileMulti props = iconMulti props
  [ -- Document body (Neutral, matte)
    iconPart Neutral SoftVariant $
      primitiveRoundedBox
        (vec3 0.30 0.40 0.04)
        0.02
        (vec3 0.0 (-0.02) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Folded corner (Accent)
    iconPart Accent GlossyVariant $
      primitiveBox
        (vec3 0.10 0.10 0.05)
        (vec3 0.10 0.17 0.02)
        (euler 0.0 0.0 0.785)
  , -- Content lines (Secondary)
    iconPart Secondary MatteVariant $
      primitiveBox
        (vec3 0.20 0.02 0.01)
        (vec3 (-0.02) 0.05 0.025)
        (euler 0.0 0.0 0.0)
  , iconPart Secondary MatteVariant $
      primitiveBox
        (vec3 0.20 0.02 0.01)
        (vec3 (-0.02) 0.0 0.025)
        (euler 0.0 0.0 0.0)
  , iconPart Secondary MatteVariant $
      primitiveBox
        (vec3 0.14 0.02 0.01)
        (vec3 (-0.05) (-0.05) 0.025)
        (euler 0.0 0.0 0.0)
  ]

-- | Multi-color home — house body with colored roof and door
homeMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
homeMulti props = iconMulti props
  [ -- House body (Primary, soft)
    iconPart Primary SoftVariant $
      primitiveRoundedBox
        (vec3 0.32 0.24 0.22)
        0.02
        (vec3 0.0 (-0.10) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Roof (Secondary, matte)
    iconPart Secondary MatteVariant $
      primitiveCone
        0.28 0.20
        (vec3 0.0 0.14 0.0)
        (euler 0.0 0.0 0.0)
  , -- Door (Accent, glossy)
    iconPart Accent GlossyVariant $
      primitiveRoundedBox
        (vec3 0.09 0.16 0.03)
        0.01
        (vec3 0.0 (-0.14) 0.12)
        (euler 0.0 0.0 0.0)
  , -- Window (Neutral, chrome for glass effect)
    iconPart Neutral ChromeVariant $
      primitiveBox
        (vec3 0.06 0.06 0.02)
        (vec3 (-0.08) (-0.04) 0.12)
        (euler 0.0 0.0 0.0)
  ]

-- | Multi-color settings gear — gear body with chrome center
settingsMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
settingsMulti props = iconMulti props
  [ -- Gear body (Primary, metallic)
    iconPart Primary MetallicVariant $
      primitiveCylinder
        0.22 0.22 0.10
        zero3
        (euler 0.0 0.0 0.0)
  , -- Center hub (Accent, chrome)
    iconPart Accent ChromeVariant $
      primitiveSphere 0.10 zero3
  , -- Gear teeth (Secondary)
    iconPart Secondary SoftVariant $
      primitiveBox (vec3 0.10 0.10 0.10) (vec3 0.24 0.0 0.0) (euler 0.0 0.0 0.0)
  , iconPart Secondary SoftVariant $
      primitiveBox (vec3 0.10 0.10 0.10) (vec3 (-0.24) 0.0 0.0) (euler 0.0 0.0 0.0)
  , iconPart Secondary SoftVariant $
      primitiveBox (vec3 0.10 0.10 0.10) (vec3 0.0 0.24 0.0) (euler 0.0 0.0 0.0)
  , iconPart Secondary SoftVariant $
      primitiveBox (vec3 0.10 0.10 0.10) (vec3 0.0 (-0.24) 0.0) (euler 0.0 0.0 0.0)
  , iconPart Secondary SoftVariant $
      primitiveBox (vec3 0.10 0.10 0.10) (vec3 0.17 0.17 0.0) (euler 0.0 0.0 0.785)
  , iconPart Secondary SoftVariant $
      primitiveBox (vec3 0.10 0.10 0.10) (vec3 (-0.17) (-0.17) 0.0) (euler 0.0 0.0 0.785)
  ]

-- | Multi-color bell — bell body with clapper
bellMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
bellMulti props = iconMulti props
  [ -- Bell dome (Primary, glossy)
    iconPart Primary GlossyVariant $
      primitiveSphere 0.20 (vec3 0.0 0.02 0.0)
  , -- Bell rim (Secondary, chrome)
    iconPart Secondary ChromeVariant $
      primitiveTorus
        0.22 0.05
        (vec3 0.0 (-0.14) 0.0)
        (euler (pi / 2.0) 0.0 0.0)
  , -- Clapper (Accent, metallic)
    iconPart Accent MetallicVariant $
      primitiveSphere 0.06 (vec3 0.0 (-0.22) 0.0)
  , -- Top loop (Secondary)
    iconPart Secondary ChromeVariant $
      primitiveSphere 0.05 (vec3 0.0 0.22 0.0)
  ]

-- | Multi-color lock — padlock body with shackle
lockMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
lockMulti props = iconMulti props
  [ -- Lock body (Primary, metallic)
    iconPart Primary MetallicVariant $
      primitiveRoundedBox
        (vec3 0.28 0.24 0.12)
        0.03
        (vec3 0.0 (-0.08) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Shackle (Secondary, chrome)
    iconPart Secondary ChromeVariant $
      primitiveTorus
        0.10 0.04
        (vec3 0.0 0.10 0.0)
        (euler 0.0 0.0 0.0)
  , -- Keyhole (Accent)
    iconPart Accent GlossyVariant $
      primitiveSphere 0.04 (vec3 0.0 (-0.06) 0.07)
  , iconPart Accent GlossyVariant $
      primitiveBox
        (vec3 0.025 0.06 0.02)
        (vec3 0.0 (-0.11) 0.07)
        (euler 0.0 0.0 0.0)
  ]

-- | Multi-color mail — envelope with colored flap
mailMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
mailMulti props = iconMulti props
  [ -- Envelope body (Primary, soft)
    iconPart Primary SoftVariant $
      primitiveRoundedBox
        (vec3 0.44 0.28 0.12)
        0.02
        (vec3 0.0 (-0.04) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Envelope flap (Accent, glossy)
    iconPart Accent GlossyVariant $
      primitiveBox
        (vec3 0.36 0.14 0.06)
        (vec3 0.0 0.12 0.05)
        (euler 0.22 0.0 0.0)
  , -- Seal/decoration (Secondary)
    iconPart Secondary ChromeVariant $
      primitiveSphere 0.04 (vec3 0.0 0.06 0.08)
  ]

-- | Multi-color calendar — date book with binding rings
calendarMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
calendarMulti props = iconMulti props
  [ -- Calendar body (Neutral, soft)
    iconPart Neutral SoftVariant $
      primitiveRoundedBox
        (vec3 0.38 0.38 0.08)
        0.02
        (vec3 0.0 (-0.04) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Top header bar (Primary)
    iconPart Primary GlossyVariant $
      primitiveRoundedBox
        (vec3 0.38 0.08 0.09)
        0.02
        (vec3 0.0 0.16 0.005)
        (euler 0.0 0.0 0.0)
  , -- Binding ring left (Secondary, chrome)
    iconPart Secondary ChromeVariant $
      primitiveCylinder
        0.03 0.03 0.10
        (vec3 (-0.12) 0.21 0.0)
        (euler 0.0 0.0 0.0)
  , -- Binding ring right (Secondary, chrome)
    iconPart Secondary ChromeVariant $
      primitiveCylinder
        0.03 0.03 0.10
        (vec3 0.12 0.21 0.0)
        (euler 0.0 0.0 0.0)
  , -- Date highlight (Accent)
    iconPart Accent GlossyVariant $
      primitiveRoundedBox
        (vec3 0.08 0.08 0.02)
        0.01
        (vec3 0.05 (-0.08) 0.05)
        (euler 0.0 0.0 0.0)
  ]

-- | Multi-color camera — camera body with lens
cameraMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
cameraMulti props = iconMulti props
  [ -- Camera body (Primary, soft)
    iconPart Primary SoftVariant $
      primitiveRoundedBox
        (vec3 0.42 0.26 0.18)
        0.03
        (vec3 0.0 (-0.02) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Viewfinder (Secondary)
    iconPart Secondary MatteVariant $
      primitiveRoundedBox
        (vec3 0.14 0.08 0.10)
        0.02
        (vec3 0.0 0.14 0.0)
        (euler 0.0 0.0 0.0)
  , -- Lens outer ring (Accent, chrome)
    iconPart Accent ChromeVariant $
      primitiveCylinder
        0.12 0.12 0.04
        (vec3 0.0 0.0 0.10)
        (euler (pi / 2.0) 0.0 0.0)
  , -- Lens glass (Neutral, chrome for glass effect)
    iconPart Neutral ChromeVariant $
      primitiveCylinder
        0.08 0.08 0.06
        (vec3 0.0 0.0 0.13)
        (euler (pi / 2.0) 0.0 0.0)
  , -- Shutter button (Accent)
    iconPart Accent GlossyVariant $
      primitiveSphere 0.04 (vec3 0.14 0.14 0.0)
  ]

-- | Multi-color search — magnifying glass with colored handle
searchMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
searchMulti props = iconMulti props
  [ -- Glass ring (Secondary, chrome)
    iconPart Secondary ChromeVariant $
      primitiveTorus
        0.16 0.04
        (vec3 (-0.06) 0.06 0.0)
        (euler (pi / 2.0) 0.0 0.0)
  , -- Glass lens (Neutral, chrome for glass)
    iconPart Neutral ChromeVariant $
      primitiveCylinder
        0.12 0.12 0.02
        (vec3 (-0.06) 0.06 0.0)
        (euler (pi / 2.0) 0.0 0.0)
  , -- Handle (Primary, glossy)
    iconPart Primary GlossyVariant $
      primitiveCapsule
        0.05 0.18
        (vec3 0.14 (-0.14) 0.0)
        (euler 0.0 0.0 0.785)
  , -- Handle accent ring (Accent)
    iconPart Accent MetallicVariant $
      primitiveTorus
        0.06 0.02
        (vec3 0.06 (-0.06) 0.0)
        (euler (pi / 2.0) 0.0 0.785)
  ]

-- | Multi-color download — arrow with tray
downloadMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
downloadMulti props = iconMulti props
  [ -- Arrow shaft (Primary)
    iconPart Primary SoftVariant $
      primitiveCapsule
        0.05 0.22
        (vec3 0.0 0.06 0.0)
        (euler 0.0 0.0 0.0)
  , -- Arrow head (Accent, glossy)
    iconPart Accent GlossyVariant $
      primitiveCone
        0.16 0.14
        (vec3 0.0 (-0.12) 0.0)
        (euler pi 0.0 0.0)
  , -- Tray (Secondary, metallic)
    iconPart Secondary MetallicVariant $
      primitiveRoundedBox
        (vec3 0.44 0.08 0.18)
        0.02
        (vec3 0.0 (-0.24) 0.0)
        (euler 0.0 0.0 0.0)
  ]

-- | Multi-color upload — arrow with tray pointing up
uploadMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
uploadMulti props = iconMulti props
  [ -- Arrow shaft (Primary)
    iconPart Primary SoftVariant $
      primitiveCapsule
        0.05 0.22
        (vec3 0.0 0.0 0.0)
        (euler 0.0 0.0 0.0)
  , -- Arrow head (Accent, glossy)
    iconPart Accent GlossyVariant $
      primitiveCone
        0.16 0.14
        (vec3 0.0 0.18 0.0)
        (euler 0.0 0.0 0.0)
  , -- Tray (Secondary, metallic)
    iconPart Secondary MetallicVariant $
      primitiveRoundedBox
        (vec3 0.44 0.08 0.18)
        0.02
        (vec3 0.0 (-0.24) 0.0)
        (euler 0.0 0.0 0.0)
  ]

-- | Multi-color user — person silhouette with styled layers
userMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
userMulti props = iconMulti props
  [ -- Head (Primary, soft)
    iconPart Primary SoftVariant $
      primitiveSphere 0.14 (vec3 0.0 0.16 0.0)
  , -- Body (Secondary)
    iconPart Secondary SoftVariant $
      primitiveCylinder
        0.10 0.20 0.28
        (vec3 0.0 (-0.12) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Collar/accent (Accent)
    iconPart Accent GlossyVariant $
      primitiveTorus
        0.12 0.03
        (vec3 0.0 0.02 0.0)
        (euler (pi / 2.0) 0.0 0.0)
  ]

-- | Multi-color heart — two-tone heart with depth
heartMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
heartMulti props = iconMulti props
  [ -- Left lobe (Primary)
    iconPart Primary GlossyVariant $
      primitiveSphere 0.16 (vec3 (-0.11) 0.09 0.0)
  , -- Right lobe (Primary)
    iconPart Primary GlossyVariant $
      primitiveSphere 0.16 (vec3 0.11 0.09 0.0)
  , -- Bottom point (Accent)
    iconPart Accent GlossyVariant $
      primitiveCone
        0.22 0.28
        (vec3 0.0 (-0.12) 0.0)
        (euler pi 0.0 0.0)
  , -- Highlight (Neutral, chrome)
    iconPart Neutral ChromeVariant $
      primitiveSphere 0.05 (vec3 (-0.08) 0.12 0.10)
  ]

-- | Multi-color star — five-pointed star with center
starMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
starMulti props = iconMulti props
  [ -- Center (Primary)
    iconPart Primary GlossyVariant $
      primitiveSphere 0.12 zero3
  , -- Top point (Accent)
    iconPart Accent GlossyVariant $
      primitiveCone 0.10 0.22 (vec3 0.0 0.22 0.0) (euler 0.0 0.0 0.0)
  , -- Bottom left (Secondary)
    iconPart Secondary SoftVariant $
      primitiveCone 0.10 0.22 (vec3 (-0.21) (-0.12) 0.0) (euler 0.0 0.0 2.2)
  , -- Bottom right (Secondary)
    iconPart Secondary SoftVariant $
      primitiveCone 0.10 0.22 (vec3 0.21 (-0.12) 0.0) (euler 0.0 0.0 (-2.2))
  , -- Top left (Accent)
    iconPart Accent GlossyVariant $
      primitiveCone 0.08 0.18 (vec3 (-0.14) 0.18 0.0) (euler 0.0 0.0 1.2)
  , -- Top right (Accent)
    iconPart Accent GlossyVariant $
      primitiveCone 0.08 0.18 (vec3 0.14 0.18 0.0) (euler 0.0 0.0 (-1.2))
  ]

-- | Multi-color play button — triangle with chrome ring
playMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
playMulti props = iconMulti props
  [ -- Play triangle (Accent, glossy)
    iconPart Accent GlossyVariant $
      primitiveCone
        0.22 0.32
        zero3
        (euler 0.0 0.0 (-pi / 2.0))
  , -- Background circle (Primary)
    iconPart Primary SoftVariant $
      primitiveCylinder
        0.30 0.30 0.08
        (vec3 0.02 0.0 (-0.04))
        (euler 0.0 0.0 0.0)
  , -- Outer ring (Secondary, chrome)
    iconPart Secondary ChromeVariant $
      primitiveTorus
        0.32 0.03
        (vec3 0.02 0.0 (-0.04))
        (euler (pi / 2.0) 0.0 0.0)
  ]

-- | Multi-color microphone — mic with stand
micMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
micMulti props = iconMulti props
  [ -- Mic head (Primary, metallic)
    iconPart Primary MetallicVariant $
      primitiveSphere 0.14 (vec3 0.0 0.14 0.0)
  , -- Mic body (Secondary)
    iconPart Secondary SoftVariant $
      primitiveCylinder
        0.10 0.10 0.16
        (vec3 0.0 0.0 0.0)
        (euler 0.0 0.0 0.0)
  , -- Stand (Accent, chrome)
    iconPart Accent ChromeVariant $
      primitiveCylinder
        0.04 0.04 0.14
        (vec3 0.0 (-0.16) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Base (Secondary, metallic)
    iconPart Secondary MetallicVariant $
      primitiveCylinder
        0.12 0.12 0.04
        (vec3 0.0 (-0.24) 0.0)
        (euler 0.0 0.0 0.0)
  ]

-- | Multi-color globe — earth with rings
globeMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
globeMulti props = iconMulti props
  [ -- Globe sphere (Primary, glossy)
    iconPart Primary GlossyVariant $
      primitiveSphere 0.26 zero3
  , -- Equator ring (Secondary, chrome)
    iconPart Secondary ChromeVariant $
      primitiveTorus
        0.28 0.02
        zero3
        (euler (pi / 2.0) 0.0 0.0)
  , -- Meridian ring (Accent)
    iconPart Accent MetallicVariant $
      primitiveTorus
        0.28 0.02
        zero3
        (euler 0.0 0.0 0.0)
  , -- Continent highlight (Neutral)
    iconPart Neutral SoftVariant $
      primitiveSphere 0.08 (vec3 0.12 0.10 0.18)
  ]

-- | Multi-color terminal — command prompt window
terminalMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
terminalMulti props = iconMulti props
  [ -- Window frame (Primary, soft)
    iconPart Primary SoftVariant $
      primitiveRoundedBox
        (vec3 0.44 0.34 0.06)
        0.03
        zero3
        (euler 0.0 0.0 0.0)
  , -- Title bar (Secondary)
    iconPart Secondary MatteVariant $
      primitiveBox
        (vec3 0.44 0.06 0.07)
        (vec3 0.0 0.14 0.005)
        (euler 0.0 0.0 0.0)
  , -- Prompt chevron (Accent)
    iconPart Accent GlossyVariant $
      primitiveBox
        (vec3 0.10 0.04 0.02)
        (vec3 (-0.14) 0.02 0.04)
        (euler 0.0 0.0 (-0.5))
  , iconPart Accent GlossyVariant $
      primitiveBox
        (vec3 0.10 0.04 0.02)
        (vec3 (-0.14) (-0.04) 0.04)
        (euler 0.0 0.0 0.5)
  , -- Cursor line (Neutral)
    iconPart Neutral ChromeVariant $
      primitiveBox
        (vec3 0.14 0.04 0.02)
        (vec3 0.02 (-0.01) 0.04)
        (euler 0.0 0.0 0.0)
  ]

-- | Multi-color cloud — fluffy cloud with depth
cloudMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
cloudMulti props = iconMulti props
  [ -- Main cloud body (Primary)
    iconPart Primary SoftVariant $
      primitiveSphere 0.20 (vec3 0.0 0.0 0.0)
  , -- Left puff (Secondary)
    iconPart Secondary SoftVariant $
      primitiveSphere 0.14 (vec3 (-0.16) (-0.04) 0.0)
  , -- Right puff (Secondary)
    iconPart Secondary SoftVariant $
      primitiveSphere 0.16 (vec3 0.16 (-0.02) 0.0)
  , -- Top puff (Accent)
    iconPart Accent GlossyVariant $
      primitiveSphere 0.12 (vec3 0.06 0.12 0.0)
  , -- Shadow puff (Neutral)
    iconPart Neutral MatteVariant $
      primitiveSphere 0.10 (vec3 (-0.06) (-0.10) (-0.04))
  ]

-- | Multi-color alert — warning triangle
alertMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
alertMulti props = iconMulti props
  [ -- Triangle base (Primary)
    iconPart Primary GlossyVariant $
      primitiveCone
        0.30 0.38
        (vec3 0.0 (-0.06) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Exclamation stem (Accent)
    iconPart Accent MatteVariant $
      primitiveCapsule
        0.04 0.12
        (vec3 0.0 0.06 0.0)
        (euler 0.0 0.0 0.0)
  , -- Exclamation dot (Accent)
    iconPart Accent GlossyVariant $
      primitiveSphere 0.04 (vec3 0.0 (-0.10) 0.0)
  ]

-- | Multi-color checkmark — success indicator
checkMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
checkMulti props = iconMulti props
  [ -- Background circle (Primary)
    iconPart Primary SoftVariant $
      primitiveCylinder
        0.28 0.28 0.08
        zero3
        (euler 0.0 0.0 0.0)
  , -- Outer ring (Secondary, chrome)
    iconPart Secondary ChromeVariant $
      primitiveTorus
        0.30 0.03
        zero3
        (euler (pi / 2.0) 0.0 0.0)
  , -- Check short arm (Accent)
    iconPart Accent GlossyVariant $
      primitiveCapsule
        0.04 0.10
        (vec3 (-0.08) (-0.02) 0.05)
        (euler 0.0 0.0 0.7)
  , -- Check long arm (Accent)
    iconPart Accent GlossyVariant $
      primitiveCapsule
        0.04 0.20
        (vec3 0.06 0.04 0.05)
        (euler 0.0 0.0 (-0.5))
  ]

-- | Multi-color clock — timepiece with hands
clockMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
clockMulti props = iconMulti props
  [ -- Clock face (Primary)
    iconPart Primary SoftVariant $
      primitiveCylinder
        0.28 0.28 0.08
        zero3
        (euler 0.0 0.0 0.0)
  , -- Outer ring (Secondary, chrome)
    iconPart Secondary ChromeVariant $
      primitiveTorus
        0.30 0.03
        zero3
        (euler (pi / 2.0) 0.0 0.0)
  , -- Hour hand (Accent)
    iconPart Accent MetallicVariant $
      primitiveCapsule
        0.03 0.10
        (vec3 0.0 0.05 0.05)
        (euler 0.0 0.0 0.0)
  , -- Minute hand (Accent)
    iconPart Accent MetallicVariant $
      primitiveCapsule
        0.025 0.16
        (vec3 0.05 0.02 0.05)
        (euler 0.0 0.0 (-0.5))
  , -- Center dot (Secondary)
    iconPart Secondary ChromeVariant $
      primitiveSphere 0.04 (vec3 0.0 0.0 0.05)
  ]

-- | Multi-color bar chart — data visualization
chartMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
chartMulti props = iconMulti props
  [ -- Bar 1 - short (Secondary)
    iconPart Secondary SoftVariant $
      primitiveRoundedBox
        (vec3 0.10 0.18 0.10)
        0.02
        (vec3 (-0.16) (-0.10) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Bar 2 - tall (Primary)
    iconPart Primary GlossyVariant $
      primitiveRoundedBox
        (vec3 0.10 0.38 0.10)
        0.02
        (vec3 0.0 0.0 0.0)
        (euler 0.0 0.0 0.0)
  , -- Bar 3 - medium (Accent)
    iconPart Accent GlossyVariant $
      primitiveRoundedBox
        (vec3 0.10 0.28 0.10)
        0.02
        (vec3 0.16 (-0.05) 0.0)
        (euler 0.0 0.0 0.0)
  , -- Base line (Neutral, chrome)
    iconPart Neutral ChromeVariant $
      primitiveBox
        (vec3 0.44 0.02 0.12)
        (vec3 0.0 (-0.20) 0.0)
        (euler 0.0 0.0 0.0)
  ]

-- | Multi-color rocket — launch icon
rocketMulti :: forall w i. Array (Icon3DProp i) -> HH.HTML w i
rocketMulti props = iconMulti props
  [ -- Rocket body (Primary)
    iconPart Primary GlossyVariant $
      primitiveCapsule
        0.10 0.28
        (vec3 0.0 0.05 0.0)
        (euler 0.0 0.0 0.0)
  , -- Nose cone (Accent)
    iconPart Accent GlossyVariant $
      primitiveCone
        0.10 0.16
        (vec3 0.0 0.26 0.0)
        (euler 0.0 0.0 0.0)
  , -- Left fin (Secondary)
    iconPart Secondary SoftVariant $
      primitiveBox
        (vec3 0.12 0.10 0.03)
        (vec3 (-0.12) (-0.14) 0.0)
        (euler 0.0 0.0 0.5)
  , -- Right fin (Secondary)
    iconPart Secondary SoftVariant $
      primitiveBox
        (vec3 0.12 0.10 0.03)
        (vec3 0.12 (-0.14) 0.0)
        (euler 0.0 0.0 (-0.5))
  , -- Exhaust flame (Accent, with glow)
    iconPart Accent GlossyVariant $
      primitiveCone
        0.08 0.14
        (vec3 0.0 (-0.20) 0.0)
        (euler pi 0.0 0.0)
  , -- Window (Neutral, chrome)
    iconPart Neutral ChromeVariant $
      primitiveSphere 0.04 (vec3 0.0 0.10 0.10)
  ]

