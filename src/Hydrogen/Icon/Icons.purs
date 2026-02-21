-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // icons
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen 2D icon set
-- |
-- | Type-safe SVG icons for the Hydrogen framework.
-- | All icons are tree-shakeable — only imported icons are bundled.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Icon.Icons as Icon
-- | import Hydrogen.Icon.Icon as I
-- |
-- | -- Basic usage
-- | Icon.check []
-- |
-- | -- With size
-- | Icon.check [ I.size I.Lg ]
-- |
-- | -- With custom class
-- | Icon.check [ I.className "text-green-500" ]
-- |
-- | -- With accessibility
-- | Icon.check [ I.ariaLabel "Completed" ]
-- | ```
module Hydrogen.Icon.Icons
  ( -- * Actions
    check
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
  , undo
  , redo
    -- * Arrows
  , arrowUp
  , arrowDown
  , arrowLeft
  , arrowRight
  , chevronUp
  , chevronDown
  , chevronLeft
  , chevronRight
  , chevronsUp
  , chevronsDown
  , chevronsLeft
  , chevronsRight
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
  , video
  , music
  , document
  , archive
  , calendar
  , mail
  , phone
  , link
  , globe
  , home
  , settings
  , user
  , users
  , heart
  , star
  , bookmark
  , tag
  , bell
  , lock
  , unlock
  , key
  , eye
  , eyeOff
    -- * Media
  , play
  , pause
  , stop
  , skipBack
  , skipForward
  , volume
  , volumeX
  , mic
  , micOff
  , camera
  , cameraOff
    -- * Layout
  , menu
  , moreHorizontal
  , moreVertical
  , grid
  , list
  , columns
  , sidebar
  , maximize
  , minimize
  , expand
  , shrink
    -- * Data
  , barChart
  , lineChart
  , pieChart
  , trendingUp
  , trendingDown
  , activity
    -- * Misc
  , sun
  , moon
  , zap
  , cloud
  , cloudOff
  , wifi
  , wifiOff
  , bluetooth
  , battery
  , batteryLow
  , batteryCharging
  , power
  , terminal
  , code
  , git
  , gitBranch
  ) where

import Halogen.HTML as HH
import Hydrogen.Icon.Icon (IconProp, iconWith, pathElement, circleElement, lineElement, polylineElement, rectElement)
import Data.Maybe (Maybe(..))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // actions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Checkmark icon
check :: forall w i. Array IconProp -> HH.HTML w i
check props = iconWith props
  [ pathElement "M20 6L9 17l-5-5" ]

-- | X / Close icon
x :: forall w i. Array IconProp -> HH.HTML w i
x props = iconWith props
  [ pathElement "M18 6L6 18"
  , pathElement "M6 6l12 12"
  ]

-- | Plus icon
plus :: forall w i. Array IconProp -> HH.HTML w i
plus props = iconWith props
  [ pathElement "M12 5v14"
  , pathElement "M5 12h14"
  ]

-- | Minus icon
minus :: forall w i. Array IconProp -> HH.HTML w i
minus props = iconWith props
  [ pathElement "M5 12h14" ]

-- | Edit / Pencil icon
edit :: forall w i. Array IconProp -> HH.HTML w i
edit props = iconWith props
  [ pathElement "M11 4H4a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2v-7"
  , pathElement "M18.5 2.5a2.121 2.121 0 0 1 3 3L12 15l-4 1 1-4 9.5-9.5z"
  ]

-- | Trash / Delete icon
trash :: forall w i. Array IconProp -> HH.HTML w i
trash props = iconWith props
  [ pathElement "M3 6h18"
  , pathElement "M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2"
  ]

-- | Copy icon
copy :: forall w i. Array IconProp -> HH.HTML w i
copy props = iconWith props
  [ rectElement { x: 9.0, y: 9.0, width: 13.0, height: 13.0, rx: Just 2.0 }
  , pathElement "M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"
  ]

-- | Save icon
save :: forall w i. Array IconProp -> HH.HTML w i
save props = iconWith props
  [ pathElement "M19 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h11l5 5v11a2 2 0 0 1-2 2z"
  , polylineElement "17 21 17 13 7 13 7 21"
  , polylineElement "7 3 7 8 15 8"
  ]

-- | Download icon
download :: forall w i. Array IconProp -> HH.HTML w i
download props = iconWith props
  [ pathElement "M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"
  , polylineElement "7 10 12 15 17 10"
  , lineElement 12.0 15.0 12.0 3.0
  ]

-- | Upload icon
upload :: forall w i. Array IconProp -> HH.HTML w i
upload props = iconWith props
  [ pathElement "M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"
  , polylineElement "17 8 12 3 7 8"
  , lineElement 12.0 3.0 12.0 15.0
  ]

-- | Search icon
search :: forall w i. Array IconProp -> HH.HTML w i
search props = iconWith props
  [ circleElement 11.0 11.0 8.0
  , lineElement 21.0 21.0 16.65 16.65
  ]

-- | Filter icon
filter :: forall w i. Array IconProp -> HH.HTML w i
filter props = iconWith props
  [ pathElement "M22 3H2l8 9.46V19l4 2v-8.54L22 3z" ]

-- | Refresh icon
refresh :: forall w i. Array IconProp -> HH.HTML w i
refresh props = iconWith props
  [ polylineElement "23 4 23 10 17 10"
  , polylineElement "1 20 1 14 7 14"
  , pathElement "M3.51 9a9 9 0 0 1 14.85-3.36L23 10M1 14l4.64 4.36A9 9 0 0 0 20.49 15"
  ]

-- | Undo icon
undo :: forall w i. Array IconProp -> HH.HTML w i
undo props = iconWith props
  [ pathElement "M3 7v6h6"
  , pathElement "M21 17a9 9 0 0 0-9-9 9 9 0 0 0-6 2.3L3 13"
  ]

-- | Redo icon
redo :: forall w i. Array IconProp -> HH.HTML w i
redo props = iconWith props
  [ pathElement "M21 7v6h-6"
  , pathElement "M3 17a9 9 0 0 1 9-9 9 9 0 0 1 6 2.3l3 2.7"
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // arrows
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Arrow up icon
arrowUp :: forall w i. Array IconProp -> HH.HTML w i
arrowUp props = iconWith props
  [ lineElement 12.0 19.0 12.0 5.0
  , polylineElement "5 12 12 5 19 12"
  ]

-- | Arrow down icon
arrowDown :: forall w i. Array IconProp -> HH.HTML w i
arrowDown props = iconWith props
  [ lineElement 12.0 5.0 12.0 19.0
  , polylineElement "19 12 12 19 5 12"
  ]

-- | Arrow left icon
arrowLeft :: forall w i. Array IconProp -> HH.HTML w i
arrowLeft props = iconWith props
  [ lineElement 19.0 12.0 5.0 12.0
  , polylineElement "12 19 5 12 12 5"
  ]

-- | Arrow right icon
arrowRight :: forall w i. Array IconProp -> HH.HTML w i
arrowRight props = iconWith props
  [ lineElement 5.0 12.0 19.0 12.0
  , polylineElement "12 5 19 12 12 19"
  ]

-- | Chevron up icon
chevronUp :: forall w i. Array IconProp -> HH.HTML w i
chevronUp props = iconWith props
  [ polylineElement "18 15 12 9 6 15" ]

-- | Chevron down icon
chevronDown :: forall w i. Array IconProp -> HH.HTML w i
chevronDown props = iconWith props
  [ polylineElement "6 9 12 15 18 9" ]

-- | Chevron left icon
chevronLeft :: forall w i. Array IconProp -> HH.HTML w i
chevronLeft props = iconWith props
  [ polylineElement "15 18 9 12 15 6" ]

-- | Chevron right icon
chevronRight :: forall w i. Array IconProp -> HH.HTML w i
chevronRight props = iconWith props
  [ polylineElement "9 18 15 12 9 6" ]

-- | Chevrons up icon
chevronsUp :: forall w i. Array IconProp -> HH.HTML w i
chevronsUp props = iconWith props
  [ polylineElement "17 11 12 6 7 11"
  , polylineElement "17 18 12 13 7 18"
  ]

-- | Chevrons down icon
chevronsDown :: forall w i. Array IconProp -> HH.HTML w i
chevronsDown props = iconWith props
  [ polylineElement "7 13 12 18 17 13"
  , polylineElement "7 6 12 11 17 6"
  ]

-- | Chevrons left icon
chevronsLeft :: forall w i. Array IconProp -> HH.HTML w i
chevronsLeft props = iconWith props
  [ polylineElement "11 17 6 12 11 7"
  , polylineElement "18 17 13 12 18 7"
  ]

-- | Chevrons right icon
chevronsRight :: forall w i. Array IconProp -> HH.HTML w i
chevronsRight props = iconWith props
  [ polylineElement "13 17 18 12 13 7"
  , polylineElement "6 17 11 12 6 7"
  ]

-- | External link icon
externalLink :: forall w i. Array IconProp -> HH.HTML w i
externalLink props = iconWith props
  [ pathElement "M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"
  , polylineElement "15 3 21 3 21 9"
  , lineElement 10.0 14.0 21.0 3.0
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // status
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Alert circle icon
alertCircle :: forall w i. Array IconProp -> HH.HTML w i
alertCircle props = iconWith props
  [ circleElement 12.0 12.0 10.0
  , lineElement 12.0 8.0 12.0 12.0
  , lineElement 12.0 16.0 12.01 16.0
  ]

-- | Alert triangle icon
alertTriangle :: forall w i. Array IconProp -> HH.HTML w i
alertTriangle props = iconWith props
  [ pathElement "M10.29 3.86L1.82 18a2 2 0 0 0 1.71 3h16.94a2 2 0 0 0 1.71-3L13.71 3.86a2 2 0 0 0-3.42 0z"
  , lineElement 12.0 9.0 12.0 13.0
  , lineElement 12.0 17.0 12.01 17.0
  ]

-- | Info icon
info :: forall w i. Array IconProp -> HH.HTML w i
info props = iconWith props
  [ circleElement 12.0 12.0 10.0
  , lineElement 12.0 16.0 12.0 12.0
  , lineElement 12.0 8.0 12.01 8.0
  ]

-- | Help circle icon
helpCircle :: forall w i. Array IconProp -> HH.HTML w i
helpCircle props = iconWith props
  [ circleElement 12.0 12.0 10.0
  , pathElement "M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"
  , lineElement 12.0 17.0 12.01 17.0
  ]

-- | Check circle icon
checkCircle :: forall w i. Array IconProp -> HH.HTML w i
checkCircle props = iconWith props
  [ pathElement "M22 11.08V12a10 10 0 1 1-5.93-9.14"
  , polylineElement "22 4 12 14.01 9 11.01"
  ]

-- | X circle icon
xCircle :: forall w i. Array IconProp -> HH.HTML w i
xCircle props = iconWith props
  [ circleElement 12.0 12.0 10.0
  , lineElement 15.0 9.0 9.0 15.0
  , lineElement 9.0 9.0 15.0 15.0
  ]

-- | Clock icon
clock :: forall w i. Array IconProp -> HH.HTML w i
clock props = iconWith props
  [ circleElement 12.0 12.0 10.0
  , polylineElement "12 6 12 12 16 14"
  ]

-- | Loader icon
loader :: forall w i. Array IconProp -> HH.HTML w i
loader props = iconWith props
  [ lineElement 12.0 2.0 12.0 6.0
  , lineElement 12.0 18.0 12.0 22.0
  , lineElement 4.93 4.93 7.76 7.76
  , lineElement 16.24 16.24 19.07 19.07
  , lineElement 2.0 12.0 6.0 12.0
  , lineElement 18.0 12.0 22.0 12.0
  , lineElement 4.93 19.07 7.76 16.24
  , lineElement 16.24 7.76 19.07 4.93
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // objects
-- ═══════════════════════════════════════════════════════════════════════════════

-- | File icon
file :: forall w i. Array IconProp -> HH.HTML w i
file props = iconWith props
  [ pathElement "M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"
  , polylineElement "14 2 14 8 20 8"
  ]

-- | Folder icon
folder :: forall w i. Array IconProp -> HH.HTML w i
folder props = iconWith props
  [ pathElement "M22 19a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h5l2 3h9a2 2 0 0 1 2 2z" ]

-- | Folder open icon
folderOpen :: forall w i. Array IconProp -> HH.HTML w i
folderOpen props = iconWith props
  [ pathElement "M22 19a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h5l2 3h9a2 2 0 0 1 2 2v1"
  , pathElement "M2 10h20v9a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V10z"
  ]

-- | Image icon
image :: forall w i. Array IconProp -> HH.HTML w i
image props = iconWith props
  [ rectElement { x: 3.0, y: 3.0, width: 18.0, height: 18.0, rx: Just 2.0 }
  , circleElement 8.5 8.5 1.5
  , polylineElement "21 15 16 10 5 21"
  ]

-- | Video icon
video :: forall w i. Array IconProp -> HH.HTML w i
video props = iconWith props
  [ pathElement "M22.54 6.42a2.78 2.78 0 0 0-1.94-2C18.88 4 12 4 12 4s-6.88 0-8.6.46a2.78 2.78 0 0 0-1.94 2A29 29 0 0 0 1 11.75a29 29 0 0 0 .46 5.33A2.78 2.78 0 0 0 3.4 19c1.72.46 8.6.46 8.6.46s6.88 0 8.6-.46a2.78 2.78 0 0 0 1.94-2 29 29 0 0 0 .46-5.25 29 29 0 0 0-.46-5.33z"
  , pathElement "M9.75 15.02l5.75-3.27-5.75-3.27v6.54z"
  ]

-- | Music icon
music :: forall w i. Array IconProp -> HH.HTML w i
music props = iconWith props
  [ pathElement "M9 18V5l12-2v13"
  , circleElement 6.0 18.0 3.0
  , circleElement 18.0 16.0 3.0
  ]

-- | Document icon
document :: forall w i. Array IconProp -> HH.HTML w i
document props = iconWith props
  [ pathElement "M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"
  , polylineElement "14 2 14 8 20 8"
  , lineElement 16.0 13.0 8.0 13.0
  , lineElement 16.0 17.0 8.0 17.0
  , polylineElement "10 9 9 9 8 9"
  ]

-- | Archive icon
archive :: forall w i. Array IconProp -> HH.HTML w i
archive props = iconWith props
  [ polylineElement "21 8 21 21 3 21 3 8"
  , rectElement { x: 1.0, y: 3.0, width: 22.0, height: 5.0, rx: Nothing }
  , lineElement 10.0 12.0 14.0 12.0
  ]

-- | Calendar icon
calendar :: forall w i. Array IconProp -> HH.HTML w i
calendar props = iconWith props
  [ rectElement { x: 3.0, y: 4.0, width: 18.0, height: 18.0, rx: Just 2.0 }
  , lineElement 16.0 2.0 16.0 6.0
  , lineElement 8.0 2.0 8.0 6.0
  , lineElement 3.0 10.0 21.0 10.0
  ]

-- | Mail icon
mail :: forall w i. Array IconProp -> HH.HTML w i
mail props = iconWith props
  [ pathElement "M4 4h16c1.1 0 2 .9 2 2v12c0 1.1-.9 2-2 2H4c-1.1 0-2-.9-2-2V6c0-1.1.9-2 2-2z"
  , polylineElement "22 6 12 13 2 6"
  ]

-- | Phone icon
phone :: forall w i. Array IconProp -> HH.HTML w i
phone props = iconWith props
  [ pathElement "M22 16.92v3a2 2 0 0 1-2.18 2 19.79 19.79 0 0 1-8.63-3.07 19.5 19.5 0 0 1-6-6 19.79 19.79 0 0 1-3.07-8.67A2 2 0 0 1 4.11 2h3a2 2 0 0 1 2 1.72 12.84 12.84 0 0 0 .7 2.81 2 2 0 0 1-.45 2.11L8.09 9.91a16 16 0 0 0 6 6l1.27-1.27a2 2 0 0 1 2.11-.45 12.84 12.84 0 0 0 2.81.7A2 2 0 0 1 22 16.92z" ]

-- | Link icon
link :: forall w i. Array IconProp -> HH.HTML w i
link props = iconWith props
  [ pathElement "M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71"
  , pathElement "M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71"
  ]

-- | Globe icon
globe :: forall w i. Array IconProp -> HH.HTML w i
globe props = iconWith props
  [ circleElement 12.0 12.0 10.0
  , lineElement 2.0 12.0 22.0 12.0
  , pathElement "M12 2a15.3 15.3 0 0 1 4 10 15.3 15.3 0 0 1-4 10 15.3 15.3 0 0 1-4-10 15.3 15.3 0 0 1 4-10z"
  ]

-- | Home icon
home :: forall w i. Array IconProp -> HH.HTML w i
home props = iconWith props
  [ pathElement "M3 9l9-7 9 7v11a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z"
  , polylineElement "9 22 9 12 15 12 15 22"
  ]

-- | Settings icon
settings :: forall w i. Array IconProp -> HH.HTML w i
settings props = iconWith props
  [ circleElement 12.0 12.0 3.0
  , pathElement "M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1 0 2.83 2 2 0 0 1-2.83 0l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-2 2 2 2 0 0 1-2-2v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83 0 2 2 0 0 1 0-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82 1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1-2-2 2 2 0 0 1 2-2h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 0-2.83 2 2 0 0 1 2.83 0l.06.06a1.65 1.65 0 0 0 1.82.33H9a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 2-2 2 2 0 0 1 2 2v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 0 2 2 0 0 1 0 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82V9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 2 2 2 2 0 0 1-2 2h-.09a1.65 1.65 0 0 0-1.51 1z"
  ]

-- | User icon
user :: forall w i. Array IconProp -> HH.HTML w i
user props = iconWith props
  [ pathElement "M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"
  , circleElement 12.0 7.0 4.0
  ]

-- | Users icon
users :: forall w i. Array IconProp -> HH.HTML w i
users props = iconWith props
  [ pathElement "M17 21v-2a4 4 0 0 0-4-4H5a4 4 0 0 0-4 4v2"
  , circleElement 9.0 7.0 4.0
  , pathElement "M23 21v-2a4 4 0 0 0-3-3.87"
  , pathElement "M16 3.13a4 4 0 0 1 0 7.75"
  ]

-- | Heart icon
heart :: forall w i. Array IconProp -> HH.HTML w i
heart props = iconWith props
  [ pathElement "M20.84 4.61a5.5 5.5 0 0 0-7.78 0L12 5.67l-1.06-1.06a5.5 5.5 0 0 0-7.78 7.78l1.06 1.06L12 21.23l7.78-7.78 1.06-1.06a5.5 5.5 0 0 0 0-7.78z" ]

-- | Star icon
star :: forall w i. Array IconProp -> HH.HTML w i
star props = iconWith props
  [ pathElement "M12 2l3.09 6.26L22 9.27l-5 4.87 1.18 6.88L12 17.77l-6.18 3.25L7 14.14 2 9.27l6.91-1.01L12 2z" ]

-- | Bookmark icon
bookmark :: forall w i. Array IconProp -> HH.HTML w i
bookmark props = iconWith props
  [ pathElement "M19 21l-7-5-7 5V5a2 2 0 0 1 2-2h10a2 2 0 0 1 2 2z" ]

-- | Tag icon
tag :: forall w i. Array IconProp -> HH.HTML w i
tag props = iconWith props
  [ pathElement "M20.59 13.41l-7.17 7.17a2 2 0 0 1-2.83 0L2 12V2h10l8.59 8.59a2 2 0 0 1 0 2.82z"
  , lineElement 7.0 7.0 7.01 7.0
  ]

-- | Bell icon
bell :: forall w i. Array IconProp -> HH.HTML w i
bell props = iconWith props
  [ pathElement "M18 8A6 6 0 0 0 6 8c0 7-3 9-3 9h18s-3-2-3-9"
  , pathElement "M13.73 21a2 2 0 0 1-3.46 0"
  ]

-- | Lock icon
lock :: forall w i. Array IconProp -> HH.HTML w i
lock props = iconWith props
  [ rectElement { x: 3.0, y: 11.0, width: 18.0, height: 11.0, rx: Just 2.0 }
  , pathElement "M7 11V7a5 5 0 0 1 10 0v4"
  ]

-- | Unlock icon
unlock :: forall w i. Array IconProp -> HH.HTML w i
unlock props = iconWith props
  [ rectElement { x: 3.0, y: 11.0, width: 18.0, height: 11.0, rx: Just 2.0 }
  , pathElement "M7 11V7a5 5 0 0 1 9.9-1"
  ]

-- | Key icon
key :: forall w i. Array IconProp -> HH.HTML w i
key props = iconWith props
  [ pathElement "M21 2l-2 2m-7.61 7.61a5.5 5.5 0 1 1-7.778 7.778 5.5 5.5 0 0 1 7.777-7.777zm0 0L15.5 7.5m0 0l3 3L22 7l-3-3m-3.5 3.5L19 4"
  ]

-- | Eye icon
eye :: forall w i. Array IconProp -> HH.HTML w i
eye props = iconWith props
  [ pathElement "M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z"
  , circleElement 12.0 12.0 3.0
  ]

-- | Eye off icon
eyeOff :: forall w i. Array IconProp -> HH.HTML w i
eyeOff props = iconWith props
  [ pathElement "M17.94 17.94A10.07 10.07 0 0 1 12 20c-7 0-11-8-11-8a18.45 18.45 0 0 1 5.06-5.94M9.9 4.24A9.12 9.12 0 0 1 12 4c7 0 11 8 11 8a18.5 18.5 0 0 1-2.16 3.19m-6.72-1.07a3 3 0 1 1-4.24-4.24"
  , lineElement 1.0 1.0 23.0 23.0
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // media
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Play icon
play :: forall w i. Array IconProp -> HH.HTML w i
play props = iconWith props
  [ pathElement "M5 3l14 9-14 9V3z" ]

-- | Pause icon
pause :: forall w i. Array IconProp -> HH.HTML w i
pause props = iconWith props
  [ rectElement { x: 6.0, y: 4.0, width: 4.0, height: 16.0, rx: Nothing }
  , rectElement { x: 14.0, y: 4.0, width: 4.0, height: 16.0, rx: Nothing }
  ]

-- | Stop icon
stop :: forall w i. Array IconProp -> HH.HTML w i
stop props = iconWith props
  [ rectElement { x: 3.0, y: 3.0, width: 18.0, height: 18.0, rx: Just 2.0 } ]

-- | Skip back icon
skipBack :: forall w i. Array IconProp -> HH.HTML w i
skipBack props = iconWith props
  [ pathElement "M19 20L9 12l10-8v16z"
  , lineElement 5.0 19.0 5.0 5.0
  ]

-- | Skip forward icon
skipForward :: forall w i. Array IconProp -> HH.HTML w i
skipForward props = iconWith props
  [ pathElement "M5 4l10 8-10 8V4z"
  , lineElement 19.0 5.0 19.0 19.0
  ]

-- | Volume icon
volume :: forall w i. Array IconProp -> HH.HTML w i
volume props = iconWith props
  [ pathElement "M11 5L6 9H2v6h4l5 4V5z"
  , pathElement "M19.07 4.93a10 10 0 0 1 0 14.14"
  , pathElement "M15.54 8.46a5 5 0 0 1 0 7.07"
  ]

-- | Volume X icon
volumeX :: forall w i. Array IconProp -> HH.HTML w i
volumeX props = iconWith props
  [ pathElement "M11 5L6 9H2v6h4l5 4V5z"
  , lineElement 23.0 9.0 17.0 15.0
  , lineElement 17.0 9.0 23.0 15.0
  ]

-- | Mic icon
mic :: forall w i. Array IconProp -> HH.HTML w i
mic props = iconWith props
  [ pathElement "M12 1a3 3 0 0 0-3 3v8a3 3 0 0 0 6 0V4a3 3 0 0 0-3-3z"
  , pathElement "M19 10v2a7 7 0 0 1-14 0v-2"
  , lineElement 12.0 19.0 12.0 23.0
  , lineElement 8.0 23.0 16.0 23.0
  ]

-- | Mic off icon
micOff :: forall w i. Array IconProp -> HH.HTML w i
micOff props = iconWith props
  [ lineElement 1.0 1.0 23.0 23.0
  , pathElement "M9 9v3a3 3 0 0 0 5.12 2.12M15 9.34V4a3 3 0 0 0-5.94-.6"
  , pathElement "M17 16.95A7 7 0 0 1 5 12v-2m14 0v2a7 7 0 0 1-.11 1.23"
  , lineElement 12.0 19.0 12.0 23.0
  , lineElement 8.0 23.0 16.0 23.0
  ]

-- | Camera icon
camera :: forall w i. Array IconProp -> HH.HTML w i
camera props = iconWith props
  [ pathElement "M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z"
  , circleElement 12.0 13.0 4.0
  ]

-- | Camera off icon
cameraOff :: forall w i. Array IconProp -> HH.HTML w i
cameraOff props = iconWith props
  [ lineElement 1.0 1.0 23.0 23.0
  , pathElement "M21 21H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h3m3-3h6l2 3h4a2 2 0 0 1 2 2v9.34m-7.72-2.06a4 4 0 1 1-5.56-5.56"
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // layout
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Menu (hamburger) icon
menu :: forall w i. Array IconProp -> HH.HTML w i
menu props = iconWith props
  [ lineElement 3.0 12.0 21.0 12.0
  , lineElement 3.0 6.0 21.0 6.0
  , lineElement 3.0 18.0 21.0 18.0
  ]

-- | More horizontal icon
moreHorizontal :: forall w i. Array IconProp -> HH.HTML w i
moreHorizontal props = iconWith props
  [ circleElement 12.0 12.0 1.0
  , circleElement 19.0 12.0 1.0
  , circleElement 5.0 12.0 1.0
  ]

-- | More vertical icon
moreVertical :: forall w i. Array IconProp -> HH.HTML w i
moreVertical props = iconWith props
  [ circleElement 12.0 12.0 1.0
  , circleElement 12.0 5.0 1.0
  , circleElement 12.0 19.0 1.0
  ]

-- | Grid icon
grid :: forall w i. Array IconProp -> HH.HTML w i
grid props = iconWith props
  [ rectElement { x: 3.0, y: 3.0, width: 7.0, height: 7.0, rx: Nothing }
  , rectElement { x: 14.0, y: 3.0, width: 7.0, height: 7.0, rx: Nothing }
  , rectElement { x: 14.0, y: 14.0, width: 7.0, height: 7.0, rx: Nothing }
  , rectElement { x: 3.0, y: 14.0, width: 7.0, height: 7.0, rx: Nothing }
  ]

-- | List icon
list :: forall w i. Array IconProp -> HH.HTML w i
list props = iconWith props
  [ lineElement 8.0 6.0 21.0 6.0
  , lineElement 8.0 12.0 21.0 12.0
  , lineElement 8.0 18.0 21.0 18.0
  , lineElement 3.0 6.0 3.01 6.0
  , lineElement 3.0 12.0 3.01 12.0
  , lineElement 3.0 18.0 3.01 18.0
  ]

-- | Columns icon
columns :: forall w i. Array IconProp -> HH.HTML w i
columns props = iconWith props
  [ rectElement { x: 3.0, y: 3.0, width: 18.0, height: 18.0, rx: Just 2.0 }
  , lineElement 12.0 3.0 12.0 21.0
  ]

-- | Sidebar icon
sidebar :: forall w i. Array IconProp -> HH.HTML w i
sidebar props = iconWith props
  [ rectElement { x: 3.0, y: 3.0, width: 18.0, height: 18.0, rx: Just 2.0 }
  , lineElement 9.0 3.0 9.0 21.0
  ]

-- | Maximize icon
maximize :: forall w i. Array IconProp -> HH.HTML w i
maximize props = iconWith props
  [ polylineElement "8 3 3 3 3 8"
  , polylineElement "21 8 21 3 16 3"
  , polylineElement "3 16 3 21 8 21"
  , polylineElement "16 21 21 21 21 16"
  ]

-- | Minimize icon
minimize :: forall w i. Array IconProp -> HH.HTML w i
minimize props = iconWith props
  [ polylineElement "8 3 8 8 3 8"
  , polylineElement "21 8 16 8 16 3"
  , polylineElement "8 16 8 21 3 21"
  , polylineElement "16 16 21 16 21 21"
  ]

-- | Expand icon
expand :: forall w i. Array IconProp -> HH.HTML w i
expand props = iconWith props
  [ polylineElement "15 3 21 3 21 9"
  , polylineElement "9 21 3 21 3 15"
  , lineElement 21.0 3.0 14.0 10.0
  , lineElement 3.0 21.0 10.0 14.0
  ]

-- | Shrink icon
shrink :: forall w i. Array IconProp -> HH.HTML w i
shrink props = iconWith props
  [ polylineElement "4 14 10 14 10 20"
  , polylineElement "20 10 14 10 14 4"
  , lineElement 14.0 10.0 21.0 3.0
  , lineElement 3.0 21.0 10.0 14.0
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // data
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Bar chart icon
barChart :: forall w i. Array IconProp -> HH.HTML w i
barChart props = iconWith props
  [ lineElement 12.0 20.0 12.0 10.0
  , lineElement 18.0 20.0 18.0 4.0
  , lineElement 6.0 20.0 6.0 16.0
  ]

-- | Line chart icon
lineChart :: forall w i. Array IconProp -> HH.HTML w i
lineChart props = iconWith props
  [ pathElement "M3 3v18h18"
  , pathElement "M18.7 8l-5.1 5.2-2.8-2.7L7 14.3"
  ]

-- | Pie chart icon
pieChart :: forall w i. Array IconProp -> HH.HTML w i
pieChart props = iconWith props
  [ pathElement "M21.21 15.89A10 10 0 1 1 8 2.83"
  , pathElement "M22 12A10 10 0 0 0 12 2v10z"
  ]

-- | Trending up icon
trendingUp :: forall w i. Array IconProp -> HH.HTML w i
trendingUp props = iconWith props
  [ polylineElement "23 6 13.5 15.5 8.5 10.5 1 18"
  , polylineElement "17 6 23 6 23 12"
  ]

-- | Trending down icon
trendingDown :: forall w i. Array IconProp -> HH.HTML w i
trendingDown props = iconWith props
  [ polylineElement "23 18 13.5 8.5 8.5 13.5 1 6"
  , polylineElement "17 18 23 18 23 12"
  ]

-- | Activity icon
activity :: forall w i. Array IconProp -> HH.HTML w i
activity props = iconWith props
  [ polylineElement "22 12 18 12 15 21 9 3 6 12 2 12" ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // misc
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sun icon
sun :: forall w i. Array IconProp -> HH.HTML w i
sun props = iconWith props
  [ circleElement 12.0 12.0 5.0
  , lineElement 12.0 1.0 12.0 3.0
  , lineElement 12.0 21.0 12.0 23.0
  , lineElement 4.22 4.22 5.64 5.64
  , lineElement 18.36 18.36 19.78 19.78
  , lineElement 1.0 12.0 3.0 12.0
  , lineElement 21.0 12.0 23.0 12.0
  , lineElement 4.22 19.78 5.64 18.36
  , lineElement 18.36 5.64 19.78 4.22
  ]

-- | Moon icon
moon :: forall w i. Array IconProp -> HH.HTML w i
moon props = iconWith props
  [ pathElement "M21 12.79A9 9 0 1 1 11.21 3 7 7 0 0 0 21 12.79z" ]

-- | Zap icon
zap :: forall w i. Array IconProp -> HH.HTML w i
zap props = iconWith props
  [ pathElement "M13 2L3 14h9l-1 8 10-12h-9l1-8z" ]

-- | Cloud icon
cloud :: forall w i. Array IconProp -> HH.HTML w i
cloud props = iconWith props
  [ pathElement "M18 10h-1.26A8 8 0 1 0 9 20h9a5 5 0 0 0 0-10z" ]

-- | Cloud off icon
cloudOff :: forall w i. Array IconProp -> HH.HTML w i
cloudOff props = iconWith props
  [ pathElement "M22.61 16.95A5 5 0 0 0 18 10h-1.26a8 8 0 0 0-7.05-6M5 5a8 8 0 0 0 4 15h9a5 5 0 0 0 1.7-.3"
  , lineElement 1.0 1.0 23.0 23.0
  ]

-- | Wifi icon
wifi :: forall w i. Array IconProp -> HH.HTML w i
wifi props = iconWith props
  [ pathElement "M5 12.55a11 11 0 0 1 14.08 0"
  , pathElement "M1.42 9a16 16 0 0 1 21.16 0"
  , pathElement "M8.53 16.11a6 6 0 0 1 6.95 0"
  , lineElement 12.0 20.0 12.01 20.0
  ]

-- | Wifi off icon
wifiOff :: forall w i. Array IconProp -> HH.HTML w i
wifiOff props = iconWith props
  [ lineElement 1.0 1.0 23.0 23.0
  , pathElement "M16.72 11.06A10.94 10.94 0 0 1 19 12.55"
  , pathElement "M5 12.55a10.94 10.94 0 0 1 5.17-2.39"
  , pathElement "M10.71 5.05A16 16 0 0 1 22.58 9"
  , pathElement "M1.42 9a15.91 15.91 0 0 1 4.7-2.88"
  , pathElement "M8.53 16.11a6 6 0 0 1 6.95 0"
  , lineElement 12.0 20.0 12.01 20.0
  ]

-- | Bluetooth icon
bluetooth :: forall w i. Array IconProp -> HH.HTML w i
bluetooth props = iconWith props
  [ polylineElement "6.5 6.5 17.5 17.5 12 23 12 1 17.5 6.5 6.5 17.5" ]

-- | Battery icon
battery :: forall w i. Array IconProp -> HH.HTML w i
battery props = iconWith props
  [ rectElement { x: 1.0, y: 6.0, width: 18.0, height: 12.0, rx: Just 2.0 }
  , lineElement 23.0 13.0 23.0 11.0
  ]

-- | Battery low icon
batteryLow :: forall w i. Array IconProp -> HH.HTML w i
batteryLow props = iconWith props
  [ rectElement { x: 1.0, y: 6.0, width: 18.0, height: 12.0, rx: Just 2.0 }
  , lineElement 23.0 13.0 23.0 11.0
  , lineElement 5.0 10.0 5.0 14.0
  ]

-- | Battery charging icon
batteryCharging :: forall w i. Array IconProp -> HH.HTML w i
batteryCharging props = iconWith props
  [ pathElement "M5 18H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h3.19M15 6h2a2 2 0 0 1 2 2v8a2 2 0 0 1-2 2h-3.19"
  , lineElement 23.0 13.0 23.0 11.0
  , polylineElement "11 6 7 12 13 12 9 18"
  ]

-- | Power icon
power :: forall w i. Array IconProp -> HH.HTML w i
power props = iconWith props
  [ pathElement "M18.36 6.64a9 9 0 1 1-12.73 0"
  , lineElement 12.0 2.0 12.0 12.0
  ]

-- | Terminal icon
terminal :: forall w i. Array IconProp -> HH.HTML w i
terminal props = iconWith props
  [ polylineElement "4 17 10 11 4 5"
  , lineElement 12.0 19.0 20.0 19.0
  ]

-- | Code icon
code :: forall w i. Array IconProp -> HH.HTML w i
code props = iconWith props
  [ polylineElement "16 18 22 12 16 6"
  , polylineElement "8 6 2 12 8 18"
  ]

-- | Git icon
git :: forall w i. Array IconProp -> HH.HTML w i
git props = iconWith props
  [ circleElement 18.0 18.0 3.0
  , circleElement 6.0 6.0 3.0
  , pathElement "M13 6h3a2 2 0 0 1 2 2v7"
  , lineElement 6.0 9.0 6.0 21.0
  ]

-- | Git branch icon
gitBranch :: forall w i. Array IconProp -> HH.HTML w i
gitBranch props = iconWith props
  [ lineElement 6.0 3.0 6.0 15.0
  , circleElement 18.0 6.0 3.0
  , circleElement 6.0 18.0 3.0
  , pathElement "M18 9a9 9 0 0 1-9 9"
  ]
