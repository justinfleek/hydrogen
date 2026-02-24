-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // sheet
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sheet component
-- |
-- | A slide-out panel that extends from the edge of the viewport.
-- | Similar to a drawer but with more flexibility in sizing and styling.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Sheet as Sheet
-- |
-- | -- Basic sheet from right
-- | Sheet.sheet
-- |   [ Sheet.open state.showSheet
-- |   , Sheet.side Sheet.Right
-- |   , Sheet.onClose HandleClose
-- |   ]
-- |   [ Sheet.sheetHeader []
-- |       [ Sheet.sheetTitle [] [ HH.text "Settings" ]
-- |       , Sheet.sheetDescription [] [ HH.text "Configure your preferences" ]
-- |       ]
-- |   , Sheet.sheetContent []
-- |       [ -- Your content here
-- |       ]
-- |   , Sheet.sheetFooter []
-- |       [ Button.button [] [ HH.text "Save" ] ]
-- |   ]
-- |
-- | -- Sheet from bottom (like mobile bottom sheet)
-- | Sheet.sheet
-- |   [ Sheet.open state.showBottomSheet
-- |   , Sheet.side Sheet.Bottom
-- |   , Sheet.size "h-1/2"
-- |   ]
-- |   [ -- Content
-- |   ]
-- | ```
module Hydrogen.Component.Sheet
  ( -- * Sheet Components
    sheet
  , sheetTrigger
  , sheetOverlay
  , sheetContent
  , sheetHeader
  , sheetFooter
  , sheetTitle
  , sheetDescription
  , sheetClose
    -- * Props
  , SheetProps
  , SheetProp
  , defaultProps
    -- * Prop Builders
  , open
  , side
  , size
  , closeOnOverlay
  , closeOnEscape
  , showClose
  , className
  , onClose
  , onOpenChange
    -- * Types
  , Side(Top, Right, Bottom, Left)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Side from which the sheet appears
data Side
  = Top
  | Right
  | Bottom
  | Left

derive instance eqSide :: Eq Side

-- | Get side-specific classes for content positioning
sideContentClasses :: Side -> String
sideContentClasses = case _ of
  Top -> "inset-x-0 top-0 border-b"
  Right -> "inset-y-0 right-0 h-full border-l"
  Bottom -> "inset-x-0 bottom-0 border-t"
  Left -> "inset-y-0 left-0 h-full border-r"

-- | Get side-specific animation classes
sideAnimationClasses :: Side -> String
sideAnimationClasses = case _ of
  Top -> "slide-in-from-top"
  Right -> "slide-in-from-right"
  Bottom -> "slide-in-from-bottom"
  Left -> "slide-in-from-left"

-- | Get default size for each side
defaultSizeForSide :: Side -> String
defaultSizeForSide = case _ of
  Top -> "h-auto max-h-screen"
  Right -> "w-3/4 sm:max-w-sm"
  Bottom -> "h-auto max-h-screen"
  Left -> "w-3/4 sm:max-w-sm"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sheet properties
type SheetProps i =
  { open :: Boolean
  , side :: Side
  , size :: Maybe String
  , closeOnOverlay :: Boolean
  , closeOnEscape :: Boolean
  , showClose :: Boolean
  , className :: String
  , onClose :: Maybe i
  , onOpenChange :: Maybe (Boolean -> i)
  }

-- | Property modifier
type SheetProp i = SheetProps i -> SheetProps i

-- | Default properties
defaultProps :: forall i. SheetProps i
defaultProps =
  { open: false
  , side: Right
  , size: Nothing
  , closeOnOverlay: true
  , closeOnEscape: true
  , showClose: true
  , className: ""
  , onClose: Nothing
  , onOpenChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set open state
open :: forall i. Boolean -> SheetProp i
open o props = props { open = o }

-- | Set side
side :: forall i. Side -> SheetProp i
side s props = props { side = s }

-- | Set custom size (width for left/right, height for top/bottom)
size :: forall i. String -> SheetProp i
size s props = props { size = Just s }

-- | Close on overlay click
closeOnOverlay :: forall i. Boolean -> SheetProp i
closeOnOverlay c props = props { closeOnOverlay = c }

-- | Close on escape key
closeOnEscape :: forall i. Boolean -> SheetProp i
closeOnEscape c props = props { closeOnEscape = c }

-- | Show close button
showClose :: forall i. Boolean -> SheetProp i
showClose s props = props { showClose = s }

-- | Add custom class
className :: forall i. String -> SheetProp i
className c props = props { className = props.className <> " " <> c }

-- | Set close handler
onClose :: forall i. i -> SheetProp i
onClose handler props = props { onClose = Just handler }

-- | Set open change handler
onOpenChange :: forall i. (Boolean -> i) -> SheetProp i
onOpenChange handler props = props { onOpenChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Overlay classes
overlayClasses :: String
overlayClasses =
  "fixed inset-0 z-50 bg-black/80 animate-in fade-in-0"

-- | Content base classes
contentBaseClasses :: String
contentBaseClasses =
  "fixed z-50 gap-4 bg-background p-6 shadow-lg transition ease-in-out animate-in duration-300"

-- | Header classes
headerClasses :: String
headerClasses =
  "flex flex-col space-y-2"

-- | Footer classes
footerClasses :: String
footerClasses =
  "flex flex-col-reverse sm:flex-row sm:justify-end sm:space-x-2"

-- | Title classes
titleClasses :: String
titleClasses =
  "text-lg font-semibold text-foreground"

-- | Description classes
descriptionClasses :: String
descriptionClasses =
  "text-sm text-muted-foreground"

-- | Close button classes
closeButtonClasses :: String
closeButtonClasses =
  "absolute right-4 top-4 rounded-sm opacity-70 ring-offset-background transition-opacity hover:opacity-100 focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2 disabled:pointer-events-none"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sheet trigger (for use with uncontrolled pattern)
sheetTrigger :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
sheetTrigger children =
  HH.span
    [ cls [ "inline-block" ] ]
    children

-- | Sheet overlay (standalone)
sheetOverlay :: forall w i. Maybe i -> HH.HTML w i
sheetOverlay closeHandler =
  let
    clickHandler = case closeHandler of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> []
  in
    HH.div
      ( [ cls [ overlayClasses ] ] <> clickHandler )
      []

-- | Sheet content wrapper (standalone)
sheetContent :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
sheetContent customClass children =
  HH.div
    [ cls [ contentBaseClasses, customClass ]
    , ARIA.role "dialog"
    ]
    children

-- | Sheet header
sheetHeader :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
sheetHeader customClass children =
  HH.div
    [ cls [ headerClasses, customClass ] ]
    children

-- | Sheet footer
sheetFooter :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
sheetFooter customClass children =
  HH.div
    [ cls [ footerClasses, customClass ] ]
    children

-- | Sheet title
sheetTitle :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
sheetTitle customClass children =
  HH.h2
    [ cls [ titleClasses, customClass ] ]
    children

-- | Sheet description
sheetDescription :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
sheetDescription customClass children =
  HH.p
    [ cls [ descriptionClasses, customClass ] ]
    children

-- | Sheet close button
sheetClose :: forall w i. Maybe i -> HH.HTML w i
sheetClose closeHandler =
  let
    clickHandler = case closeHandler of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> []
  in
    HH.button
      ( [ cls [ closeButtonClasses ]
        , HP.type_ HP.ButtonButton
        , ARIA.label "Close"
        ] <> clickHandler
      )
      [ closeIcon ]

-- | Full sheet component
sheet :: forall w i. Array (SheetProp i) -> Array (HH.HTML w i) -> HH.HTML w i
sheet propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Size classes
    sizeClass = case props.size of
      Just s -> s
      Nothing -> defaultSizeForSide props.side
    
    -- Content classes
    contentCls = 
      contentBaseClasses 
      <> " " <> sideContentClasses props.side
      <> " " <> sideAnimationClasses props.side
      <> " " <> sizeClass
      <> " " <> props.className
    
    -- Overlay handler
    overlayHandler = 
      if props.closeOnOverlay
        then props.onClose
        else Nothing
  in
    if not props.open
      then HH.text ""
      else
        HH.div
          [ cls [ "relative z-50" ] ]
          [ -- Overlay
            sheetOverlay overlayHandler
          -- Content
          , HH.div
              [ cls [ contentCls ]
              , ARIA.role "dialog"
              , ARIA.modal "true"
              ]
              ( children <>
                -- Close button
                ( if props.showClose
                    then [ sheetClose props.onClose ]
                    else []
                )
              )
          ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Close (X) icon
closeIcon :: forall w i. HH.HTML w i
closeIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "18"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "6"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "6"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "18"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    ]
