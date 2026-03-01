-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // transform-editor // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal helper elements for TransformEditor.
-- |
-- | Contains input fields, toggles, preview widgets, and icons used by the
-- | 2D and 3D transform editors. These are implementation details and not
-- | intended for direct use outside the TransformEditor module.
module Hydrogen.Element.Compound.TransformEditor.Internal
  ( -- * Input Fields
    numberField
  , numberField3D
  , numberFieldRotation
  
  -- * Toggles
  , linkedToggle
  , linkedToggle3D
  , isUniformScale3D
  
  -- * Preview Widgets
  , originPreview
  , originDot
  , gimbalPreview
  
  -- * Icons
  , linkIcon
  ) where

import Prelude
  ( show
  , (<>)
  , (<)
  , (>)
  , (>=)
  , (==)
  , (&&)
  )

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Geometry.Transform as T2D
import Hydrogen.Schema.Geometry.Transform3D as T3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // input // fields
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number field with label and unit
numberField :: forall msg. String -> String -> String -> E.Element msg
numberField labelText valueStr unit =
  E.div_
    [ E.class_ "flex flex-col gap-1" ]
    [ E.label_
        [ E.class_ "text-xs text-muted-foreground" ]
        [ E.text labelText ]
    , E.div_
        [ E.class_ "flex items-center" ]
        [ E.input_
            [ E.class_ "h-7 w-full rounded-l border border-input bg-background px-2 text-xs text-right focus:outline-none focus:ring-1 focus:ring-ring"
            , E.type_ "text"
            , E.value valueStr
            , E.attr "inputmode" "numeric"
            ]
        , E.span_
            [ E.class_ "h-7 px-2 flex items-center rounded-r border border-l-0 border-input bg-muted text-xs text-muted-foreground" ]
            [ E.text unit ]
        ]
    ]

-- | Number field for 3D values (blue tinted to indicate Z axis)
numberField3D :: forall msg. String -> String -> String -> E.Element msg
numberField3D labelText valueStr unit =
  E.div_
    [ E.class_ "flex flex-col gap-1" ]
    [ E.label_
        [ E.class_ "text-xs text-blue-500" ]
        [ E.text labelText ]
    , E.div_
        [ E.class_ "flex items-center" ]
        [ E.input_
            [ E.class_ "h-7 w-full rounded-l border border-blue-500/50 bg-blue-500/5 px-2 text-xs text-right focus:outline-none focus:ring-1 focus:ring-blue-500"
            , E.type_ "text"
            , E.value valueStr
            , E.attr "inputmode" "numeric"
            ]
        , E.span_
            [ E.class_ "h-7 px-2 flex items-center rounded-r border border-l-0 border-blue-500/50 bg-blue-500/10 text-xs text-blue-500" ]
            [ E.text unit ]
        ]
    ]

-- | Number field for rotation (with circular slider potential)
numberFieldRotation :: forall msg. String -> String -> E.Element msg
numberFieldRotation labelText valueStr =
  E.div_
    [ E.class_ "flex flex-col gap-1" ]
    [ E.label_
        [ E.class_ "text-xs text-muted-foreground" ]
        [ E.text labelText ]
    , E.div_
        [ E.class_ "flex items-center" ]
        [ E.input_
            [ E.class_ "h-7 w-full rounded-l border border-input bg-background px-2 text-xs text-right focus:outline-none focus:ring-1 focus:ring-ring"
            , E.type_ "text"
            , E.value valueStr
            , E.attr "inputmode" "numeric"
            ]
        , E.span_
            [ E.class_ "h-7 px-2 flex items-center rounded-r border border-l-0 border-input bg-muted text-xs text-muted-foreground" ]
            [ E.text "°" ]
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // toggles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if 3D scale is uniform (same X, Y, Z)
isUniformScale3D :: T3D.Scale3D -> Boolean
isUniformScale3D sc = 
  let x = T3D.getScale3DX sc
      y = T3D.getScale3DY sc
      z = T3D.getScale3DZ sc
  in x == y && y == z

-- | Linked scale toggle
linkedToggle :: forall msg. Boolean -> E.Element msg
linkedToggle isLinked =
  E.div_
    [ E.class_ "flex items-center gap-2" ]
    [ E.button_
        [ E.classes 
            [ "flex items-center justify-center"
            , "w-6 h-6 rounded"
            , if isLinked then "bg-primary text-primary-foreground" else "bg-muted text-muted-foreground"
            ]
        , E.attr "type" "button"
        ]
        [ linkIcon ]
    , E.span_
        [ E.class_ "text-xs text-muted-foreground" ]
        [ E.text "Constrain proportions" ]
    ]

-- | Linked scale toggle for 3D
linkedToggle3D :: forall msg. Boolean -> E.Element msg
linkedToggle3D isLinked =
  E.div_
    [ E.class_ "flex items-center gap-2" ]
    [ E.button_
        [ E.classes 
            [ "flex items-center justify-center"
            , "w-6 h-6 rounded"
            , if isLinked then "bg-blue-500 text-white" else "bg-muted text-muted-foreground"
            ]
        , E.attr "type" "button"
        ]
        [ linkIcon ]
    , E.span_
        [ E.class_ "text-xs text-muted-foreground" ]
        [ E.text "Constrain proportions (3D)" ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // preview // widgets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Origin preview with 9-point grid
originPreview :: forall msg. T2D.Origin -> Boolean -> E.Element msg
originPreview o showPreviewFlag =
  let
    x = T2D.getOriginX o
    y = T2D.getOriginY o
  in
    E.div_
      [ E.class_ "space-y-2" ]
      [ -- Visual grid
        if showPreviewFlag
          then E.div_
            [ E.classes 
                [ "grid grid-cols-3 gap-1"
                , "w-20 h-20"
                , "border border-border rounded"
                , "p-1"
                ]
            ]
            [ originDot (x < 17.0) (y < 17.0)
            , originDot (x >= 17.0) (y < 17.0)
            , originDot (x > 83.0) (y < 17.0)
            , originDot (x < 17.0) (y >= 17.0)
            , originDot (x >= 17.0) (y >= 17.0)
            , originDot (x > 83.0) (y >= 17.0)
            , originDot (x < 17.0) (y > 83.0)
            , originDot (x >= 17.0) (y > 83.0)
            , originDot (x > 83.0) (y > 83.0)
            ]
          else E.empty
      -- Numeric inputs
      , E.div_
          [ E.class_ "grid grid-cols-2 gap-2" ]
          [ numberField "X" (show x) "%"
          , numberField "Y" (show y) "%"
          ]
      ]

-- | Origin dot
originDot :: forall msg. Boolean -> Boolean -> E.Element msg
originDot xMatch _yMatch =
  let
    isActive = xMatch
  in
    E.div_
      [ E.classes 
          [ "w-5 h-5 rounded-full"
          , "flex items-center justify-center"
          , "cursor-pointer"
          , if isActive then "bg-primary" else "bg-muted hover:bg-muted-foreground/20"
          ]
      ]
      []

-- | Gimbal preview widget
-- |
-- | Visual 3D orientation indicator showing pitch, yaw, roll as three rings.
-- | Runtime will make this interactive for drag-to-rotate.
gimbalPreview :: forall msg. Number -> Number -> Number -> E.Element msg
gimbalPreview pitch yaw roll =
  E.div_
    [ E.classes 
        [ "gimbal-preview"
        , "relative"
        , "w-24 h-24"
        , "mx-auto"
        , "border border-border rounded-full"
        , "bg-muted/20"
        ]
    , E.dataAttr "gimbal" "true"
    , E.dataAttr "pitch" (show pitch)
    , E.dataAttr "yaw" (show yaw)
    , E.dataAttr "roll" (show roll)
    ]
    [ -- Pitch ring (X-axis, red)
      E.div_
        [ E.classes 
            [ "absolute inset-2"
            , "border-2 border-red-500/50 rounded-full"
            , "pointer-events-none"
            ]
        , E.attr "style" ("transform: rotateX(" <> show pitch <> "deg)")
        ]
        []
    -- Yaw ring (Y-axis, green)  
    , E.div_
        [ E.classes 
            [ "absolute inset-4"
            , "border-2 border-green-500/50 rounded-full"
            , "pointer-events-none"
            ]
        , E.attr "style" ("transform: rotateY(" <> show yaw <> "deg)")
        ]
        []
    -- Roll ring (Z-axis, blue)
    , E.div_
        [ E.classes 
            [ "absolute inset-6"
            , "border-2 border-blue-500/50 rounded-full"
            , "pointer-events-none"
            ]
        , E.attr "style" ("transform: rotateZ(" <> show roll <> "deg)")
        ]
        []
    -- Center reference
    , E.div_
        [ E.classes 
            [ "absolute"
            , "left-1/2 top-1/2"
            , "-translate-x-1/2 -translate-y-1/2"
            , "w-2 h-2"
            , "bg-foreground rounded-full"
            ]
        ]
        []
    -- Axis labels
    , E.span_ [ E.class_ "absolute -top-5 left-1/2 -translate-x-1/2 text-[10px] text-red-500" ] [ E.text "P" ]
    , E.span_ [ E.class_ "absolute top-1/2 -right-5 -translate-y-1/2 text-[10px] text-green-500" ] [ E.text "Y" ]
    , E.span_ [ E.class_ "absolute -bottom-5 left-1/2 -translate-x-1/2 text-[10px] text-blue-500" ] [ E.text "R" ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Link icon for proportional scaling
linkIcon :: forall msg. E.Element msg
linkIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "14"
    , E.attr "height" "14"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.path_ [ E.attr "d" "M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71" ]
    , E.path_ [ E.attr "d" "M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71" ]
    ]
