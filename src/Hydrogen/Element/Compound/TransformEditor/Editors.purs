-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // transform-editor // editors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete 2D and 3D transform editor components.
-- |
-- | These render the full property panel for editing transforms with all
-- | sections (translate, rotate, scale, etc.) combined.
module Hydrogen.Element.Compound.TransformEditor.Editors
  ( transform2DEditor
  , transform3DEditor
  ) where

import Prelude
  ( show
  , ($)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E
import Hydrogen.Schema.Geometry.Transform as T2D
import Hydrogen.Schema.Geometry.Transform3D as T3D
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)
import Hydrogen.Element.Compound.PropertySection as Section
import Hydrogen.Element.Compound.TransformEditor.Props 
  ( Transform2DEditorProp
  , Transform3DEditorProp
  , defaultProps2D
  , defaultProps3D
  )
import Hydrogen.Element.Compound.TransformEditor.Internal
  ( numberField
  , numberField3D
  , numberFieldRotation
  , linkedToggle
  , linkedToggle3D
  , isUniformScale3D
  , originPreview
  , gimbalPreview
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // 2D complete editor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 2D Transform Editor
-- |
-- | Renders all 2D transform properties: translate, rotate, scale, skew, origin.
-- | Each section shows the appropriate controls with bounded values.
-- |
-- | Pure Element — can be rendered to any target.
transform2DEditor :: forall msg. Array (Transform2DEditorProp msg) -> E.Element msg
transform2DEditor propMods =
  let
    props = foldl (\p f -> f p) defaultProps2D propMods
    
    t = case props.transform of
      Just tr -> tr
      Nothing -> T2D.identityTransform
    
    T2D.Transform2D rec = t
  in
    E.div_
      [ E.classes 
          [ "transform-2d-editor"
          , "space-y-2"
          , props.className
          ]
      ]
      [ -- Position/Translate section
        Section.section
          [ Section.label "Position"
          , Section.isOpen true
          ]
          [ case rec.translate of
              Just tr -> 
                E.div_
                  [ E.class_ "grid grid-cols-2 gap-2" ]
                  [ numberField "X" (show $ T2D.getTranslateX tr) "px"
                  , numberField "Y" (show $ T2D.getTranslateY tr) "px"
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "grid grid-cols-2 gap-2" ]
                  [ numberField "X" "0" "px"
                  , numberField "Y" "0" "px"
                  ]
          ]
      
      -- Scale section
      , Section.section
          [ Section.label "Scale"
          , Section.isOpen true
          ]
          [ case rec.scale of
              Just sc ->
                E.div_
                  [ E.class_ "space-y-2" ]
                  [ E.div_
                      [ E.class_ "grid grid-cols-2 gap-2" ]
                      [ numberField "W" (show $ T2D.getScaleX sc) "%"
                      , numberField "H" (show $ T2D.getScaleY sc) "%"
                      ]
                  , linkedToggle (T2D.isUniformScale sc)
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "grid grid-cols-2 gap-2" ]
                  [ numberField "W" "100" "%"
                  , numberField "H" "100" "%"
                  ]
          ]
      
      -- Rotation section
      , Section.section
          [ Section.label "Rotation"
          , Section.isOpen true
          ]
          [ case rec.rotate of
              Just r ->
                numberField "Angle" (show $ unwrapDegrees $ T2D.getRotation r) "°"
              Nothing ->
                numberField "Angle" "0" "°"
          ]
      
      -- Skew section (collapsed by default)
      , Section.section
          [ Section.label "Skew"
          , Section.isOpen false
          ]
          [ case rec.skew of
              Just sk ->
                E.div_
                  [ E.class_ "grid grid-cols-2 gap-2" ]
                  [ numberField "X" (show $ T2D.getSkewX sk) "°"
                  , numberField "Y" (show $ T2D.getSkewY sk) "°"
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "grid grid-cols-2 gap-2" ]
                  [ numberField "X" "0" "°"
                  , numberField "Y" "0" "°"
                  ]
          ]
      
      -- Origin section with visual preview
      , Section.section
          [ Section.label "Transform Origin"
          , Section.isOpen false
          ]
          [ originPreview rec.origin props.showOriginPreview
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // 3D complete editor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 3D Transform Editor
-- |
-- | Renders all 3D transform properties with gimbal control for rotation.
-- | Clearly differentiates from 2D by showing Z axis and perspective.
-- |
-- | Pure Element — can be rendered to any target.
transform3DEditor :: forall msg. Array (Transform3DEditorProp msg) -> E.Element msg
transform3DEditor propMods =
  let
    props = foldl (\p f -> f p) defaultProps3D propMods
    
    t = case props.transform of
      Just tr -> tr
      Nothing -> T3D.identity3D
    
    T3D.Transform3D rec = t
  in
    E.div_
      [ E.classes 
          [ "transform-3d-editor"
          , "space-y-2"
          , props.className
          ]
      ]
      [ -- 3D badge to differentiate from 2D
        E.div_
          [ E.class_ "flex items-center gap-2 mb-2" ]
          [ E.span_
              [ E.classes 
                  [ "inline-flex items-center"
                  , "px-2 py-0.5"
                  , "bg-blue-500/10 text-blue-500"
                  , "text-xs font-medium rounded"
                  ]
              ]
              [ E.text "3D" ]
          , E.span_
              [ E.class_ "text-xs text-muted-foreground" ]
              [ E.text "Z-axis and perspective enabled" ]
          ]
      
      -- Position section (X, Y, Z)
      , Section.section
          [ Section.label "Position"
          , Section.isOpen true
          ]
          [ case rec.translate of
              Just tr ->
                E.div_
                  [ E.class_ "grid grid-cols-3 gap-2" ]
                  [ numberField "X" (show $ T3D.getTranslate3DX tr) "px"
                  , numberField "Y" (show $ T3D.getTranslate3DY tr) "px"
                  , numberField3D "Z" (show $ T3D.getTranslate3DZ tr) "px"
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "grid grid-cols-3 gap-2" ]
                  [ numberField "X" "0" "px"
                  , numberField "Y" "0" "px"
                  , numberField3D "Z" "0" "px"
                  ]
          ]
      
      -- Rotation section with gimbal
      , Section.section
          [ Section.label "Rotation"
          , Section.isOpen true
          ]
          [ case rec.rotate of
              Just r ->
                E.div_
                  [ E.class_ "space-y-3" ]
                  [ -- Gimbal visualization
                    if props.showGimbal
                      then gimbalPreview 
                             (unwrapDegrees $ T3D.getRotateX r) 
                             (unwrapDegrees $ T3D.getRotateY r) 
                             (unwrapDegrees $ T3D.getRotateZ r)
                      else E.empty
                  -- Numeric inputs for precise control
                  , E.div_
                      [ E.class_ "grid grid-cols-3 gap-2" ]
                      [ numberFieldRotation "Pitch" (show $ unwrapDegrees $ T3D.getRotateX r)
                      , numberFieldRotation "Yaw" (show $ unwrapDegrees $ T3D.getRotateY r)
                      , numberFieldRotation "Roll" (show $ unwrapDegrees $ T3D.getRotateZ r)
                      ]
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "space-y-3" ]
                  [ if props.showGimbal then gimbalPreview 0.0 0.0 0.0 else E.empty
                  , E.div_
                      [ E.class_ "grid grid-cols-3 gap-2" ]
                      [ numberFieldRotation "Pitch" "0"
                      , numberFieldRotation "Yaw" "0"
                      , numberFieldRotation "Roll" "0"
                      ]
                  ]
          ]
      
      -- Scale section (X, Y, Z)
      , Section.section
          [ Section.label "Scale"
          , Section.isOpen true
          ]
          [ case rec.scale of
              Just sc ->
                E.div_
                  [ E.class_ "space-y-2" ]
                  [ E.div_
                      [ E.class_ "grid grid-cols-3 gap-2" ]
                      [ numberField "X" (show $ T3D.getScale3DX sc) "%"
                      , numberField "Y" (show $ T3D.getScale3DY sc) "%"
                      , numberField3D "Z" (show $ T3D.getScale3DZ sc) "%"
                      ]
                  , linkedToggle3D (isUniformScale3D sc)
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "grid grid-cols-3 gap-2" ]
                  [ numberField "X" "100" "%"
                  , numberField "Y" "100" "%"
                  , numberField3D "Z" "100" "%"
                  ]
          ]
      
      -- Perspective section (3D only)
      , Section.section
          [ Section.label "Perspective"
          , Section.isOpen false
          ]
          [ perspectiveFields rec.perspective rec.perspectiveOrigin
          ]
      ]

-- | Helper for perspective fields
perspectiveFields :: forall msg. Maybe T3D.Perspective -> T3D.PerspectiveOrigin -> E.Element msg
perspectiveFields maybePerspective origin =
  let
    distanceStr = case maybePerspective of
      Just p -> show $ T3D.getPerspective p
      Nothing -> "1000"
    originX = show $ T3D.getPerspectiveOriginX origin
    originY = show $ T3D.getPerspectiveOriginY origin
  in
    E.div_
      [ E.class_ "space-y-2" ]
      [ numberField "Distance" distanceStr "px"
      , E.div_
          [ E.class_ "grid grid-cols-2 gap-2" ]
          [ numberField "Origin X" originX "%"
          , numberField "Origin Y" originY "%"
          ]
      ]
