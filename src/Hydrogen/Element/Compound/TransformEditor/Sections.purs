-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // transform-editor // sections
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Individual transform section components.
-- |
-- | Standalone sections for editing specific transform properties.
-- | These can be used independently when only a subset of transform
-- | controls are needed.
module Hydrogen.Element.Compound.TransformEditor.Sections
  ( -- * 2D Sections
    translateSection2D
  , rotateSection2D
  , scaleSection2D
  , skewSection2D
  , originSection
  
  -- * 3D Sections
  , translateSection3D
  , rotateSection3D
  , scaleSection3D
  , perspectiveSection
  ) where

import Prelude
  ( show
  , ($)
  )

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Geometry.Transform as T2D
import Hydrogen.Schema.Geometry.Transform3D as T3D
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)
import Hydrogen.Element.Compound.PropertySection as Section
import Hydrogen.Element.Compound.TransformEditor.Internal 
  ( numberField
  , numberField3D
  , numberFieldRotation
  , originPreview
  , gimbalPreview
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 2D // sections
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D Translate section
translateSection2D :: forall msg. T2D.Translate -> (T2D.Translate -> msg) -> E.Element msg
translateSection2D tr _onChange =
  Section.section
    [ Section.label "Position" ]
    [ E.div_
        [ E.class_ "grid grid-cols-2 gap-2" ]
        [ numberField "X" (show $ T2D.getTranslateX tr) "px"
        , numberField "Y" (show $ T2D.getTranslateY tr) "px"
        ]
    ]

-- | 2D Rotate section
rotateSection2D :: forall msg. T2D.Rotate -> (T2D.Rotate -> msg) -> E.Element msg
rotateSection2D r _onChange =
  Section.section
    [ Section.label "Rotation" ]
    [ numberField "Angle" (show $ unwrapDegrees $ T2D.getRotation r) "°"
    ]

-- | 2D Scale section
scaleSection2D :: forall msg. T2D.Scale -> (T2D.Scale -> msg) -> E.Element msg
scaleSection2D sc _onChange =
  Section.section
    [ Section.label "Scale" ]
    [ E.div_
        [ E.class_ "grid grid-cols-2 gap-2" ]
        [ numberField "W" (show $ T2D.getScaleX sc) "%"
        , numberField "H" (show $ T2D.getScaleY sc) "%"
        ]
    ]

-- | 2D Skew section
skewSection2D :: forall msg. T2D.Skew -> (T2D.Skew -> msg) -> E.Element msg
skewSection2D sk _onChange =
  Section.section
    [ Section.label "Skew" ]
    [ E.div_
        [ E.class_ "grid grid-cols-2 gap-2" ]
        [ numberField "X" (show $ T2D.getSkewX sk) "°"
        , numberField "Y" (show $ T2D.getSkewY sk) "°"
        ]
    ]

-- | Origin section with visual preview
originSection :: forall msg. T2D.Origin -> (T2D.Origin -> msg) -> E.Element msg
originSection o _onChange =
  Section.section
    [ Section.label "Transform Origin" ]
    [ originPreview o true
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 3D // sections
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D Translate section
translateSection3D :: forall msg. T3D.Translate3D -> (T3D.Translate3D -> msg) -> E.Element msg
translateSection3D tr _onChange =
  Section.section
    [ Section.label "Position" ]
    [ E.div_
        [ E.class_ "grid grid-cols-3 gap-2" ]
        [ numberField "X" (show $ T3D.getTranslate3DX tr) "px"
        , numberField "Y" (show $ T3D.getTranslate3DY tr) "px"
        , numberField3D "Z" (show $ T3D.getTranslate3DZ tr) "px"
        ]
    ]

-- | 3D Rotate section with gimbal
rotateSection3D :: forall msg. T3D.Rotate3D -> (T3D.Rotate3D -> msg) -> E.Element msg
rotateSection3D r _onChange =
  Section.section
    [ Section.label "Rotation" ]
    [ gimbalPreview (unwrapDegrees $ T3D.getRotateX r) (unwrapDegrees $ T3D.getRotateY r) (unwrapDegrees $ T3D.getRotateZ r)
    , E.div_
        [ E.class_ "grid grid-cols-3 gap-2 mt-2" ]
        [ numberFieldRotation "Pitch" (show $ unwrapDegrees $ T3D.getRotateX r)
        , numberFieldRotation "Yaw" (show $ unwrapDegrees $ T3D.getRotateY r)
        , numberFieldRotation "Roll" (show $ unwrapDegrees $ T3D.getRotateZ r)
        ]
    ]

-- | 3D Scale section
scaleSection3D :: forall msg. T3D.Scale3D -> (T3D.Scale3D -> msg) -> E.Element msg
scaleSection3D sc _onChange =
  Section.section
    [ Section.label "Scale" ]
    [ E.div_
        [ E.class_ "grid grid-cols-3 gap-2" ]
        [ numberField "X" (show $ T3D.getScale3DX sc) "%"
        , numberField "Y" (show $ T3D.getScale3DY sc) "%"
        , numberField3D "Z" (show $ T3D.getScale3DZ sc) "%"
        ]
    ]

-- | Perspective section
perspectiveSection :: forall msg. T3D.Perspective -> (T3D.Perspective -> msg) -> E.Element msg
perspectiveSection p _onChange =
  Section.section
    [ Section.label "Perspective" ]
    [ numberField "Distance" (show $ T3D.getPerspective p) "px"
    ]
