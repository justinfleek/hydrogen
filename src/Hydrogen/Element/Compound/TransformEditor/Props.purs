-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // transform-editor // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Type definitions, defaults, and property builders for TransformEditor.
-- |
-- | Provides the configuration types for both 2D and 3D transform editors,
-- | along with modifier functions for building property arrays.
module Hydrogen.Element.Compound.TransformEditor.Props
  ( -- * 2D Types
    Transform2DEditorProps
  , Transform2DEditorProp
  , defaultProps2D
  
  -- * 3D Types
  , Transform3DEditorProps
  , Transform3DEditorProp
  , defaultProps3D
  
  -- * 2D Prop Builders
  , transform2D
  , onTransform2DChange
  , showOriginPreview
  
  -- * 3D Prop Builders
  , transform3D
  , onTransform3DChange
  , showGimbal
  
  -- * Shared Prop Builders
  , compactMode
  , className
  ) where

import Prelude
  ( (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Schema.Geometry.Transform as T2D
import Hydrogen.Schema.Geometry.Transform3D as T3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // 2D // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D Transform Editor properties
type Transform2DEditorProps msg =
  { transform :: Maybe T2D.Transform2D
  , onChange :: Maybe (T2D.Transform2D -> msg)
  , showOriginPreview :: Boolean
  , compact :: Boolean
  , className :: String
  }

-- | 2D property modifier
type Transform2DEditorProp msg = Transform2DEditorProps msg -> Transform2DEditorProps msg

-- | Default 2D properties
defaultProps2D :: forall msg. Transform2DEditorProps msg
defaultProps2D =
  { transform: Nothing
  , onChange: Nothing
  , showOriginPreview: true
  , compact: false
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // 3D // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D Transform Editor properties
type Transform3DEditorProps msg =
  { transform :: Maybe T3D.Transform3D
  , onChange :: Maybe (T3D.Transform3D -> msg)
  , showGimbal :: Boolean
  , compact :: Boolean
  , className :: String
  }

-- | 3D property modifier
type Transform3DEditorProp msg = Transform3DEditorProps msg -> Transform3DEditorProps msg

-- | Default 3D properties
defaultProps3D :: forall msg. Transform3DEditorProps msg
defaultProps3D =
  { transform: Nothing
  , onChange: Nothing
  , showGimbal: true
  , compact: false
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // 2D // prop // builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set 2D transform
transform2D :: forall msg. T2D.Transform2D -> Transform2DEditorProp msg
transform2D t props = props { transform = Just t }

-- | Set 2D change handler
onTransform2DChange :: forall msg. (T2D.Transform2D -> msg) -> Transform2DEditorProp msg
onTransform2DChange handler props = props { onChange = Just handler }

-- | Show origin preview for 2D transforms
showOriginPreview :: forall msg. Boolean -> Transform2DEditorProp msg
showOriginPreview o props = props { showOriginPreview = o }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // 3D // prop // builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set 3D transform
transform3D :: forall msg. T3D.Transform3D -> Transform3DEditorProp msg
transform3D t props = props { transform = Just t }

-- | Set 3D change handler
onTransform3DChange :: forall msg. (T3D.Transform3D -> msg) -> Transform3DEditorProp msg
onTransform3DChange handler props = props { onChange = Just handler }

-- | Show gimbal preview for 3D rotation
showGimbal :: forall msg. Boolean -> Transform3DEditorProp msg
showGimbal g props = props { showGimbal = g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // shared // prop // builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable compact mode
compactMode :: forall a. { compact :: Boolean | a } -> { compact :: Boolean | a }
compactMode props = props { compact = true }

-- | Add custom class
className :: forall msg. String -> Transform2DEditorProp msg
className c props = props { className = props.className <> " " <> c }
