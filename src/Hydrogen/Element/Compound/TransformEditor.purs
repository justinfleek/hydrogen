-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // transform-editor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TransformEditor — Property panel for 2D and 3D transforms.
-- |
-- | Provides unified UI for editing transforms with clear visual differentiation
-- | between 2D operations (X, Y, rotation) and 3D operations (Z axis, perspective,
-- | gimbal controls).
-- |
-- | ## Design Philosophy
-- |
-- | At billion-agent scale, transform editing must be:
-- | - **Type-safe**: 2D and 3D are distinct types with distinct UI
-- | - **Bounded**: All values clamped to valid ranges
-- | - **Visual**: 3D includes gimbal preview, 2D shows transform origin
-- | - **Composable**: Each section can be used independently
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.TransformEditor as TE
-- | 
-- | -- 2D transform editor
-- | TE.transform2DEditor
-- |   [ TE.transform2D state.transform
-- |   , TE.onTransform2DChange UpdateTransform
-- |   ]
-- |
-- | -- 3D transform editor with gimbal
-- | TE.transform3DEditor
-- |   [ TE.transform3D state.transform3D
-- |   , TE.onTransform3DChange UpdateTransform3D
-- |   , TE.showGimbal true
-- |   ]
-- |
-- | -- Standalone sections
-- | TE.translateSection2D state.translate ChangeTranslate
-- | TE.rotateSection3D state.rotate ChangeRotate  -- shows gimbal
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `TransformEditor.Props` — Types, defaults, and prop builders
-- | - `TransformEditor.Editors` — Complete 2D and 3D editor components
-- | - `TransformEditor.Sections` — Individual section components
-- | - `TransformEditor.Internal` — Helper elements (not re-exported)
module Hydrogen.Element.Compound.TransformEditor
  ( -- * Props and Types
    module Props
  
  -- * Complete Editors
  , module Editors
  
  -- * Individual Sections
  , module Sections
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.TransformEditor.Props 
  ( Transform2DEditorProps
  , Transform2DEditorProp
  , Transform3DEditorProps
  , Transform3DEditorProp
  , defaultProps2D
  , defaultProps3D
  , transform2D
  , onTransform2DChange
  , transform3D
  , onTransform3DChange
  , showGimbal
  , showOriginPreview
  , compactMode
  , className
  ) as Props

import Hydrogen.Element.Compound.TransformEditor.Editors
  ( transform2DEditor
  , transform3DEditor
  ) as Editors

import Hydrogen.Element.Compound.TransformEditor.Sections
  ( translateSection2D
  , rotateSection2D
  , scaleSection2D
  , skewSection2D
  , originSection
  , translateSection3D
  , rotateSection3D
  , scaleSection3D
  , perspectiveSection
  ) as Sections
