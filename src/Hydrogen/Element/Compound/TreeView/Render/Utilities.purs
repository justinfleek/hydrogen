-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // treeview // render // utilities
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Render Utilities — Helper functions for rendering.
-- |
-- | This module provides utility functions used across render submodules:
-- | - Node disabled state checking
-- | - Indent pixel computation
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (Depth)
-- | - TreeView.Node (TreeNode, nodeDisabled)
-- | - Hydrogen.Schema.Dimension.Device (Pixel)

module Hydrogen.Element.Compound.TreeView.Render.Utilities
  ( -- * Utilities
    isNodeDisabled
  , computeIndentPixels
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (*)
  , ($)
  , (==)
  , not
  )

import Data.Maybe (maybe)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Dimension.Device (Pixel, unwrapPixel)
import Hydrogen.Schema.Dimension.Device as Device

import Hydrogen.Element.Compound.TreeView.Types
  ( Depth
  , unwrapDepth
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( TreeNode
  , nodeDisabled
  )

import Hydrogen.Element.Compound.TreeView.Render.Props
  ( TreeViewProps
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a node is disabled
-- |
-- | Returns true if the node has the disabled flag set.
-- | Uses `not` and `$` to properly negate the disabled check.
isNodeDisabled :: TreeNode -> Boolean
isNodeDisabled node = not $ (nodeDisabled node == false)

-- | Compute indentation in pixels for a given depth
-- |
-- | Takes the indentSize from props (or default 20px) and multiplies
-- | by depth level. Returns the value as a Pixel type.
computeIndentPixels :: forall msg. TreeViewProps msg -> Depth -> Pixel
computeIndentPixels props depth =
  let
    baseIndent = maybe (Device.px 20.0) (\p -> p) props.indentSize
    depthMultiplier = Int.toNumber (unwrapDepth depth)
    indentValue = unwrapPixel baseIndent * depthMultiplier
  in
    Device.px indentValue
