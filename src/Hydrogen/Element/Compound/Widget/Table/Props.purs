-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // table // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Table Props — Property types and builders for table configuration.
-- |
-- | ## Overview
-- |
-- | This module provides the property system for configuring Table widgets:
-- | - TableProps record type with all configurable options
-- | - TableProp modifier functions for clean API
-- | - Default property values

module Hydrogen.Element.Compound.Widget.Table.Props
  ( -- * Props Types
    TableProps
  , TableProp
  , defaultProps
  
  -- * Prop Builders
  , selectable
  , searchable
  , striped
  , bordered
  , compact
  , className
  ) where

import Prelude
  ( (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // prop types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Table widget properties.
type TableProps =
  { selectable :: Boolean
  , searchable :: Boolean
  , striped :: Boolean
  , bordered :: Boolean
  , compact :: Boolean
  , className :: String
  }

-- | Property modifier.
type TableProp = TableProps -> TableProps

-- | Default properties.
defaultProps :: TableProps
defaultProps =
  { selectable: false
  , searchable: false
  , striped: true
  , bordered: true
  , compact: false
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable/disable row selection.
selectable :: Boolean -> TableProp
selectable b props = props { selectable = b }

-- | Enable/disable search box.
searchable :: Boolean -> TableProp
searchable b props = props { searchable = b }

-- | Enable/disable striped rows.
striped :: Boolean -> TableProp
striped b props = props { striped = b }

-- | Enable/disable borders.
bordered :: Boolean -> TableProp
bordered b props = props { bordered = b }

-- | Use compact row spacing.
compact :: Boolean -> TableProp
compact b props = props { compact = b }

-- | Add custom CSS class.
className :: String -> TableProp
className c props = props { className = props.className <> " " <> c }
