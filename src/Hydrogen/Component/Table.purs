-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // table
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Table component
-- |
-- | Styled data table components.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Table as Table
-- |
-- | Table.table []
-- |   [ Table.tableHeader []
-- |       [ Table.tableRow []
-- |           [ Table.tableHead [] [ HH.text "Name" ]
-- |           , Table.tableHead [] [ HH.text "Status" ]
-- |           ]
-- |       ]
-- |   , Table.tableBody []
-- |       [ Table.tableRow []
-- |           [ Table.tableCell [] [ HH.text "John" ]
-- |           , Table.tableCell [] [ HH.text "Active" ]
-- |           ]
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Component.Table
  ( -- * Table Components
    table
  , tableHeader
  , tableBody
  , tableFooter
  , tableRow
  , tableHead
  , tableCell
  , tableCaption
    -- * Props
  , TableProps
  , TableProp
  , className
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type TableProps = { className :: String }
type TableProp = TableProps -> TableProps

defaultProps :: TableProps
defaultProps = { className: "" }

-- | Add custom class
className :: String -> TableProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Table container
table :: forall w i. Array TableProp -> Array (HH.HTML w i) -> HH.HTML w i
table propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative w-full overflow-auto" ] ]
    [ HH.table
        [ cls [ "w-full caption-bottom text-sm", props.className ] ]
        children
    ]

-- | Table header
tableHeader :: forall w i. Array TableProp -> Array (HH.HTML w i) -> HH.HTML w i
tableHeader propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.thead
    [ cls [ "[&_tr]:border-b", props.className ] ]
    children

-- | Table body
tableBody :: forall w i. Array TableProp -> Array (HH.HTML w i) -> HH.HTML w i
tableBody propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.tbody
    [ cls [ "[&_tr:last-child]:border-0", props.className ] ]
    children

-- | Table footer
tableFooter :: forall w i. Array TableProp -> Array (HH.HTML w i) -> HH.HTML w i
tableFooter propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.tfoot
    [ cls [ "border-t bg-muted/50 font-medium [&>tr]:last:border-b-0", props.className ] ]
    children

-- | Table row
tableRow :: forall w i. Array TableProp -> Array (HH.HTML w i) -> HH.HTML w i
tableRow propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.tr
    [ cls [ "border-b transition-colors hover:bg-muted/50 data-[state=selected]:bg-muted", props.className ] ]
    children

-- | Table header cell
tableHead :: forall w i. Array TableProp -> Array (HH.HTML w i) -> HH.HTML w i
tableHead propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.th
    [ cls [ "h-12 px-4 text-left align-middle font-medium text-muted-foreground [&:has([role=checkbox])]:pr-0", props.className ] ]
    children

-- | Table cell
tableCell :: forall w i. Array TableProp -> Array (HH.HTML w i) -> HH.HTML w i
tableCell propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.td
    [ cls [ "p-4 align-middle [&:has([role=checkbox])]:pr-0", props.className ] ]
    children

-- | Table caption
tableCaption :: forall w i. Array TableProp -> Array (HH.HTML w i) -> HH.HTML w i
tableCaption propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.caption
    [ cls [ "mt-4 text-sm text-muted-foreground", props.className ] ]
    children
