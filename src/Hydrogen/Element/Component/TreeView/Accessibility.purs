-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // treeview // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Accessibility — ARIA attributes, announcements, and RTL support.
-- |
-- | ## Accessibility Features
-- |
-- | **ARIA Attributes**:
-- | - role="tree" on container
-- | - role="treeitem" on nodes
-- | - aria-expanded for expandable nodes
-- | - aria-selected for selection state
-- | - aria-level for depth
-- | - aria-posinset/aria-setsize for position
-- |
-- | **Keyboard Navigation**:
-- | - Arrow keys for movement
-- | - Enter/Space for activation
-- | - Home/End for first/last
-- | - Type-ahead search
-- |
-- | **Screen Reader Announcements**:
-- | - Expansion state changes
-- | - Selection changes
-- | - Loading states
-- |
-- | **RTL Support**:
-- | - Horizontal navigation flipped
-- | - Visual layout mirrored
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Node (tree structure)
-- | - TreeView.State (selection, expansion)

module Hydrogen.Element.Component.TreeView.Accessibility
  ( -- * ARIA Attributes
    AriaAttrs
  , ariaAttrs
  , containerAriaAttrs
  , nodeAriaAttrs
  
  -- * Aria Builders
  , ariaExpanded
  , ariaSelected
  , ariaLevel
  , ariaSetSize
  , ariaPosInSet
  , ariaLabel
  , ariaDescribedBy
  , ariaActiveDescendant
  
  -- * Announcements
  , Announcement
  , announcement
  , expandAnnouncement
  , collapseAnnouncement
  , selectAnnouncement
  , loadingAnnouncement
  , errorAnnouncement
  
  -- * Live Regions
  , LiveRegion
  , liveRegion
  , politeRegion
  , assertiveRegion
  , liveRegionAttrs
  
  -- * RTL Support
  , Direction(..)
  , isRTL
  , flipNavigationKey
  , directionAttr
  
  -- * Focus Management
  , focusableAttrs
  , rovingTabIndex
  , focusFirst
  , focusLast
  
  -- * Accessibility Config
  , A11yConfig
  , a11yConfig
  , defaultA11yConfig
  , withReducedMotion
  , withHighContrast
  , withDirection
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  , (<<<)
  , not
  , negate
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element as E

import Hydrogen.Element.Component.TreeView.Types
  ( NodeId
  , Depth
  , unwrapDepth
  , CheckState(Checked, Unchecked, Indeterminate)
  )

import Hydrogen.Element.Component.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeLabel
  , nodeChildren
  , nodeHasChildren
  , siblingNodes
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // aria attributes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Collection of ARIA attributes
type AriaAttrs msg = Array (E.Attribute msg)

-- | Build ARIA attributes for a value
ariaAttrs :: forall msg. Array (E.Attribute msg) -> AriaAttrs msg
ariaAttrs = Array.filter (not <<< isEmptyAttr)
  where
    isEmptyAttr :: E.Attribute msg -> Boolean
    isEmptyAttr _ = false  -- All attributes are valid

-- | ARIA attributes for tree container
containerAriaAttrs ::
  forall msg.
  { multiselectable :: Boolean
  , label :: String
  , activeDescendant :: Maybe NodeId
  } ->
  AriaAttrs msg
containerAriaAttrs config =
  let
    base =
      [ E.role "tree"
      , E.attr "aria-multiselectable" (if config.multiselectable then "true" else "false")
      ]
    
    labelAttr = if config.label == ""
      then []
      else [ E.attr "aria-label" config.label ]
    
    activeAttr = case config.activeDescendant of
      Nothing -> []
      Just nid -> [ E.attr "aria-activedescendant" (show nid) ]
  in
    base <> labelAttr <> activeAttr

-- | ARIA attributes for a tree node
nodeAriaAttrs ::
  forall msg.
  { expanded :: Maybe Boolean    -- ^ Nothing if not expandable
  , selected :: Boolean
  , level :: Int
  , setSize :: Int
  , posInSet :: Int
  , hasChildren :: Boolean
  , disabled :: Boolean
  } ->
  AriaAttrs msg
nodeAriaAttrs config =
  let
    base =
      [ E.role "treeitem"
      , E.attr "aria-level" (show config.level)
      , E.attr "aria-setsize" (show config.setSize)
      , E.attr "aria-posinset" (show config.posInSet)
      , E.attr "aria-selected" (if config.selected then "true" else "false")
      ]
    
    expandedAttr = case config.expanded of
      Nothing -> []
      Just exp -> [ E.attr "aria-expanded" (if exp then "true" else "false") ]
    
    disabledAttr = if config.disabled
      then [ E.attr "aria-disabled" "true" ]
      else []
  in
    base <> expandedAttr <> disabledAttr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // aria builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | aria-expanded attribute
ariaExpanded :: forall msg. Boolean -> E.Attribute msg
ariaExpanded exp = E.attr "aria-expanded" (if exp then "true" else "false")

-- | aria-selected attribute
ariaSelected :: forall msg. Boolean -> E.Attribute msg
ariaSelected sel = E.attr "aria-selected" (if sel then "true" else "false")

-- | aria-level attribute
ariaLevel :: forall msg. Int -> E.Attribute msg
ariaLevel level = E.attr "aria-level" (show level)

-- | aria-setsize attribute
ariaSetSize :: forall msg. Int -> E.Attribute msg
ariaSetSize size = E.attr "aria-setsize" (show size)

-- | aria-posinset attribute
ariaPosInSet :: forall msg. Int -> E.Attribute msg
ariaPosInSet pos = E.attr "aria-posinset" (show pos)

-- | aria-label attribute
ariaLabel :: forall msg. String -> E.Attribute msg
ariaLabel label = E.attr "aria-label" label

-- | aria-describedby attribute
ariaDescribedBy :: forall msg. String -> E.Attribute msg
ariaDescribedBy id = E.attr "aria-describedby" id

-- | aria-activedescendant attribute
ariaActiveDescendant :: forall msg. NodeId -> E.Attribute msg
ariaActiveDescendant nid = E.attr "aria-activedescendant" (show nid)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // announcements
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Announcement for screen readers
type Announcement =
  { text :: String
  , priority :: String  -- ^ "polite" or "assertive"
  }

-- | Create an announcement
announcement :: String -> String -> Announcement
announcement text priority = { text, priority }

-- | Announcement for expansion
expandAnnouncement :: TreeNode -> Announcement
expandAnnouncement node =
  { text: nodeLabel node <> " expanded"
  , priority: "polite"
  }

-- | Announcement for collapse
collapseAnnouncement :: TreeNode -> Announcement
collapseAnnouncement node =
  { text: nodeLabel node <> " collapsed"
  , priority: "polite"
  }

-- | Announcement for selection
selectAnnouncement :: TreeNode -> Announcement
selectAnnouncement node =
  { text: nodeLabel node <> " selected"
  , priority: "polite"
  }

-- | Announcement for loading
loadingAnnouncement :: String -> Announcement
loadingAnnouncement context =
  { text: "Loading " <> context
  , priority: "polite"
  }

-- | Announcement for errors
errorAnnouncement :: String -> Announcement
errorAnnouncement message =
  { text: "Error: " <> message
  , priority: "assertive"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // live regions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | ARIA live region configuration
type LiveRegion =
  { id :: String
  , ariaLive :: String        -- ^ "polite", "assertive", "off"
  , ariaAtomic :: Boolean     -- ^ Announce entire region or just changes
  , ariaRelevant :: String    -- ^ "additions", "removals", "text", "all"
  }

-- | Create a live region
liveRegion :: String -> String -> LiveRegion
liveRegion id ariaLive =
  { id
  , ariaLive
  , ariaAtomic: true
  , ariaRelevant: "additions text"
  }

-- | Polite live region (queued after current speech)
politeRegion :: String -> LiveRegion
politeRegion id = liveRegion id "polite"

-- | Assertive live region (interrupts current speech)
assertiveRegion :: String -> LiveRegion
assertiveRegion id = liveRegion id "assertive"

-- | Get attributes for a live region element
liveRegionAttrs :: forall msg. LiveRegion -> Array (E.Attribute msg)
liveRegionAttrs lr =
  [ E.attr "id" lr.id
  , E.attr "aria-live" lr.ariaLive
  , E.attr "aria-atomic" (if lr.ariaAtomic then "true" else "false")
  , E.attr "aria-relevant" lr.ariaRelevant
  , E.role "status"
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // rtl support
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Text direction
data Direction
  = LTR   -- ^ Left-to-right
  | RTL   -- ^ Right-to-left
  | Auto  -- ^ Auto-detect

derive instance eqDirection :: Eq Direction

instance showDirection :: Show Direction where
  show LTR = "ltr"
  show RTL = "rtl"
  show Auto = "auto"

-- | Check if direction is RTL
isRTL :: Direction -> Boolean
isRTL RTL = true
isRTL _ = false

-- | Flip navigation key for RTL
flipNavigationKey :: Direction -> String -> String
flipNavigationKey dir key =
  if isRTL dir
    then case key of
      "ArrowLeft" -> "ArrowRight"
      "ArrowRight" -> "ArrowLeft"
      other -> other
    else key

-- | Get dir attribute value
directionAttr :: forall msg. Direction -> E.Attribute msg
directionAttr dir = E.attr "dir" (show dir)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // focus management
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Attributes for focusable element
focusableAttrs :: forall msg. Boolean -> Array (E.Attribute msg)
focusableAttrs isFocusable =
  if isFocusable
    then [ E.tabIndex 0 ]
    else [ E.tabIndex (-1) ]

-- | Roving tabindex - only one item in group is focusable
rovingTabIndex :: forall msg. Boolean -> E.Attribute msg
rovingTabIndex isCurrent = E.tabIndex (if isCurrent then 0 else (-1))

-- | Focus first node instruction
focusFirst :: String
focusFirst = "first"

-- | Focus last node instruction  
focusLast :: String
focusLast = "last"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // accessibility config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Accessibility configuration
type A11yConfig =
  { reducedMotion :: Boolean      -- ^ Respect prefers-reduced-motion
  , highContrast :: Boolean       -- ^ Use high contrast colors
  , direction :: Direction        -- ^ Text direction
  , announceChanges :: Boolean    -- ^ Announce state changes to screen readers
  , focusVisible :: Boolean       -- ^ Show visible focus indicators
  , labelledBy :: Maybe String    -- ^ ID of labelling element
  }

-- | Create accessibility config
a11yConfig :: A11yConfig
a11yConfig =
  { reducedMotion: false
  , highContrast: false
  , direction: LTR
  , announceChanges: true
  , focusVisible: true
  , labelledBy: Nothing
  }

-- | Default accessibility config
defaultA11yConfig :: A11yConfig
defaultA11yConfig = a11yConfig

-- | Enable reduced motion
withReducedMotion :: Boolean -> A11yConfig -> A11yConfig
withReducedMotion r c = c { reducedMotion = r }

-- | Enable high contrast
withHighContrast :: Boolean -> A11yConfig -> A11yConfig
withHighContrast h c = c { highContrast = h }

-- | Set text direction
withDirection :: Direction -> A11yConfig -> A11yConfig
withDirection d c = c { direction = d }
