-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // reactive // focusmanagement
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FocusManagement - keyboard navigation and focus state atoms.
-- |
-- | Models focus rings, focus traps, roving tabindex, and
-- | focus scope management for accessible interfaces.

module Hydrogen.Schema.Reactive.FocusManagement
  ( -- * Focus Visibility
    FocusVisibility(..)
  , isFocusVisible
  , isFocusHidden
  , shouldShowRing
  -- * Focus Origin
  , FocusOrigin(..)
  , isKeyboardOrigin
  , isMouseOrigin
  , isTouchOrigin
  , isProgrammaticOrigin
  -- * Focus Ring Style
  , FocusRingStyle(..)
  , isOutlineRing
  , isShadowRing
  , isBorderRing
  -- * Focus Ring (Molecule)
  , FocusRing
  , focusRing
  , defaultFocusRing
  , noFocusRing
  , withRingColor
  , withRingWidth
  , withRingOffset
  -- * Focus Trap Mode
  , FocusTrapMode(..)
  , isHardTrap
  , isSoftTrap
  , isNoTrap
  -- * Focus Trap (Molecule)
  , FocusTrap
  , focusTrap
  , hardTrap
  , softTrap
  , disabledTrap
  , isTrapActive
  , shouldReturnFocus
  -- * Roving Tabindex
  , RovingTabindex
  , rovingTabindex
  , initRoving
  , rovingFocusIndex
  , rovingMoveNext
  , rovingMovePrev
  , rovingMoveFirst
  , rovingMoveLast
  , isRovingFocused
  -- * Focus Scope (Compound)
  , FocusScope
  , focusScope
  , defaultScope
  , modalScope
  , scopeWithTrap
  , isScopeActive
  , scopeFocusedId
  ) where

import Prelude

import Data.Maybe (Maybe(..), isJust)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // focus visibility
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Focus indicator visibility mode
data FocusVisibility
  = FocusVisible    -- ^ Always show focus indicator
  | FocusHidden     -- ^ Never show focus indicator
  | FocusAuto       -- ^ Show only for keyboard navigation (:focus-visible)

derive instance eqFocusVisibility :: Eq FocusVisibility
derive instance ordFocusVisibility :: Ord FocusVisibility

instance showFocusVisibility :: Show FocusVisibility where
  show FocusVisible = "visible"
  show FocusHidden = "hidden"
  show FocusAuto = "auto"

isFocusVisible :: FocusVisibility -> Boolean
isFocusVisible FocusVisible = true
isFocusVisible _ = false

isFocusHidden :: FocusVisibility -> Boolean
isFocusHidden FocusHidden = true
isFocusHidden _ = false

-- | Should show focus ring based on visibility and origin?
shouldShowRing :: FocusVisibility -> FocusOrigin -> Boolean
shouldShowRing FocusVisible _ = true
shouldShowRing FocusHidden _ = false
shouldShowRing FocusAuto origin = isKeyboardOrigin origin

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // focus origin
-- ═══════════════════════════════════════════════════════════════════════════════

-- | How focus was acquired
data FocusOrigin
  = KeyboardOrigin     -- ^ Focus via Tab or arrow keys
  | MouseOrigin        -- ^ Focus via mouse click
  | TouchOrigin        -- ^ Focus via touch
  | ProgrammaticOrigin -- ^ Focus via JavaScript

derive instance eqFocusOrigin :: Eq FocusOrigin
derive instance ordFocusOrigin :: Ord FocusOrigin

instance showFocusOrigin :: Show FocusOrigin where
  show KeyboardOrigin = "keyboard"
  show MouseOrigin = "mouse"
  show TouchOrigin = "touch"
  show ProgrammaticOrigin = "programmatic"

isKeyboardOrigin :: FocusOrigin -> Boolean
isKeyboardOrigin KeyboardOrigin = true
isKeyboardOrigin _ = false

isMouseOrigin :: FocusOrigin -> Boolean
isMouseOrigin MouseOrigin = true
isMouseOrigin _ = false

isTouchOrigin :: FocusOrigin -> Boolean
isTouchOrigin TouchOrigin = true
isTouchOrigin _ = false

isProgrammaticOrigin :: FocusOrigin -> Boolean
isProgrammaticOrigin ProgrammaticOrigin = true
isProgrammaticOrigin _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // focus ring style
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Visual style of focus indicator
data FocusRingStyle
  = OutlineRing    -- ^ CSS outline (default, doesn't affect layout)
  | ShadowRing     -- ^ Box shadow (can be inset)
  | BorderRing     -- ^ Border change (affects layout)

derive instance eqFocusRingStyle :: Eq FocusRingStyle
derive instance ordFocusRingStyle :: Ord FocusRingStyle

instance showFocusRingStyle :: Show FocusRingStyle where
  show OutlineRing = "outline"
  show ShadowRing = "shadow"
  show BorderRing = "border"

isOutlineRing :: FocusRingStyle -> Boolean
isOutlineRing OutlineRing = true
isOutlineRing _ = false

isShadowRing :: FocusRingStyle -> Boolean
isShadowRing ShadowRing = true
isShadowRing _ = false

isBorderRing :: FocusRingStyle -> Boolean
isBorderRing BorderRing = true
isBorderRing _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // focus ring molecule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Focus ring appearance configuration
type FocusRing =
  { style :: FocusRingStyle
  , color :: String           -- ^ CSS color value
  , width :: Number           -- ^ Ring width in pixels
  , offset :: Number          -- ^ Gap between element and ring in pixels
  , visibility :: FocusVisibility
  , enabled :: Boolean
  }

-- | Create focus ring
focusRing :: FocusRingStyle -> String -> Number -> Number -> FocusRing
focusRing style color width offset =
  { style
  , color
  , width
  , offset
  , visibility: FocusAuto
  , enabled: true
  }

-- | Default focus ring (blue outline, auto visibility)
defaultFocusRing :: FocusRing
defaultFocusRing = focusRing OutlineRing "#0066ff" 2.0 2.0

-- | No focus ring (accessibility concern - use sparingly)
noFocusRing :: FocusRing
noFocusRing = defaultFocusRing { enabled = false }

-- | Set ring color
withRingColor :: String -> FocusRing -> FocusRing
withRingColor color ring = ring { color = color }

-- | Set ring width
withRingWidth :: Number -> FocusRing -> FocusRing
withRingWidth width ring = ring { width = width }

-- | Set ring offset
withRingOffset :: Number -> FocusRing -> FocusRing
withRingOffset offset ring = ring { offset = offset }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // focus trap mode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Focus trap behavior
data FocusTrapMode
  = HardTrap   -- ^ Focus cannot leave trap (modal dialogs)
  | SoftTrap   -- ^ Focus returns to trap after leaving (panels)
  | NoTrap     -- ^ No trapping behavior

derive instance eqFocusTrapMode :: Eq FocusTrapMode
derive instance ordFocusTrapMode :: Ord FocusTrapMode

instance showFocusTrapMode :: Show FocusTrapMode where
  show HardTrap = "hard"
  show SoftTrap = "soft"
  show NoTrap = "none"

isHardTrap :: FocusTrapMode -> Boolean
isHardTrap HardTrap = true
isHardTrap _ = false

isSoftTrap :: FocusTrapMode -> Boolean
isSoftTrap SoftTrap = true
isSoftTrap _ = false

isNoTrap :: FocusTrapMode -> Boolean
isNoTrap NoTrap = true
isNoTrap _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // focus trap molecule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Focus trap configuration
type FocusTrap =
  { mode :: FocusTrapMode
  , active :: Boolean
  , returnFocusOnDeactivate :: Boolean
  , initialFocusId :: Maybe String
  , finalFocusId :: Maybe String       -- ^ Where to return focus
  , clickOutsideDeactivates :: Boolean
  , escapeDeactivates :: Boolean
  }

-- | Create focus trap
focusTrap :: FocusTrapMode -> FocusTrap
focusTrap mode =
  { mode
  , active: true
  , returnFocusOnDeactivate: true
  , initialFocusId: Nothing
  , finalFocusId: Nothing
  , clickOutsideDeactivates: false
  , escapeDeactivates: true
  }

-- | Hard trap for modals
hardTrap :: FocusTrap
hardTrap = (focusTrap HardTrap)
  { clickOutsideDeactivates = false
  , escapeDeactivates = false
  }

-- | Soft trap for panels
softTrap :: FocusTrap
softTrap = (focusTrap SoftTrap)
  { clickOutsideDeactivates = true
  , escapeDeactivates = true
  }

-- | Disabled trap
disabledTrap :: FocusTrap
disabledTrap = (focusTrap NoTrap) { active = false }

-- | Is trap currently active?
isTrapActive :: FocusTrap -> Boolean
isTrapActive trap = trap.active && not (isNoTrap trap.mode)

-- | Should return focus when deactivated?
shouldReturnFocus :: FocusTrap -> Boolean
shouldReturnFocus trap = trap.returnFocusOnDeactivate && isJust trap.finalFocusId

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // roving tabindex
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Roving tabindex state for composite widgets (toolbars, menus, listboxes)
type RovingTabindex =
  { focusedIndex :: Int        -- ^ Currently focused item (has tabindex=0)
  , itemCount :: Int           -- ^ Total number of items
  , wrap :: Boolean            -- ^ Wrap at boundaries
  , vertical :: Boolean        -- ^ Use up/down arrows (vs left/right)
  }

-- | Create roving tabindex state
rovingTabindex :: Int -> Int -> Boolean -> Boolean -> RovingTabindex
rovingTabindex focusedIndex itemCount wrap vertical =
  { focusedIndex: clampIndex focusedIndex itemCount
  , itemCount
  , wrap
  , vertical
  }
  where
  clampIndex :: Int -> Int -> Int
  clampIndex idx count
    | count <= 0 = 0
    | idx < 0 = 0
    | idx >= count = count - 1
    | otherwise = idx

-- | Initialize roving state
initRoving :: Int -> RovingTabindex
initRoving count = rovingTabindex 0 count true false

-- | Get currently focused index
rovingFocusIndex :: RovingTabindex -> Int
rovingFocusIndex rt = rt.focusedIndex

-- | Move to next item
rovingMoveNext :: RovingTabindex -> RovingTabindex
rovingMoveNext rt
  | rt.itemCount <= 0 = rt
  | rt.focusedIndex >= rt.itemCount - 1 = 
      if rt.wrap 
        then rt { focusedIndex = 0 }
        else rt
  | otherwise = rt { focusedIndex = rt.focusedIndex + 1 }

-- | Move to previous item
rovingMovePrev :: RovingTabindex -> RovingTabindex
rovingMovePrev rt
  | rt.itemCount <= 0 = rt
  | rt.focusedIndex <= 0 = 
      if rt.wrap 
        then rt { focusedIndex = rt.itemCount - 1 }
        else rt
  | otherwise = rt { focusedIndex = rt.focusedIndex - 1 }

-- | Move to first item
rovingMoveFirst :: RovingTabindex -> RovingTabindex
rovingMoveFirst rt = rt { focusedIndex = 0 }

-- | Move to last item
rovingMoveLast :: RovingTabindex -> RovingTabindex
rovingMoveLast rt
  | rt.itemCount <= 0 = rt
  | otherwise = rt { focusedIndex = rt.itemCount - 1 }

-- | Is specific index the focused one?
isRovingFocused :: Int -> RovingTabindex -> Boolean
isRovingFocused idx rt = idx == rt.focusedIndex

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // focus scope compound
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Focus scope - manages focus within a region
type FocusScope =
  { id :: String                -- ^ Unique scope identifier
  , active :: Boolean           -- ^ Is this scope currently active
  , trap :: FocusTrap           -- ^ Focus trapping configuration
  , ring :: FocusRing           -- ^ Focus ring appearance
  , focusedElementId :: Maybe String  -- ^ Currently focused element
  , lastFocusedId :: Maybe String     -- ^ Last focused element (for restoration)
  , parentScopeId :: Maybe String     -- ^ Parent scope (for nesting)
  }

-- | Create focus scope
focusScope :: String -> FocusTrap -> FocusRing -> FocusScope
focusScope id trap ring =
  { id
  , active: true
  , trap
  , ring
  , focusedElementId: Nothing
  , lastFocusedId: Nothing
  , parentScopeId: Nothing
  }

-- | Default focus scope (no trap)
defaultScope :: String -> FocusScope
defaultScope id = focusScope id disabledTrap defaultFocusRing

-- | Modal focus scope (hard trap)
modalScope :: String -> FocusScope
modalScope id = focusScope id hardTrap defaultFocusRing

-- | Add trap to existing scope
scopeWithTrap :: FocusTrap -> FocusScope -> FocusScope
scopeWithTrap trap scope = scope { trap = trap }

-- | Is scope active?
isScopeActive :: FocusScope -> Boolean
isScopeActive scope = scope.active

-- | Get focused element ID in scope
scopeFocusedId :: FocusScope -> Maybe String
scopeFocusedId scope = scope.focusedElementId
