-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // icon // brand
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Icon Brand Integration — Resolve icon colors from brand palettes.
-- |
-- | This module bridges Icon types with the Brand system:
-- |
-- | ```
-- | IconProps.colorRole  ──► resolveIconColor ──► OKLCH
-- |                                │
-- |                                ▼
-- |                          ThemedColorSystem
-- |                          (Brand palette)
-- | ```
-- |
-- | ## Color Resolution Flow
-- |
-- | 1. Icon specifies `ColorRole` (semantic: Primary, Secondary, etc.)
-- | 2. Brand system maps role to `ColorToken` for current theme mode
-- | 3. `ColorToken` contains concrete `OKLCH` value
-- | 4. Renderer uses OKLCH for actual pixel output
-- |
-- | ## Theme Awareness
-- |
-- | Icons automatically adapt to theme changes:
-- | - Same icon definition
-- | - Different theme mode (Light → Dark)
-- | - Different resolved colors
-- | - Same visual semantics
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Color resolution is a pure lookup. No side effects, no network calls.
-- | Given the same (ColorRole, ThemeMode, ThemedColorSystem), you get
-- | the same OKLCH value. Always. Deterministic brand rendering.
-- |
-- | ## Debugging
-- |
-- | This module implements the SHOW_DEBUG_CONVENTION. All types have
-- | Show instances for structured debugging output. IconTheme and
-- | ThemedIcon can be inspected programmatically at runtime.

module Hydrogen.Icon.Brand
  ( -- * Color Resolution
    resolveIconColor
  , resolveIconColors
  , resolvePartColors
  , resolveStyleAwareColor
  , resolveWithFallback
  
  -- * Icon Theming
  , IconTheme(..)
  , mkIconTheme
  , iconThemeMode
  , iconThemeColors
  
  -- * Themed Icon
  , ThemedIcon(..)
  , applyTheme
  , themedIconDefinition
  , themedIconColors
  
  -- * Default Colors
  , defaultIconColor
  , defaultSecondaryColor
  , fallbackColor
  
  -- * Color Role Utilities
  , roleToTokenName
  , suggestSecondaryRole
  , contrastRole
  , roleForStyle
  , roleToString
  
  -- * Comparison (Eq)
  , sameIconTheme
  , sameColorRole
  , samePaletteMode
  
  -- * Filtering
  , filterTokensByPrefix
  , filterTokensByCategory
  , filterTokensByExactRole
  
  -- * Comparison Utilities
  , differentColorRole
  , differentPaletteMode
  , not
  
  -- * String Utilities
  , dropPrefix
  , lastSegment
  
  -- * Role Utilities
  , stripOnPrefix
  , hasOnPrefix
  
  -- * Path Utilities
  , isSinglePath
  , isMultiPath
  , isPartedIcon
  , pathCount
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (/=)
  , (<>)
  , map
  , bind
  , pure
  , (+)
  )

import Data.Maybe (Maybe(Just, Nothing), fromMaybe, maybe)
import Data.Array (head, filter, tail)
import Data.String (take, drop, length, indexOf) as String
import Data.String.Pattern (Pattern(Pattern))

import Hydrogen.Schema.Color.OKLCH (OKLCH, oklch)
import Hydrogen.Schema.Brand.Token (TokenName, mkTokenName, unTokenName)
import Hydrogen.Schema.Brand.Token.Color 
  ( ColorRole
      ( RolePrimary
      , RoleSecondary
      , RoleTertiary
      , RoleAccent
      , RoleNeutral
      , RoleBackground
      , RoleSurface
      , RoleSuccess
      , RoleWarning
      , RoleError
      , RoleInfo
      , RoleOnPrimary
      , RoleOnSecondary
      , RoleOnBackground
      , RoleOnSurface
      , RoleOutline
      , RoleScrim
      )
  , ColorToken
  , colorTokenRole
  , colorTokenName
  , colorTokenValue
  )
import Hydrogen.Schema.Brand.ColorSystem
  ( ThemedColorSystem
  , PaletteMode(ModeLight, ModeDark, ModeContrast, ModeCustom)
  , getPaletteForMode
  , paletteColors
  , filterByRole
  )

import Hydrogen.Icon.Types
  ( IconDefinition
  , IconPath(SinglePath, MultiPath, PartedIcon)
  , IconPart
  , IconProps
  , IconStyle(StyleOutline, StyleSolid, StyleDuotone, StyleFilled)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // color // resolution
-- ═════════════════════════════════════════════════════════════════════════════

-- | Resolve a ColorRole to a concrete OKLCH value.
-- |
-- | Given:
-- | - A semantic role (Primary, Secondary, OnSurface, etc.)
-- | - A theme mode (Light, Dark, Contrast)
-- | - A themed color system (brand palette)
-- |
-- | Returns the OKLCH color for that role in that mode.
-- | Falls back to a default neutral color if role not found in palette.
resolveIconColor 
  :: ColorRole 
  -> PaletteMode 
  -> ThemedColorSystem 
  -> OKLCH
resolveIconColor role mode colorSystem =
  fromMaybe fallbackColor (findColorByRole role mode colorSystem)

-- | Find a color token by role in a themed system.
findColorByRole 
  :: ColorRole 
  -> PaletteMode 
  -> ThemedColorSystem 
  -> Maybe OKLCH
findColorByRole role mode colorSystem = do
  palette <- getPaletteForMode mode colorSystem
  let colors = paletteColors palette
  let matching = filterByRole role colors
  token <- head matching
  pure (colorTokenValue token)

-- | Resolve both primary and secondary colors for an icon.
-- |
-- | Used for duotone icons that need two colors.
resolveIconColors
  :: IconProps
  -> PaletteMode
  -> ThemedColorSystem
  -> { primary :: OKLCH, secondary :: Maybe OKLCH }
resolveIconColors props mode colorSystem =
  { primary: resolveIconColor props.colorRole mode colorSystem
  , secondary: map (\role -> resolveIconColor role mode colorSystem) props.secondaryRole
  }

-- | Resolve colors for all parts of a parted icon.
-- |
-- | Each part has a default role; this resolves all of them.
resolvePartColors
  :: Array IconPart
  -> PaletteMode
  -> ThemedColorSystem
  -> Array { part :: IconPart, color :: OKLCH }
resolvePartColors parts mode colorSystem =
  map resolveOne parts
  where
    resolveOne :: IconPart -> { part :: IconPart, color :: OKLCH }
    resolveOne part =
      { part: part
      , color: resolveIconColor part.defaultRole mode colorSystem
      }

-- | Resolve color with explicit fallback.
-- |
-- | Allows specifying a custom fallback color instead of the default.
resolveWithFallback
  :: OKLCH
  -> ColorRole
  -> PaletteMode
  -> ThemedColorSystem
  -> OKLCH
resolveWithFallback fallback role mode colorSystem =
  case findColorByRole role mode colorSystem of
    Just oklch -> oklch
    Nothing -> fallback

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // icon // theming
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icon theme configuration.
-- |
-- | Combines a palette mode with resolved color tokens.
-- | Implements Show and Eq for debugging and comparison.
newtype IconTheme = IconTheme
  { mode :: PaletteMode
  , colorSystem :: ThemedColorSystem
  }

-- | Show instance for IconTheme.
-- |
-- | Output: "(IconTheme <mode>)"
-- | Per SHOW_DEBUG_CONVENTION - parseable and unambiguous.
instance showIconTheme :: Show IconTheme where
  show (IconTheme t) = "(IconTheme " <> showPaletteMode t.mode <> ")"

-- | Eq instance for IconTheme.
instance eqIconTheme :: Eq IconTheme where
  eq (IconTheme t1) (IconTheme t2) = t1.mode == t2.mode

-- | Create an icon theme.
mkIconTheme :: PaletteMode -> ThemedColorSystem -> IconTheme
mkIconTheme mode colorSystem = IconTheme
  { mode: mode
  , colorSystem: colorSystem
  }

-- | Get theme mode.
iconThemeMode :: IconTheme -> PaletteMode
iconThemeMode (IconTheme t) = t.mode

-- | Get color system.
iconThemeColors :: IconTheme -> ThemedColorSystem
iconThemeColors (IconTheme t) = t.colorSystem

-- | Show palette mode (helper for Show instance).
showPaletteMode :: PaletteMode -> String
showPaletteMode = case _ of
  ModeLight -> "Light"
  ModeDark -> "Dark"
  ModeContrast -> "Contrast"
  ModeCustom name -> "Custom(" <> name <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // themed // icon
-- ═════════════════════════════════════════════════════════════════════════════

-- | An icon with resolved theme colors.
-- |
-- | Contains the original definition plus resolved OKLCH values
-- | for all color roles used in the icon.
-- | Implements Show for debugging.
newtype ThemedIcon = ThemedIcon
  { definition :: IconDefinition
  , props :: IconProps
  , theme :: IconTheme
  , resolvedPrimary :: OKLCH
  , resolvedSecondary :: Maybe OKLCH
  , resolvedParts :: Maybe (Array { part :: IconPart, color :: OKLCH })
  }

-- | Show instance for ThemedIcon.
-- |
-- | Output: "(ThemedIcon <name> <style> primary:<oklch> secondary:<oklch?>)"
-- | Per SHOW_DEBUG_CONVENTION.
instance showThemedIcon :: Show ThemedIcon where
  show (ThemedIcon ti) = "(ThemedIcon "
    <> "name:" <> show ti.definition.name
    <> " style:" <> show ti.props.style
    <> " primary:" <> show ti.resolvedPrimary
    <> " secondary:" <> maybe "none" show ti.resolvedSecondary
    <> ")"

-- | Apply a theme to an icon, resolving all colors.
applyTheme
  :: IconDefinition
  -> IconProps
  -> IconTheme
  -> ThemedIcon
applyTheme definition props (IconTheme theme) =
  ThemedIcon
    { definition: definition
    , props: props
    , theme: IconTheme theme
    , resolvedPrimary: colors.primary
    , resolvedSecondary: colors.secondary
    , resolvedParts: parts
    }
  where
    colors = resolveIconColors props theme.mode theme.colorSystem
    parts = case definition.paths of
      PartedIcon iconParts -> 
        Just (resolvePartColors iconParts theme.mode theme.colorSystem)
      _ -> Nothing

-- | Get definition from themed icon.
themedIconDefinition :: ThemedIcon -> IconDefinition
themedIconDefinition (ThemedIcon ti) = ti.definition

-- | Get resolved colors from themed icon.
themedIconColors :: ThemedIcon -> { primary :: OKLCH, secondary :: Maybe OKLCH }
themedIconColors (ThemedIcon ti) =
  { primary: ti.resolvedPrimary
  , secondary: ti.resolvedSecondary
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // default // colors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default icon color when no theme is available.
-- |
-- | A neutral dark gray suitable for most contexts.
-- | OKLCH: L=0.3, C=0.0, H=0 (achromatic dark)
defaultIconColor :: OKLCH
defaultIconColor = oklch 0.3 0.0 0

-- | Default secondary color for duotone icons.
-- |
-- | A lighter neutral gray.
-- | OKLCH: L=0.6, C=0.0, H=0 (achromatic medium)
defaultSecondaryColor :: OKLCH
defaultSecondaryColor = oklch 0.6 0.0 0

-- | Fallback color when role resolution fails.
-- |
-- | A medium gray that's visible but indicates something is wrong.
-- | OKLCH: L=0.5, C=0.0, H=0 (achromatic medium)
fallbackColor :: OKLCH
fallbackColor = oklch 0.5 0.0 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // color // role // utils
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert a ColorRole to its canonical token name.
-- |
-- | Used for token lookup in color systems.
roleToTokenName :: ColorRole -> Maybe TokenName
roleToTokenName role = mkTokenName (roleToString role)

-- | Convert role to string.
-- |
-- | Returns the canonical string representation for token lookup.
roleToString :: ColorRole -> String
roleToString = case _ of
  RolePrimary -> "color.primary"
  RoleSecondary -> "color.secondary"
  RoleTertiary -> "color.tertiary"
  RoleAccent -> "color.accent"
  RoleNeutral -> "color.neutral"
  RoleBackground -> "color.background"
  RoleSurface -> "color.surface"
  RoleSuccess -> "color.success"
  RoleWarning -> "color.warning"
  RoleError -> "color.error"
  RoleInfo -> "color.info"
  RoleOnPrimary -> "color.on-primary"
  RoleOnSecondary -> "color.on-secondary"
  RoleOnBackground -> "color.on-background"
  RoleOnSurface -> "color.on-surface"
  RoleOutline -> "color.outline"
  RoleScrim -> "color.scrim"

-- | Suggest a secondary role that pairs well with a primary role.
-- |
-- | For duotone icons, this helps choose complementary colors.
suggestSecondaryRole :: ColorRole -> ColorRole
suggestSecondaryRole = case _ of
  RolePrimary -> RoleOnPrimary
  RoleSecondary -> RoleOnSecondary
  RoleAccent -> RolePrimary
  RoleSuccess -> RoleOnSurface
  RoleWarning -> RoleOnSurface
  RoleError -> RoleOnSurface
  RoleInfo -> RoleOnSurface
  RoleOnPrimary -> RolePrimary
  RoleOnSecondary -> RoleSecondary
  RoleOnBackground -> RoleBackground
  RoleOnSurface -> RoleSurface
  _ -> RoleNeutral

-- | Get the contrast role for a given role.
-- |
-- | Returns the "on-X" role for backgrounds, or the background for "on-X" roles.
-- | Useful for ensuring text/icon visibility on colored backgrounds.
contrastRole :: ColorRole -> ColorRole
contrastRole = case _ of
  RolePrimary -> RoleOnPrimary
  RoleSecondary -> RoleOnSecondary
  RoleBackground -> RoleOnBackground
  RoleSurface -> RoleOnSurface
  RoleOnPrimary -> RolePrimary
  RoleOnSecondary -> RoleSecondary
  RoleOnBackground -> RoleBackground
  RoleOnSurface -> RoleSurface
  RoleSuccess -> RoleOnSurface
  RoleWarning -> RoleOnSurface
  RoleError -> RoleOnSurface
  RoleInfo -> RoleOnSurface
  _ -> RoleOnSurface

-- | Determine appropriate color role based on icon style.
-- |
-- | Different styles may warrant different color treatments.
roleForStyle :: IconStyle -> ColorRole -> ColorRole
roleForStyle style baseRole = case style of
  StyleOutline -> case baseRole of
    RolePrimary -> RoleOnSurface
    RoleSecondary -> RoleOnSurface
    _ -> baseRole
  StyleSolid -> baseRole
  StyleFilled -> baseRole
  StyleDuotone -> baseRole

-- | Resolve color with style awareness.
resolveStyleAwareColor
  :: IconStyle
  -> ColorRole
  -> PaletteMode
  -> ThemedColorSystem
  -> OKLCH
resolveStyleAwareColor style role mode colorSystem =
  resolveIconColor (roleForStyle style role) mode colorSystem

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two icon themes are equivalent.
sameIconTheme :: IconTheme -> IconTheme -> Boolean
sameIconTheme (IconTheme t1) (IconTheme t2) = t1.mode == t2.mode

-- | Check if two color roles are the same.
sameColorRole :: ColorRole -> ColorRole -> Boolean
sameColorRole = (==)

-- | Check if two palette modes are the same.
samePaletteMode :: PaletteMode -> PaletteMode -> Boolean
samePaletteMode = (==)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // filtering // utils
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter tokens by prefix.
-- |
-- | Returns tokens whose names start with the given prefix.
-- | Useful for finding all tokens in a category.
filterTokensByPrefix
  :: String
  -> Array ColorToken
  -> Array ColorToken
filterTokensByPrefix prefix tokens =
  filter (\token -> hasPrefix token) tokens
  where
    hasPrefix :: ColorToken -> Boolean
    hasPrefix t =
      let name = unTokenName (colorTokenName t)
          prefixLength = String.length prefix
      in String.take prefixLength name == prefix

-- | Filter tokens by category.
-- |
-- | Returns tokens whose names contain the category string.
-- | Example: filterTokensByCategory "surface" finds all surface tokens.
filterTokensByCategory
  :: String
  -> Array ColorToken
  -> Array ColorToken
filterTokensByCategory category tokens =
  filter (\token -> containsCategory token) tokens
  where
    containsCategory :: ColorToken -> Boolean
    containsCategory token =
      let name = unTokenName (colorTokenName token)
          categoryDot = Pattern ("." <> category <> ".")
      in case String.indexOf categoryDot name of
        Nothing -> false
        Just _ -> true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // comparison // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two color roles are different.
differentColorRole :: ColorRole -> ColorRole -> Boolean
differentColorRole = (/=)

-- | Check if two palette modes are different.
differentPaletteMode :: PaletteMode -> PaletteMode -> Boolean
differentPaletteMode = (/=)

-- | Negate a boolean value.
not :: Boolean -> Boolean
not b = if b then false else true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // string // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the part of a string after the prefix.
-- |
-- | If string starts with prefix, returns the remainder after removing prefix.
-- | Otherwise returns the original string.
dropPrefix :: String -> String -> String
dropPrefix prefix s =
  let prefixLength = String.length prefix
  in if String.take prefixLength s == prefix
     then String.drop prefixLength s
     else s

-- | Get the last segment of a dotted name.
-- |
-- | For "color.primary.success", returns "success".
lastSegment :: String -> String
lastSegment s =
  let dotIndex = String.indexOf (Pattern ".") s
  in case dotIndex of
    Nothing -> s
    Just idx -> String.drop (idx + 1) s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // role // filtering // utils
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the base role without "on-" prefix.
-- |
-- | RoleOnPrimary -> RolePrimary
-- | RoleOnSurface -> RoleSurface
-- | Others unchanged
stripOnPrefix :: ColorRole -> ColorRole
stripOnPrefix role = case role of
  RoleOnPrimary -> RolePrimary
  RoleOnSecondary -> RoleSecondary
  RoleOnBackground -> RoleBackground
  RoleOnSurface -> RoleSurface
  _ -> role

-- | Check if a role has "on-" prefix.
hasOnPrefix :: ColorRole -> Boolean
hasOnPrefix role = case role of
  RoleOnPrimary -> true
  RoleOnSecondary -> true
  RoleOnBackground -> true
  RoleOnSurface -> true
  _ -> false

-- | Filter tokens by role (using colorTokenRole).
filterTokensByExactRole
  :: ColorRole
  -> Array ColorToken
  -> Array ColorToken
filterTokensByExactRole role tokens =
  filter (\t -> colorTokenRole t == role) tokens

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // path // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if icon definition has a single path.
isSinglePath :: IconPath -> Boolean
isSinglePath = case _ of
  SinglePath _ -> true
  _ -> false

-- | Check if icon definition has multiple paths.
isMultiPath :: IconPath -> Boolean
isMultiPath = case _ of
  MultiPath _ -> true
  _ -> false

-- | Check if icon definition has parted paths.
isPartedIcon :: IconPath -> Boolean
isPartedIcon = case _ of
  PartedIcon _ -> true
  _ -> false

-- | Get path count from IconPath.
pathCount :: IconPath -> Int
pathCount = case _ of
  SinglePath _ -> 1
  MultiPath paths -> arrayLength paths
  PartedIcon parts -> arrayLength parts
  where
    arrayLength :: forall a. Array a -> Int
    arrayLength arr = countHelper arr 0
    countHelper :: forall a. Array a -> Int -> Int
    countHelper arr acc = case head arr of
      Nothing -> acc
      Just _ -> countHelper (fromMaybe [] (tail arr)) (acc + 1)
