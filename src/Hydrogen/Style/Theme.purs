-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // theme
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Theme system for light/dark mode and custom themes
-- |
-- | This module provides:
-- | - Theme mode (light/dark/system)
-- | - Theme CSS variable generation
-- | - Theme switching utilities
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Style.Theme as Theme
-- |
-- | -- Apply dark mode class
-- | Theme.themeClass Theme.Dark  -- "dark"
-- |
-- | -- Generate CSS variables for a theme
-- | Theme.themeCss defaultLightTheme
-- | ```
module Hydrogen.Style.Theme
  ( -- * Theme Mode
    ThemeMode(..)
  , themeClass
  , themeAttr
    -- * Theme Definition
  , Theme
  , defaultLightTheme
  , defaultDarkTheme
    -- * CSS Generation
  , themeCss
  , themeCssVars
    -- * Color Scheme
  , ColorScheme(..)
  , colorScheme
    -- * Dark Mode Variants
  , dark
  , light
  ) where

import Prelude

import Data.Array (intercalate)
import Hydrogen.Style.Color (HSL, toCssVar)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // theme mode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Theme mode
data ThemeMode
  = Light
  | Dark
  | System  -- Follow system preference

derive instance eqThemeMode :: Eq ThemeMode

-- | Get the class name for theme mode
themeClass :: ThemeMode -> String
themeClass = case _ of
  Light -> ""
  Dark -> "dark"
  System -> ""

-- | Get the data attribute for theme mode
themeAttr :: ThemeMode -> String
themeAttr = case _ of
  Light -> "light"
  Dark -> "dark"
  System -> "system"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // theme definition
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete theme definition (shadcn/ui style)
type Theme =
  { -- Base
    background :: HSL
  , foreground :: HSL
    -- Card
  , card :: HSL
  , cardForeground :: HSL
    -- Popover
  , popover :: HSL
  , popoverForeground :: HSL
    -- Primary
  , primary :: HSL
  , primaryForeground :: HSL
    -- Secondary
  , secondary :: HSL
  , secondaryForeground :: HSL
    -- Muted
  , muted :: HSL
  , mutedForeground :: HSL
    -- Accent
  , accent :: HSL
  , accentForeground :: HSL
    -- Destructive
  , destructive :: HSL
  , destructiveForeground :: HSL
    -- Border/Input/Ring
  , border :: HSL
  , input :: HSL
  , ring :: HSL
    -- Chart colors
  , chart1 :: HSL
  , chart2 :: HSL
  , chart3 :: HSL
  , chart4 :: HSL
  , chart5 :: HSL
    -- Radius
  , radius :: String
  }

-- | Default light theme (shadcn/ui Zinc)
defaultLightTheme :: Theme
defaultLightTheme =
  { background: { h: 0.0, s: 0.0, l: 100.0, a: 100.0 }
  , foreground: { h: 240.0, s: 10.0, l: 3.9, a: 100.0 }
  , card: { h: 0.0, s: 0.0, l: 100.0, a: 100.0 }
  , cardForeground: { h: 240.0, s: 10.0, l: 3.9, a: 100.0 }
  , popover: { h: 0.0, s: 0.0, l: 100.0, a: 100.0 }
  , popoverForeground: { h: 240.0, s: 10.0, l: 3.9, a: 100.0 }
  , primary: { h: 240.0, s: 5.9, l: 10.0, a: 100.0 }
  , primaryForeground: { h: 0.0, s: 0.0, l: 98.0, a: 100.0 }
  , secondary: { h: 240.0, s: 4.8, l: 95.9, a: 100.0 }
  , secondaryForeground: { h: 240.0, s: 5.9, l: 10.0, a: 100.0 }
  , muted: { h: 240.0, s: 4.8, l: 95.9, a: 100.0 }
  , mutedForeground: { h: 240.0, s: 3.8, l: 46.1, a: 100.0 }
  , accent: { h: 240.0, s: 4.8, l: 95.9, a: 100.0 }
  , accentForeground: { h: 240.0, s: 5.9, l: 10.0, a: 100.0 }
  , destructive: { h: 0.0, s: 84.2, l: 60.2, a: 100.0 }
  , destructiveForeground: { h: 0.0, s: 0.0, l: 98.0, a: 100.0 }
  , border: { h: 240.0, s: 5.9, l: 90.0, a: 100.0 }
  , input: { h: 240.0, s: 5.9, l: 90.0, a: 100.0 }
  , ring: { h: 240.0, s: 5.9, l: 10.0, a: 100.0 }
  , chart1: { h: 12.0, s: 76.0, l: 61.0, a: 100.0 }
  , chart2: { h: 173.0, s: 58.0, l: 39.0, a: 100.0 }
  , chart3: { h: 197.0, s: 37.0, l: 24.0, a: 100.0 }
  , chart4: { h: 43.0, s: 74.0, l: 66.0, a: 100.0 }
  , chart5: { h: 27.0, s: 87.0, l: 67.0, a: 100.0 }
  , radius: "0.5rem"
  }

-- | Default dark theme (shadcn/ui Zinc)
defaultDarkTheme :: Theme
defaultDarkTheme =
  { background: { h: 240.0, s: 10.0, l: 3.9, a: 100.0 }
  , foreground: { h: 0.0, s: 0.0, l: 98.0, a: 100.0 }
  , card: { h: 240.0, s: 10.0, l: 3.9, a: 100.0 }
  , cardForeground: { h: 0.0, s: 0.0, l: 98.0, a: 100.0 }
  , popover: { h: 240.0, s: 10.0, l: 3.9, a: 100.0 }
  , popoverForeground: { h: 0.0, s: 0.0, l: 98.0, a: 100.0 }
  , primary: { h: 0.0, s: 0.0, l: 98.0, a: 100.0 }
  , primaryForeground: { h: 240.0, s: 5.9, l: 10.0, a: 100.0 }
  , secondary: { h: 240.0, s: 3.7, l: 15.9, a: 100.0 }
  , secondaryForeground: { h: 0.0, s: 0.0, l: 98.0, a: 100.0 }
  , muted: { h: 240.0, s: 3.7, l: 15.9, a: 100.0 }
  , mutedForeground: { h: 240.0, s: 5.0, l: 64.9, a: 100.0 }
  , accent: { h: 240.0, s: 3.7, l: 15.9, a: 100.0 }
  , accentForeground: { h: 0.0, s: 0.0, l: 98.0, a: 100.0 }
  , destructive: { h: 0.0, s: 62.8, l: 30.6, a: 100.0 }
  , destructiveForeground: { h: 0.0, s: 0.0, l: 98.0, a: 100.0 }
  , border: { h: 240.0, s: 3.7, l: 15.9, a: 100.0 }
  , input: { h: 240.0, s: 3.7, l: 15.9, a: 100.0 }
  , ring: { h: 240.0, s: 4.9, l: 83.9, a: 100.0 }
  , chart1: { h: 220.0, s: 70.0, l: 50.0, a: 100.0 }
  , chart2: { h: 160.0, s: 60.0, l: 45.0, a: 100.0 }
  , chart3: { h: 30.0, s: 80.0, l: 55.0, a: 100.0 }
  , chart4: { h: 280.0, s: 65.0, l: 60.0, a: 100.0 }
  , chart5: { h: 340.0, s: 75.0, l: 55.0, a: 100.0 }
  , radius: "0.5rem"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // css generation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate CSS for a theme (for :root or .dark)
themeCss :: Theme -> String
themeCss theme = intercalate "\n"
  [ "  --background: " <> toCssVar theme.background <> ";"
  , "  --foreground: " <> toCssVar theme.foreground <> ";"
  , "  --card: " <> toCssVar theme.card <> ";"
  , "  --card-foreground: " <> toCssVar theme.cardForeground <> ";"
  , "  --popover: " <> toCssVar theme.popover <> ";"
  , "  --popover-foreground: " <> toCssVar theme.popoverForeground <> ";"
  , "  --primary: " <> toCssVar theme.primary <> ";"
  , "  --primary-foreground: " <> toCssVar theme.primaryForeground <> ";"
  , "  --secondary: " <> toCssVar theme.secondary <> ";"
  , "  --secondary-foreground: " <> toCssVar theme.secondaryForeground <> ";"
  , "  --muted: " <> toCssVar theme.muted <> ";"
  , "  --muted-foreground: " <> toCssVar theme.mutedForeground <> ";"
  , "  --accent: " <> toCssVar theme.accent <> ";"
  , "  --accent-foreground: " <> toCssVar theme.accentForeground <> ";"
  , "  --destructive: " <> toCssVar theme.destructive <> ";"
  , "  --destructive-foreground: " <> toCssVar theme.destructiveForeground <> ";"
  , "  --border: " <> toCssVar theme.border <> ";"
  , "  --input: " <> toCssVar theme.input <> ";"
  , "  --ring: " <> toCssVar theme.ring <> ";"
  , "  --chart-1: " <> toCssVar theme.chart1 <> ";"
  , "  --chart-2: " <> toCssVar theme.chart2 <> ";"
  , "  --chart-3: " <> toCssVar theme.chart3 <> ";"
  , "  --chart-4: " <> toCssVar theme.chart4 <> ";"
  , "  --chart-5: " <> toCssVar theme.chart5 <> ";"
  , "  --radius: " <> theme.radius <> ";"
  ]

-- | Generate complete CSS with light and dark themes
themeCssVars :: Theme -> Theme -> String
themeCssVars light' dark' = intercalate "\n"
  [ ":root {"
  , themeCss light'
  , "}"
  , ""
  , ".dark {"
  , themeCss dark'
  , "}"
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // color scheme
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS color-scheme property values
data ColorScheme
  = ColorSchemeLight
  | ColorSchemeDark
  | ColorSchemeNormal

derive instance eqColorScheme :: Eq ColorScheme

-- | Convert color scheme to CSS value
colorScheme :: ColorScheme -> String
colorScheme = case _ of
  ColorSchemeLight -> "light"
  ColorSchemeDark -> "dark"
  ColorSchemeNormal -> "normal"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // dark mode variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Prefix a class with dark: variant
-- |
-- | ```purescript
-- | dark "bg-black"  -- "dark:bg-black"
-- | ```
dark :: String -> String
dark cls = "dark:" <> cls

-- | Prefix a class with light: variant (for dark-mode-first approach)
-- |
-- | Note: Requires Tailwind dark mode to be "class" or "selector"
light :: String -> String
light cls = "light:" <> cls
