-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // footer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Footer component
-- |
-- | A responsive footer with configurable columns, links, and bottom bar.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.Footer as Footer
-- |
-- | -- Simple footer
-- | Footer.footer []
-- |   [ Footer.footerBottom []
-- |       [ HH.text "© 2024 MyCompany. All rights reserved." ]
-- |   ]
-- |
-- | -- Multi-column footer
-- | Footer.footer []
-- |   [ Footer.footerColumns []
-- |       [ Footer.footerColumn
-- |           { title: "Product"
-- |           , links: 
-- |               [ { label: "Features", href: "/features" }
-- |               , { label: "Pricing", href: "/pricing" }
-- |               ]
-- |           }
-- |       , Footer.footerColumn
-- |           { title: "Company"
-- |           , links:
-- |               [ { label: "About", href: "/about" }
-- |               , { label: "Blog", href: "/blog" }
-- |               ]
-- |           }
-- |       ]
-- |   , Footer.footerBottom []
-- |       [ HH.text "© 2024 MyCompany" ]
-- |   ]
-- | ```
module Hydrogen.Layout.Footer
  ( -- * Footer Components
    footer
  , footerColumns
  , footerColumn
  , footerBottom
  , footerLink
  , footerSocial
  , footerNewsletter
    -- * Column Types
  , FooterColumnConfig
  , FooterLinkConfig
    -- * Props
  , FooterProps
  , FooterProp
  , defaultProps
    -- * Prop Builders
  , variant
  , maxWidth
  , bordered
  , className
    -- * Variants
  , FooterVariant(..)
  ) where

import Prelude

import Data.Array (foldl)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Footer variants
data FooterVariant
  = Default
  | Minimal
  | Centered
  | Dark

derive instance eqFooterVariant :: Eq FooterVariant

-- | Get variant classes
variantClasses :: FooterVariant -> String
variantClasses = case _ of
  Default -> "bg-background border-t"
  Minimal -> "bg-background"
  Centered -> "bg-background border-t text-center"
  Dark -> "bg-foreground text-background"

-- | Link configuration
type FooterLinkConfig =
  { label :: String
  , href :: String
  }

-- | Column configuration
type FooterColumnConfig =
  { title :: String
  , links :: Array FooterLinkConfig
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Footer properties
type FooterProps =
  { variant :: FooterVariant
  , maxWidth :: String
  , bordered :: Boolean
  , className :: String
  }

-- | Property modifier
type FooterProp = FooterProps -> FooterProps

-- | Default properties
defaultProps :: FooterProps
defaultProps =
  { variant: Default
  , maxWidth: "max-w-7xl"
  , bordered: true
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set variant
variant :: FooterVariant -> FooterProp
variant v props = props { variant = v }

-- | Set max width
maxWidth :: String -> FooterProp
maxWidth m props = props { maxWidth = m }

-- | Show border
bordered :: Boolean -> FooterProp
bordered b props = props { bordered = b }

-- | Add custom class
className :: String -> FooterProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Container classes
containerClasses :: String
containerClasses =
  "w-full"

-- | Inner wrapper classes
wrapperClasses :: String
wrapperClasses =
  "mx-auto px-4 sm:px-6 lg:px-8 py-12"

-- | Columns grid classes
columnsClasses :: String
columnsClasses =
  "grid grid-cols-2 gap-8 md:grid-cols-4 lg:grid-cols-5"

-- | Column classes
columnClasses :: String
columnClasses =
  "space-y-4"

-- | Column title classes
columnTitleClasses :: String
columnTitleClasses =
  "text-sm font-semibold text-foreground uppercase tracking-wider"

-- | Column links container classes
columnLinksClasses :: String
columnLinksClasses =
  "space-y-3"

-- | Link classes
linkClasses :: String
linkClasses =
  "block text-sm text-muted-foreground hover:text-foreground transition-colors"

-- | Bottom bar classes
bottomClasses :: String
bottomClasses =
  "border-t py-6"

-- | Bottom content classes
bottomContentClasses :: String
bottomContentClasses =
  "flex flex-col items-center justify-between gap-4 md:flex-row"

-- | Social links container classes
socialClasses :: String
socialClasses =
  "flex space-x-6"

-- | Social icon classes
socialIconClasses :: String
socialIconClasses =
  "text-muted-foreground hover:text-foreground transition-colors"

-- | Newsletter form classes
newsletterClasses :: String
newsletterClasses =
  "flex flex-col sm:flex-row gap-2"

-- | Newsletter input classes
newsletterInputClasses :: String
newsletterInputClasses =
  "flex h-10 rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2"

-- | Newsletter button classes
newsletterButtonClasses :: String
newsletterButtonClasses =
  "inline-flex items-center justify-center rounded-md text-sm font-medium h-10 px-4 bg-primary text-primary-foreground hover:bg-primary/90"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a footer link
footerLink :: forall w i. FooterLinkConfig -> HH.HTML w i
footerLink config =
  HH.a
    [ cls [ linkClasses ]
    , HP.href config.href
    ]
    [ HH.text config.label ]

-- | Create a footer column
footerColumn :: forall w i. FooterColumnConfig -> HH.HTML w i
footerColumn config =
  HH.div
    [ cls [ columnClasses ] ]
    [ HH.h3
        [ cls [ columnTitleClasses ] ]
        [ HH.text config.title ]
    , HH.div
        [ cls [ columnLinksClasses ] ]
        (map footerLink config.links)
    ]

-- | Footer columns container
footerColumns :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
footerColumns customClass children =
  HH.div
    [ cls [ columnsClasses, customClass ] ]
    children

-- | Footer bottom bar
footerBottom :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
footerBottom customClass children =
  HH.div
    [ cls [ bottomClasses, customClass ] ]
    [ HH.div
        [ cls [ bottomContentClasses ] ]
        children
    ]

-- | Social links section
footerSocial :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
footerSocial icons =
  HH.div
    [ cls [ socialClasses ] ]
    icons

-- | Newsletter signup form
footerNewsletter :: forall w i. 
  { placeholder :: String, buttonLabel :: String } -> 
  HH.HTML w i
footerNewsletter config =
  HH.form
    [ cls [ newsletterClasses ] ]
    [ HH.input
        [ cls [ newsletterInputClasses ]
        , HP.type_ HP.InputEmail
        , HP.placeholder config.placeholder
        , ARIA.label "Email address"
        ]
    , HH.button
        [ cls [ newsletterButtonClasses ]
        , HP.type_ HP.ButtonSubmit
        ]
        [ HH.text config.buttonLabel ]
    ]

-- | Full footer component
footer :: forall w i. Array FooterProp -> Array (HH.HTML w i) -> HH.HTML w i
footer propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    containerCls = 
      containerClasses 
      <> " " <> variantClasses props.variant
      <> " " <> props.className
  in
    HH.footer
      [ cls [ containerCls ]
      , ARIA.label "Footer"
      ]
      [ HH.div
          [ cls [ wrapperClasses, props.maxWidth ] ]
          children
      ]
