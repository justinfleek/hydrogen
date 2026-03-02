-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // ssg // pure
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Static Site Generation — Zero unsafeCoerce
-- |
-- | This module provides SSG functionality using Hydrogen's pure Element type
-- | instead of Halogen's HTML type. The entire rendering pipeline is safe.
-- |
-- | ══════════════════════════════════════════════════════════════════════════
-- | COMPARISON WITH Hydrogen.SSG
-- | ══════════════════════════════════════════════════════════════════════════
-- |
-- | Hydrogen.SSG (Halogen path):
-- |   - Uses HH.HTML type from Halogen
-- |   - Renders via HTML.Renderer (contains unsafeCoerce at Halogen boundary)
-- |   - Compatible with existing Halogen components
-- |
-- | Hydrogen.SSG.Pure (this module):
-- |   - Uses Element type from Hydrogen.Render.Element
-- |   - Renders via Target.Static (zero unsafeCoerce)
-- |   - Pure data all the way down
-- |
-- | ══════════════════════════════════════════════════════════════════════════
-- |
-- | Usage:
-- | ```purescript
-- | import Hydrogen.SSG.Pure as SSG
-- | import Hydrogen.Render.Element as E
-- |
-- | myPage :: forall msg. Element msg
-- | myPage = E.div_ [ E.class_ "container" ] [ E.text "Hello" ]
-- |
-- | html :: String
-- | html = SSG.renderPage defaultDocConfig defaultPageMeta myPage
-- | ```
module Hydrogen.SSG.Pure
  ( -- * Document configuration
    DocConfig
  , defaultDocConfig
  
  -- * Page metadata  
  , PageMeta
  , defaultPageMeta
  
  -- * Rendering
  , renderPage
  , renderDocument
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , (<>)
  )

import Data.Array (concat)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element
  ( Element
  )

import Hydrogen.Render.Element.Attributes
  ( attr
  , href
  , src
  )

import Hydrogen.Render.Element.HTML
  ( body_
  , head_
  , html_
  , link_
  , meta_
  , script_
  , title_
  )

import Hydrogen.Render.Element.Constructors (text)

import Hydrogen.Target.Static as Static

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // document // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for the HTML document
type DocConfig =
  { lang :: String
  , charsetValue :: String
  , viewport :: String
  , siteName :: String
  , themeColor :: Maybe String
  , manifest :: Maybe String
  , favicon :: Maybe String
  , stylesheets :: Array String
  , scripts :: Array String
  }

-- | Default document configuration
defaultDocConfig :: DocConfig
defaultDocConfig =
  { lang: "en"
  , charsetValue: "utf-8"
  , viewport: "width=device-width, initial-scale=1"
  , siteName: ""
  , themeColor: Nothing
  , favicon: Nothing
  , manifest: Nothing
  , stylesheets: []
  , scripts: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // page // metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metadata for a single page
type PageMeta =
  { title :: String
  , description :: String
  , path :: String
  , ogImage :: Maybe String
  , canonicalUrl :: Maybe String
  }

-- | Default page metadata
defaultPageMeta :: PageMeta
defaultPageMeta =
  { title: ""
  , description: ""
  , path: "/"
  , ogImage: Nothing
  , canonicalUrl: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a complete HTML page with DOCTYPE
renderPage :: forall msg. DocConfig -> PageMeta -> Element msg -> String
renderPage config pageMeta bodyContent =
  let doc = renderDocument config pageMeta bodyContent
  in "<!DOCTYPE html>" <> Static.render doc

-- | Render the HTML document element (without DOCTYPE)
renderDocument :: forall msg. DocConfig -> PageMeta -> Element msg -> Element msg
renderDocument config pageMeta bodyContent =
  html_ [ attr "lang" config.lang ]
    [ head_ [] (headElements config pageMeta)
    , body_ [] ([ bodyContent ] <> scriptElements config)
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // head // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build all head elements from config and page meta
headElements :: forall msg. DocConfig -> PageMeta -> Array (Element msg)
headElements config pageMeta = concat
  [ coreMetaElements config pageMeta
  , ogElements config pageMeta
  , twitterElements pageMeta
  , linkElements config pageMeta
  ]

-- | Core meta elements (charset, viewport, title, description)
coreMetaElements :: forall msg. DocConfig -> PageMeta -> Array (Element msg)
coreMetaElements config pageMeta =
  [ meta_ [ attr "charset" config.charsetValue ]
  , meta_ [ attr "name" "viewport", attr "content" config.viewport ]
  , title_ [ text pageMeta.title ]
  , meta_ [ attr "name" "description", attr "content" pageMeta.description ]
  ]

-- | OpenGraph meta elements
ogElements :: forall msg. DocConfig -> PageMeta -> Array (Element msg)
ogElements config pageMeta = concat
  [ [ ogMeta "og:type" "website"
    , ogMeta "og:title" pageMeta.title
    , ogMeta "og:description" pageMeta.description
    , ogMeta "og:url" pageMeta.path
    ]
  , siteNameMeta config
  , ogImageMeta pageMeta
  ]

-- | Twitter Card meta elements
twitterElements :: forall msg. PageMeta -> Array (Element msg)
twitterElements pageMeta = concat
  [ [ twitterMeta "twitter:card" "summary_large_image"
    , twitterMeta "twitter:title" pageMeta.title
    , twitterMeta "twitter:description" pageMeta.description
    ]
  , twitterImageMeta pageMeta
  ]

-- | Link elements (stylesheets, favicon, manifest, canonical)
linkElements :: forall msg. DocConfig -> PageMeta -> Array (Element msg)
linkElements config pageMeta = concat
  [ stylesheetLinks config
  , faviconLink config
  , manifestLink config
  , canonicalLink pageMeta
  , themeColorMeta config
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an OpenGraph meta element
ogMeta :: forall msg. String -> String -> Element msg
ogMeta prop val = meta_ [ attr "property" prop, attr "content" val ]

-- | Create a Twitter meta element  
twitterMeta :: forall msg. String -> String -> Element msg
twitterMeta nameVal val = meta_ [ attr "name" nameVal, attr "content" val ]

-- | Site name OG meta (if configured)
siteNameMeta :: forall msg. DocConfig -> Array (Element msg)
siteNameMeta config = case config.siteName of
  "" -> []
  siteName -> [ ogMeta "og:site_name" siteName ]

-- | OG image meta (if provided)
ogImageMeta :: forall msg. PageMeta -> Array (Element msg)
ogImageMeta pageMeta = case pageMeta.ogImage of
  Nothing -> []
  Just url -> [ ogMeta "og:image" url ]

-- | Twitter image meta (if provided)
twitterImageMeta :: forall msg. PageMeta -> Array (Element msg)
twitterImageMeta pageMeta = case pageMeta.ogImage of
  Nothing -> []
  Just url -> [ twitterMeta "twitter:image" url ]

-- | Stylesheet link elements
stylesheetLinks :: forall msg. DocConfig -> Array (Element msg)
stylesheetLinks config = map makeLink config.stylesheets
  where
  makeLink :: String -> Element msg
  makeLink url = link_ [ attr "rel" "stylesheet", href url ]

-- | Script elements (loaded at end of body)
scriptElements :: forall msg. DocConfig -> Array (Element msg)
scriptElements config = map makeScript config.scripts
  where
  makeScript :: String -> Element msg
  makeScript url = script_ [ src url ] []

-- | Favicon link (if configured)
faviconLink :: forall msg. DocConfig -> Array (Element msg)
faviconLink config = case config.favicon of
  Nothing -> []
  Just url -> [ link_ [ attr "rel" "icon", href url ] ]

-- | Manifest link (if configured)
manifestLink :: forall msg. DocConfig -> Array (Element msg)
manifestLink config = case config.manifest of
  Nothing -> []
  Just url -> [ link_ [ attr "rel" "manifest", href url ] ]

-- | Canonical URL link (if provided)
canonicalLink :: forall msg. PageMeta -> Array (Element msg)
canonicalLink pageMeta = case pageMeta.canonicalUrl of
  Nothing -> []
  Just url -> [ link_ [ attr "rel" "canonical", href url ] ]

-- | Theme color meta (if configured)
themeColorMeta :: forall msg. DocConfig -> Array (Element msg)
themeColorMeta config = case config.themeColor of
  Nothing -> []
  Just color -> [ meta_ [ attr "name" "theme-color", attr "content" color ] ]
