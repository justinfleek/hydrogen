module Test.Main where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String
import Effect (Effect)
import Effect.Aff (launchAff_)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.HTML.Renderer (render, renderWith, defaultOptions)
import Hydrogen.HTML.Renderer as Renderer
import Hydrogen.Data.Format as Format
import Hydrogen.Router (normalizeTrailingSlash)
import Hydrogen.SSG as SSG
import Hydrogen.UI.Core as UI
import Hydrogen.UI.Error as Error
import Hydrogen.UI.Loading as Loading
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter] do
  describe "Hydrogen Framework" do
    formatTests
    routerTests
    uiCoreTests
    uiLoadingTests
    uiErrorTests
    ssgTests
    rendererTests

-- =============================================================================
--                                                              // format tests
-- =============================================================================

formatTests :: Spec Unit
formatTests = describe "Data.Format" do
  describe "formatBytes" do
    it "formats bytes" do
      Format.formatBytes 500.0 `shouldEqual` "500 B"
    
    it "formats kilobytes" do
      Format.formatBytes 1024.0 `shouldEqual` "1.0 KB"
    
    it "formats megabytes" do
      Format.formatBytes (1.5 * Format.mb) `shouldEqual` "1.5 MB"
    
    it "formats gigabytes" do
      Format.formatBytes (2.5 * Format.gb) `shouldEqual` "2.5 GB"
    
    it "handles negative numbers" do
      Format.formatBytes (-1024.0) `shouldEqual` "-1.0 KB"

  describe "formatBytesCompact" do
    it "formats without spaces" do
      Format.formatBytesCompact (1.5 * Format.gb) `shouldEqual` "1.5GB"

  describe "formatNum" do
    it "formats with one decimal" do
      Format.formatNum 3.14159 `shouldEqual` "3.1"

  describe "formatNumCompact" do
    it "formats thousands" do
      Format.formatNumCompact 1500.0 `shouldEqual` "1.5k"
    
    it "formats millions" do
      Format.formatNumCompact 2500000.0 `shouldEqual` "2.5M"
    
    it "keeps small numbers as-is" do
      Format.formatNumCompact 500.0 `shouldEqual` "500"

  describe "formatPercent" do
    it "formats percentages" do
      Format.formatPercent 0.874 `shouldEqual` "87.4%"

  describe "formatCount" do
    it "formats count" do
      Format.formatCount 45230 `shouldEqual` "45.2k"

  describe "formatDuration" do
    it "formats seconds" do
      Format.formatDuration 45 `shouldEqual` "45s"
    
    it "formats minutes and seconds" do
      Format.formatDuration 125 `shouldEqual` "2m 5s"
    
    it "formats hours" do
      Format.formatDuration 3661 `shouldEqual` "1h 1m 1s"
    
    it "handles zero" do
      Format.formatDuration 0 `shouldEqual` "-"

  describe "formatDurationCompact" do
    it "shows largest unit only" do
      Format.formatDurationCompact 3661 `shouldEqual` "1h"

  describe "percentage" do
    it "calculates percentage" do
      Format.percentage 750.0 1000.0 `shouldEqual` 75
    
    it "handles division by zero" do
      Format.percentage 1.0 0.0 `shouldEqual` 0

  describe "rate" do
    it "calculates rate" do
      Format.rate 90 100 `shouldEqual` 0.9
    
    it "handles zero total" do
      Format.rate 1 0 `shouldEqual` 0.0

  describe "ratio" do
    it "calculates ratio" do
      Format.ratio 3.0 4.0 `shouldEqual` 0.75
    
    it "handles zero denominator" do
      Format.ratio 1.0 0.0 `shouldEqual` 0.0

-- =============================================================================
--                                                              // router tests
-- =============================================================================

routerTests :: Spec Unit
routerTests = describe "Router" do
  describe "normalizeTrailingSlash" do
    it "preserves root path" do
      normalizeTrailingSlash "/" `shouldEqual` "/"
    
    it "removes trailing slash" do
      normalizeTrailingSlash "/about/" `shouldEqual` "/about"
    
    it "keeps path without trailing slash" do
      normalizeTrailingSlash "/about" `shouldEqual` "/about"
    
    it "handles nested paths" do
      normalizeTrailingSlash "/docs/api/" `shouldEqual` "/docs/api"

-- =============================================================================
--                                                             // ui core tests
-- =============================================================================

uiCoreTests :: Spec Unit
uiCoreTests = describe "UI.Core" do
  describe "classes" do
    it "combines class names" do
      UI.classes ["foo", "bar", "baz"] `shouldEqual` "foo bar baz"
    
    it "filters empty strings" do
      UI.classes ["foo", "", "bar"] `shouldEqual` "foo bar"
    
    it "handles empty array" do
      UI.classes [] `shouldEqual` ""

  describe "box" do
    it "renders div with class" do
      let html = UI.box "my-class" [ HH.text "content" ]
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "my-class")
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "content")

  describe "row" do
    it "renders flex row" do
      let html = UI.row "gap-4" [ HH.text "item" ]
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "flex")
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "flex-row")

  describe "column" do
    it "renders flex column" do
      let html = UI.column "gap-2" [ HH.text "item" ]
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "flex")
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "flex-col")

-- =============================================================================
--                                                          // ui loading tests
-- =============================================================================

uiLoadingTests :: Spec Unit
uiLoadingTests = describe "UI.Loading" do
  describe "spinner" do
    it "renders with animate-spin" do
      let html = Loading.spinner "w-8 h-8"
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "animate-spin")
    
    it "applies size class" do
      let html = Loading.spinner "w-8 h-8"
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "w-8 h-8")

  describe "loadingState" do
    it "includes message" do
      let html = Loading.loadingState "Loading data..."
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "Loading data...")
    
    it "includes spinner" do
      let html = Loading.loadingState "test"
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "animate-spin")

  describe "loadingCard" do
    it "renders with animate-pulse" do
      Renderer.render Loading.loadingCard `shouldSatisfy` String.contains (String.Pattern "animate-pulse")

  describe "skeletonText" do
    it "applies width class" do
      let html = Loading.skeletonText "w-32"
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "w-32")

-- =============================================================================
--                                                            // ui error tests
-- =============================================================================

uiErrorTests :: Spec Unit
uiErrorTests = describe "UI.Error" do
  describe "errorState" do
    it "shows message" do
      let html = Error.errorState "Something went wrong"
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "Something went wrong")
    
    it "shows failed to load text" do
      let html = Error.errorState "test"
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "Failed to load")

  describe "errorCard" do
    it "shows message" do
      let html = Error.errorCard "Network error"
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "Network error")
    
    it "has error styling" do
      let html = Error.errorCard "test"
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "destructive")

  describe "errorBadge" do
    it "shows error label" do
      let html = Error.errorBadge "Invalid input"
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "Error:")
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "Invalid input")

  describe "emptyState" do
    it "shows title and description" do
      let html = Error.emptyState "No items" "Add your first item"
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "No items")
      Renderer.render html `shouldSatisfy` String.contains (String.Pattern "Add your first item")

-- =============================================================================
--                                                                 // ssg tests
-- =============================================================================

ssgTests :: Spec Unit
ssgTests = describe "SSG" do
  describe "renderPage" do
    it "includes DOCTYPE" do
      let page = SSG.renderPage SSG.defaultDocConfig testMeta (HH.div_ [])
      page `shouldSatisfy` String.contains (String.Pattern "<!DOCTYPE html>")
    
    it "includes title" do
      let page = SSG.renderPage SSG.defaultDocConfig testMeta (HH.div_ [])
      page `shouldSatisfy` String.contains (String.Pattern "<title>Test Page</title>")
    
    it "includes meta description" do
      let page = SSG.renderPage SSG.defaultDocConfig testMeta (HH.div_ [])
      page `shouldSatisfy` String.contains (String.Pattern "Test description")

  describe "ogTags" do
    it "includes og:title" do
      let tags = SSG.ogTags SSG.defaultDocConfig testMeta
      let rendered = Renderer.render (HH.div_ tags)
      rendered `shouldSatisfy` String.contains (String.Pattern "og:title")
    
    it "includes og:description" do
      let tags = SSG.ogTags SSG.defaultDocConfig testMeta
      let rendered = Renderer.render (HH.div_ tags)
      rendered `shouldSatisfy` String.contains (String.Pattern "og:description")

  describe "twitterTags" do
    it "includes twitter:card" do
      let tags = SSG.twitterTags testMeta
      let rendered = Renderer.render (HH.div_ tags)
      rendered `shouldSatisfy` String.contains (String.Pattern "twitter:card")

testMeta :: SSG.PageMeta
testMeta =
  { title: "Test Page"
  , description: "Test description"
  , path: "/test"
  , ogImage: Nothing
  , canonicalUrl: Nothing
  }

-- =============================================================================
--                                                           // renderer tests
-- =============================================================================

rendererTests :: Spec Unit
rendererTests = describe "HTML.Renderer" do
  describe "basic rendering" do
    it "renders empty div" do
      render (HH.div [] []) `shouldEqual` "<div></div>"

    it "renders text content" do
      render (HH.div [] [ HH.text "Hello" ]) `shouldEqual` "<div>Hello</div>"

    it "renders multiple text nodes" do
      render (HH.div [] [ HH.text "Hello", HH.text " ", HH.text "World" ])
        `shouldEqual` "<div>Hello World</div>"

    it "renders span" do
      render (HH.span [] [ HH.text "test" ]) `shouldEqual` "<span>test</span>"

    it "renders paragraph" do
      render (HH.p [] [ HH.text "paragraph" ]) `shouldEqual` "<p>paragraph</p>"

    it "renders heading" do
      render (HH.h1 [] [ HH.text "Title" ]) `shouldEqual` "<h1>Title</h1>"

    it "renders ul/li" do
      render (HH.ul [] [ HH.li [] [ HH.text "item" ] ])
        `shouldEqual` "<ul><li>item</li></ul>"

  describe "attributes" do
    it "renders id attribute" do
      render (HH.div [ HP.id "my-id" ] []) `shouldEqual` "<div id=\"my-id\"></div>"

    it "renders title attribute" do
      render (HH.div [ HP.title "tooltip" ] [])
        `shouldEqual` "<div title=\"tooltip\"></div>"

    it "renders href on anchor" do
      render (HH.a [ HP.href "/path" ] [ HH.text "link" ])
        `shouldEqual` "<a href=\"/path\">link</a>"

    it "renders src on img" do
      render (HH.img [ HP.src "/image.png" ])
        `shouldEqual` "<img src=\"/image.png\"/>"

    it "renders multiple attributes" do
      render (HH.div [ HP.id "foo", HP.title "bar" ] [])
        `shouldEqual` "<div id=\"foo\" title=\"bar\"></div>"

    it "renders data attributes" do
      render (HH.div [ HP.attr (HH.AttrName "data-testid") "test" ] [])
        `shouldEqual` "<div data-testid=\"test\"></div>"

  describe "properties" do
    it "renders className as class" do
      render (HH.div [ HP.class_ (HH.ClassName "container") ] [])
        `shouldEqual` "<div class=\"container\"></div>"

    it "renders multiple classes" do
      render (HH.div [ HP.classes [ HH.ClassName "foo", HH.ClassName "bar" ] ] [])
        `shouldEqual` "<div class=\"foo bar\"></div>"

    it "renders disabled as boolean attribute" do
      render (HH.button [ HP.disabled true ] [ HH.text "click" ])
        `shouldEqual` "<button disabled>click</button>"

    it "omits disabled when false" do
      render (HH.button [ HP.disabled false ] [ HH.text "click" ])
        `shouldEqual` "<button>click</button>"

    it "renders checked attribute" do
      render (HH.input [ HP.type_ HP.InputCheckbox, HP.checked true ])
        `shouldEqual` "<input type=\"checkbox\" checked/>"

    it "renders placeholder" do
      render (HH.input [ HP.placeholder "Enter text" ])
        `shouldEqual` "<input placeholder=\"Enter text\"/>"

  describe "escaping" do
    it "escapes < in text" do
      render (HH.div [] [ HH.text "a < b" ]) `shouldEqual` "<div>a &lt; b</div>"

    it "escapes > in text" do
      render (HH.div [] [ HH.text "a > b" ]) `shouldEqual` "<div>a &gt; b</div>"

    it "escapes & in text" do
      render (HH.div [] [ HH.text "a & b" ]) `shouldEqual` "<div>a &amp; b</div>"

    it "escapes quotes in attributes" do
      render (HH.div [ HP.title "say \"hello\"" ] [])
        `shouldEqual` "<div title=\"say &quot;hello&quot;\"></div>"

  describe "self-closing" do
    it "renders br as self-closing" do
      render (HH.br []) `shouldEqual` "<br/>"

    it "renders hr as self-closing" do
      render (HH.hr []) `shouldEqual` "<hr/>"

    it "renders img as self-closing" do
      render (HH.img [ HP.src "x.png" ]) `shouldEqual` "<img src=\"x.png\"/>"

    it "renders input as self-closing" do
      render (HH.input []) `shouldEqual` "<input/>"

    it "renders non-self-closing without self-close" do
      renderWith (defaultOptions { selfClosingTags = false }) (HH.br [])
        `shouldEqual` "<br></br>"

  describe "nesting" do
    it "renders nested elements" do
      render (HH.div [] [ HH.span [] [ HH.text "inner" ] ])
        `shouldEqual` "<div><span>inner</span></div>"

    it "renders deeply nested elements" do
      render (HH.div [] [ HH.div [] [ HH.div [] [ HH.text "deep" ] ] ])
        `shouldEqual` "<div><div><div>deep</div></div></div>"

    it "renders siblings" do
      render (HH.div [] [ HH.span [] [], HH.span [] [] ])
        `shouldEqual` "<div><span></span><span></span></div>"

    it "renders complex structure" do
      render (HH.article [ HP.class_ (HH.ClassName "post") ]
        [ HH.h1 [] [ HH.text "Title" ]
        , HH.p [] [ HH.text "Content with ", HH.strong [] [ HH.text "bold" ], HH.text " text." ]
        ])
        `shouldEqual` "<article class=\"post\"><h1>Title</h1><p>Content with <strong>bold</strong> text.</p></article>"
