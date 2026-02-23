-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // render // example
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Example: Using Hydrogen's Pure Rendering Abstraction
-- |
-- | This module demonstrates the new pure rendering pattern where UI is
-- | defined as data (`Hydrogen.Render.Element`) and then compiled to
-- | different targets (Halogen, Static HTML, etc.).
-- |
-- | ## The Pattern
-- |
-- | ```
-- | Hydrogen.Render.Element msg
-- |         │
-- |         ├──► Hydrogen.Target.Halogen ──► Reactive Halogen HTML
-- |         │
-- |         └──► Hydrogen.Target.Static  ──► Static HTML String
-- | ```
-- |
-- | ## Benefits
-- |
-- | 1. **Single Source of Truth** — Define UI once, render anywhere
-- | 2. **Pure Data** — Elements are pure PureScript values
-- | 3. **Testable** — UI structure can be tested without DOM
-- | 4. **Target Flexibility** — Add Canvas, WebGL, Native targets later
-- |
-- | ## Usage in Halogen Components
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element as E
-- | import Hydrogen.Target.Halogen as TH
-- |
-- | -- Define UI as pure Element
-- | counterView :: Int -> E.Element Action
-- | counterView count = E.div_
-- |   [ E.class_ "counter" ]
-- |   [ E.span_ [] [ E.text (show count) ]
-- |   , E.button_ [ E.onClick Increment ] [ E.text "+" ]
-- |   , E.button_ [ E.onClick Decrement ] [ E.text "-" ]
-- |   ]
-- |
-- | -- Convert to Halogen HTML in render function
-- | render :: State -> H.ComponentHTML Action Slots m
-- | render state = TH.toHalogen (counterView state.count)
-- | ```
module Hydrogen.Render.Example
  ( -- * Counter Example
    CounterAction(..)
  , counterElement
  , counterElementStatic
  
  -- * Form Example  
  , FormAction(..)
  , loginFormElement
  
  -- * Card Example
  , cardElement
  , userCardElement
  
  -- * Demonstrating Both Targets
  , renderCounterToHalogen
  , renderCounterToStatic
  ) where

import Prelude
  ( show
  , (<>)
  )

import Halogen.HTML.Core as Core
import Hydrogen.Render.Element as E
import Hydrogen.Target.Halogen as TH
import Hydrogen.Target.Static as TS

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // counter example
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Actions for the counter component
data CounterAction
  = Increment
  | Decrement
  | Reset

-- | Counter UI as a pure Element
-- |
-- | This is pure data describing the UI. It can be rendered to any target.
counterElement :: Int -> E.Element CounterAction
counterElement count =
  E.div_
    [ E.class_ "counter flex items-center gap-4 p-4 rounded-lg bg-gray-100" ]
    [ E.button_
        [ E.onClick Decrement
        , E.class_ "px-4 py-2 bg-red-500 text-white rounded hover:bg-red-600"
        ]
        [ E.text "-" ]
    , E.span_
        [ E.class_ "text-2xl font-bold min-w-16 text-center" ]
        [ E.text (show count) ]
    , E.button_
        [ E.onClick Increment
        , E.class_ "px-4 py-2 bg-green-500 text-white rounded hover:bg-green-600"
        ]
        [ E.text "+" ]
    , E.button_
        [ E.onClick Reset
        , E.class_ "px-4 py-2 bg-gray-500 text-white rounded hover:bg-gray-600"
        ]
        [ E.text "Reset" ]
    ]

-- | Static version of counter (no event handlers)
-- |
-- | For static rendering, event handlers are ignored. This version
-- | explicitly omits them for clarity.
counterElementStatic :: forall msg. Int -> E.Element msg
counterElementStatic count =
  E.div_
    [ E.class_ "counter flex items-center gap-4 p-4 rounded-lg bg-gray-100" ]
    [ E.button_
        [ E.class_ "px-4 py-2 bg-red-500 text-white rounded" ]
        [ E.text "-" ]
    , E.span_
        [ E.class_ "text-2xl font-bold min-w-16 text-center" ]
        [ E.text (show count) ]
    , E.button_
        [ E.class_ "px-4 py-2 bg-green-500 text-white rounded" ]
        [ E.text "+" ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // form example
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Actions for the login form
data FormAction
  = UpdateEmail String
  | UpdatePassword String
  | Submit

-- | Login form as a pure Element
-- |
-- | Demonstrates input handling and form submission.
loginFormElement :: String -> String -> E.Element FormAction
loginFormElement email password =
  E.form_
    [ E.class_ "space-y-4 max-w-md mx-auto p-6 bg-white rounded-lg shadow"
    , E.onSubmit Submit
    ]
    [ E.div_
        [ E.class_ "space-y-2" ]
        [ E.label_
            [ E.attr "for" "email"
            , E.class_ "block text-sm font-medium text-gray-700"
            ]
            [ E.text "Email" ]
        , E.input_
            [ E.id_ "email"
            , E.attr "type" "email"
            , E.attr "placeholder" "you@example.com"
            , E.prop "value" email
            , E.onInput UpdateEmail
            , E.class_ "w-full px-3 py-2 border rounded-md focus:ring-2 focus:ring-blue-500"
            ]
        ]
    , E.div_
        [ E.class_ "space-y-2" ]
        [ E.label_
            [ E.attr "for" "password"
            , E.class_ "block text-sm font-medium text-gray-700"
            ]
            [ E.text "Password" ]
        , E.input_
            [ E.id_ "password"
            , E.attr "type" "password"
            , E.attr "placeholder" "••••••••"
            , E.prop "value" password
            , E.onInput UpdatePassword
            , E.class_ "w-full px-3 py-2 border rounded-md focus:ring-2 focus:ring-blue-500"
            ]
        ]
    , E.button_
        [ E.attr "type" "submit"
        , E.class_ "w-full py-2 px-4 bg-blue-600 text-white rounded-md hover:bg-blue-700"
        ]
        [ E.text "Sign In" ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // card example
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generic card wrapper as a pure Element
-- |
-- | Demonstrates polymorphic elements that can wrap any content.
cardElement :: forall msg. String -> Array (E.Element msg) -> E.Element msg
cardElement title children =
  E.div_
    [ E.class_ "rounded-lg border bg-card text-card-foreground shadow-sm" ]
    [ E.div_
        [ E.class_ "flex flex-col space-y-1.5 p-6" ]
        [ E.h3_
            [ E.class_ "text-2xl font-semibold leading-none tracking-tight" ]
            [ E.text title ]
        ]
    , E.div_
        [ E.class_ "p-6 pt-0" ]
        children
    ]

-- | User profile card
-- |
-- | Demonstrates composition of pure Elements.
userCardElement :: forall msg. String -> String -> String -> E.Element msg
userCardElement name email avatarUrl =
  cardElement name
    [ E.div_
        [ E.class_ "flex items-center gap-4" ]
        [ E.img_
            [ E.attr "src" avatarUrl
            , E.attr "alt" (name <> "'s avatar")
            , E.class_ "w-16 h-16 rounded-full"
            ]
        , E.div_
            []
            [ E.p_
                [ E.class_ "text-lg font-medium" ]
                [ E.text name ]
            , E.p_
                [ E.class_ "text-sm text-muted-foreground" ]
                [ E.text email ]
            ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // target // examples
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render counter to Halogen HTML (for use in Halogen components)
-- |
-- | ```purescript
-- | render :: State -> H.ComponentHTML Action Slots m
-- | render state = renderCounterToHalogen state.count
-- | ```
renderCounterToHalogen :: forall w. Int -> Core.HTML w CounterAction
renderCounterToHalogen count = TH.toHalogen (counterElement count)

-- | Render counter to static HTML string (for SSG)
-- |
-- | ```purescript
-- | generateStaticPage :: Int -> String
-- | generateStaticPage count = renderCounterToStatic count
-- | -- => "<div class=\"counter...\">...</div>"
-- | ```
renderCounterToStatic :: Int -> String
renderCounterToStatic count = TS.render (counterElementStatic count)
