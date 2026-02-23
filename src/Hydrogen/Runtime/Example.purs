-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // runtime // example
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Example: Pure Hydrogen Application without Framework
-- |
-- | This module demonstrates a complete Hydrogen application using only
-- | the pure runtime — no Halogen, no React, no framework.
-- |
-- | ## The Architecture
-- |
-- | ```purescript
-- | type App state msg =
-- |   { init :: state
-- |   , update :: msg -> state -> state
-- |   , view :: state -> Element msg
-- |   }
-- | ```
-- |
-- | Three pure functions. The runtime handles DOM rendering and reconciliation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Runtime.App as App
-- | import Hydrogen.Runtime.Example as Ex
-- |
-- | main :: Effect Unit
-- | main = do
-- |   _ <- App.mount "#app" Ex.counterApp
-- |   pure unit
-- | ```
-- |
-- | ## HTML
-- |
-- | ```html
-- | <!DOCTYPE html>
-- | <html>
-- | <head>
-- |   <script type="module" src="./output/Main/index.js"></script>
-- | </head>
-- | <body>
-- |   <div id="app"></div>
-- | </body>
-- | </html>
-- | ```
module Hydrogen.Runtime.Example
  ( -- * Counter Application (simple, no effects)
    CounterState
  , CounterMsg(..)
  , counterApp
  
  -- * Todo Application (simple, no effects)
  , TodoItem
  , TodoState
  , TodoMsg(..)
  , todoApp
  
  -- * Timer Application (with commands)
  , TimerState
  , TimerMsg(..)
  , timerApp
  
  -- * Spring Animation Application
  , SpringDemoState
  , SpringDemoMsg(..)
  , springDemoApp
  
  -- * HTTP Fetch Application
  , FetchState
  , FetchResult(..)
  , FetchMsg(..)
  , fetchApp
  ) where

import Prelude
  ( map
  , negate
  , otherwise
  , show
  , (<>)
  , (<)
  , (>)
  , (==)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (filter, length, snoc)
import Data.Maybe (Maybe(Nothing))
import Data.Tuple (Tuple)
import Foreign (Foreign)
import Hydrogen.Motion.Spring (springWobbly)
import Hydrogen.Render.Element as E
import Hydrogen.Runtime.Animate as Anim
import Hydrogen.Runtime.App (App, AppCmd)
import Hydrogen.Runtime.Cmd 
  ( HttpError(..)
  , HttpErrorContext
  , HttpMethod(GET)
  , HttpResult(..)
  , HttpSuccess
  , Transition
  , animationFrame
  , delay
  , http
  , noCmd
  , transition
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // counter example
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Counter state — just an integer
type CounterState = { count :: Int }

-- | Counter messages
data CounterMsg
  = Increment
  | Decrement
  | Reset
  | Add Int

-- | Counter application
-- |
-- | The simplest possible Hydrogen app demonstrating:
-- | - Pure state type
-- | - Pure update function
-- | - Pure view function
-- | - Event handling
counterApp :: App CounterState CounterMsg
counterApp =
  { init: { count: 0 }
  , update: counterUpdate
  , view: counterView
  }

-- | Pure state transition
counterUpdate :: CounterMsg -> CounterState -> CounterState
counterUpdate msg state = case msg of
  Increment -> state { count = state.count + 1 }
  Decrement -> state { count = state.count - 1 }
  Reset -> state { count = 0 }
  Add n -> state { count = state.count + n }

-- | Pure view function
counterView :: CounterState -> E.Element CounterMsg
counterView state =
  E.div_
    [ E.class_ "counter-app p-8" ]
    [ E.h1_
        [ E.class_ "text-3xl font-bold mb-6" ]
        [ E.text "Hydrogen Counter" ]
    , E.div_
        [ E.class_ "flex items-center gap-4 mb-4" ]
        [ counterButton Decrement "-" "bg-red-500 hover:bg-red-600"
        , E.span_
            [ E.class_ "text-4xl font-mono min-w-24 text-center"
            , E.style "color" (countColor state.count)
            ]
            [ E.text (show state.count) ]
        , counterButton Increment "+" "bg-green-500 hover:bg-green-600"
        ]
    , E.div_
        [ E.class_ "flex gap-2" ]
        [ counterButton Reset "Reset" "bg-gray-500 hover:bg-gray-600"
        , counterButton (Add 10) "+10" "bg-blue-500 hover:bg-blue-600"
        , counterButton (Add (negate 10)) "-10" "bg-purple-500 hover:bg-purple-600"
        ]
    ]

-- | Button helper
counterButton :: CounterMsg -> String -> String -> E.Element CounterMsg
counterButton msg label colorClass =
  E.button_
    [ E.onClick msg
    , E.class_ ("px-4 py-2 text-white rounded font-medium " <> colorClass)
    ]
    [ E.text label ]

-- | Color based on count value
countColor :: Int -> String
countColor n
  | n > 0 = "green"
  | n < 0 = "red"
  | otherwise = "black"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // todo example
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Todo item
type TodoItem =
  { id :: Int
  , text :: String
  , completed :: Boolean
  }

-- | Todo state
type TodoState =
  { items :: Array TodoItem
  , nextId :: Int
  , inputText :: String
  }

-- | Todo messages
data TodoMsg
  = AddTodo
  | RemoveTodo Int
  | ToggleTodo Int
  | UpdateInput String
  | ClearCompleted

-- | Todo application
-- |
-- | A more complex example demonstrating:
-- | - List rendering
-- | - Input handling
-- | - Filtering/mapping arrays
todoApp :: App TodoState TodoMsg
todoApp =
  { init:
      { items: []
      , nextId: 1
      , inputText: ""
      }
  , update: todoUpdate
  , view: todoView
  }

-- | Pure state transition
todoUpdate :: TodoMsg -> TodoState -> TodoState
todoUpdate msg state = case msg of
  AddTodo ->
    case state.inputText == "" of
      true -> state
      false -> state
        { items = snoc state.items
            { id: state.nextId
            , text: state.inputText
            , completed: false
            }
        , nextId = state.nextId + 1
        , inputText = ""
        }
  
  RemoveTodo id ->
    state { items = filter (\item -> (item.id == id) == false) state.items }
  
  ToggleTodo id ->
    state { items = toggleItem id state.items }
  
  UpdateInput text ->
    state { inputText = text }
  
  ClearCompleted ->
    state { items = filter (\item -> item.completed == false) state.items }

-- | Toggle completion status of an item
toggleItem :: Int -> Array TodoItem -> Array TodoItem
toggleItem id items =
  map (\item ->
    case item.id == id of
      true -> item { completed = item.completed == false }
      false -> item
  ) items

-- | Pure view function
todoView :: TodoState -> E.Element TodoMsg
todoView state =
  E.div_
    [ E.class_ "todo-app max-w-md mx-auto p-6" ]
    [ E.h1_
        [ E.class_ "text-2xl font-bold mb-4" ]
        [ E.text "Hydrogen Todo" ]
    , todoInput state.inputText
    , todoList state.items
    , todoFooter state.items
    ]

-- | Input for new todos
todoInput :: String -> E.Element TodoMsg
todoInput currentText =
  E.div_
    [ E.class_ "flex gap-2 mb-4" ]
    [ E.input_
        [ E.type_ "text"
        , E.value currentText
        , E.placeholder "What needs to be done?"
        , E.onInput UpdateInput
        , E.class_ "flex-1 px-3 py-2 border rounded"
        ]
    , E.button_
        [ E.onClick AddTodo
        , E.class_ "px-4 py-2 bg-blue-500 text-white rounded hover:bg-blue-600"
        ]
        [ E.text "Add" ]
    ]

-- | List of todo items
todoList :: Array TodoItem -> E.Element TodoMsg
todoList items =
  E.ul_
    [ E.class_ "space-y-2 mb-4" ]
    (map todoItemView items)

-- | Single todo item view
todoItemView :: TodoItem -> E.Element TodoMsg
todoItemView item =
  E.li_
    [ E.class_ "flex items-center gap-3 p-2 bg-gray-50 rounded" ]
    [ E.input_
        [ E.type_ "checkbox"
        , E.checked item.completed
        , E.onClick (ToggleTodo item.id)
        , E.class_ "w-5 h-5"
        ]
    , E.span_
        [ E.class_ (textClass item.completed) ]
        [ E.text item.text ]
    , E.button_
        [ E.onClick (RemoveTodo item.id)
        , E.class_ "ml-auto text-red-500 hover:text-red-700"
        ]
        [ E.text "×" ]
    ]

-- | Text styling based on completion
textClass :: Boolean -> String
textClass completed = case completed of
  true -> "flex-1 line-through text-gray-400"
  false -> "flex-1"

-- | Footer with count and clear button
todoFooter :: Array TodoItem -> E.Element TodoMsg
todoFooter items =
  E.div_
    [ E.class_ "flex justify-between text-sm text-gray-500" ]
    [ E.span_
        []
        [ E.text (itemsRemaining items) ]
    , E.button_
        [ E.onClick ClearCompleted
        , E.class_ "text-blue-500 hover:underline"
        ]
        [ E.text "Clear completed" ]
    ]

-- | Count of remaining items
itemsRemaining :: Array TodoItem -> String
itemsRemaining items =
  let active = filter (\item -> item.completed == false) items
  in show (length active) <> " items left"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // timer // example // cmd
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Timer state
type TimerState =
  { seconds :: Int
  , running :: Boolean
  }

-- | Timer messages
data TimerMsg
  = StartTimer
  | StopTimer
  | ResetTimer
  | Tick

-- | Timer application with commands
-- |
-- | Demonstrates:
-- | - Command-based effects (delays)
-- | - Self-scheduling tick loop
-- | - State-dependent command generation
timerApp :: AppCmd TimerState TimerMsg
timerApp =
  { init: noCmd { seconds: 0, running: false }
  , update: timerUpdate
  , view: timerView
  }

-- | Timer update with commands
timerUpdate :: TimerMsg -> TimerState -> Transition TimerState TimerMsg
timerUpdate msg state = case msg of
  StartTimer -> 
    case state.running of
      true -> noCmd state  -- Already running
      false -> 
        transition 
          state { running = true }
          (delay 1000.0 Tick)  -- Schedule first tick
  
  StopTimer ->
    noCmd state { running = false }
  
  ResetTimer ->
    noCmd state { seconds = 0, running = false }
  
  Tick ->
    case state.running of
      false -> noCmd state  -- Stopped, don't continue
      true -> 
        transition
          state { seconds = state.seconds + 1 }
          (delay 1000.0 Tick)  -- Schedule next tick

-- | Timer view
timerView :: TimerState -> E.Element TimerMsg
timerView state =
  E.div_
    [ E.class_ "timer-app p-8 text-center" ]
    [ E.h1_
        [ E.class_ "text-3xl font-bold mb-6" ]
        [ E.text "Hydrogen Timer" ]
    , E.div_
        [ E.class_ "text-6xl font-mono mb-8" ]
        [ E.text (formatTime state.seconds) ]
    , E.div_
        [ E.class_ "flex justify-center gap-4" ]
        [ timerButton 
            (case state.running of
              true -> StopTimer
              false -> StartTimer)
            (case state.running of
              true -> "Stop"
              false -> "Start")
            (case state.running of
              true -> "bg-red-500 hover:bg-red-600"
              false -> "bg-green-500 hover:bg-green-600")
        , timerButton ResetTimer "Reset" "bg-gray-500 hover:bg-gray-600"
        ]
    ]

-- | Timer button helper
timerButton :: TimerMsg -> String -> String -> E.Element TimerMsg
timerButton msg label colorClass =
  E.button_
    [ E.onClick msg
    , E.class_ ("px-6 py-3 text-white rounded-lg font-medium " <> colorClass)
    ]
    [ E.text label ]

-- | Format seconds as MM:SS
formatTime :: Int -> String
formatTime totalSeconds =
  let 
    minutes = totalSeconds / 60
    seconds = totalSeconds - (minutes * 60)
  in padZero minutes <> ":" <> padZero seconds

-- | Pad a number with leading zero
padZero :: Int -> String
padZero n = case n < 10 of
  true -> "0" <> show n
  false -> show n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // spring // demo // example
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spring animation demo state
type SpringDemoState =
  { position :: Anim.SpringState
  , targetX :: Number
  }

-- | Spring animation messages
data SpringDemoMsg
  = MoveLeft
  | MoveRight
  | MoveCenter
  | AnimTick Number  -- timestamp

-- | Spring animation demo application
-- |
-- | Demonstrates:
-- | - Physics-based spring animations
-- | - Self-scheduling animation loop via Cmd
-- | - Smooth position interpolation
springDemoApp :: AppCmd SpringDemoState SpringDemoMsg
springDemoApp =
  { init: noCmd
      { position: Anim.springState springWobbly 200.0
      , targetX: 200.0
      }
  , update: springDemoUpdate
  , view: springDemoView
  }

-- | Update with spring physics
springDemoUpdate :: SpringDemoMsg -> SpringDemoState -> Transition SpringDemoState SpringDemoMsg
springDemoUpdate msg state = case msg of
  MoveLeft ->
    let newPos = Anim.springTo state.position 50.0 0.0
    in transition state { position = newPos, targetX = 50.0 } (animationFrame AnimTick)
  
  MoveRight ->
    let newPos = Anim.springTo state.position 350.0 0.0
    in transition state { position = newPos, targetX = 350.0 } (animationFrame AnimTick)
  
  MoveCenter ->
    let newPos = Anim.springTo state.position 200.0 0.0
    in transition state { position = newPos, targetX = 200.0 } (animationFrame AnimTick)
  
  AnimTick timestamp ->
    let newPos = Anim.tickSpring timestamp state.position
    in case Anim.springComplete newPos of
      true -> noCmd state { position = newPos }
      false -> transition state { position = newPos } (animationFrame AnimTick)

-- | Spring demo view
springDemoView :: SpringDemoState -> E.Element SpringDemoMsg
springDemoView state =
  let currentX = Anim.springValue state.position
  in E.div_
    [ E.class_ "spring-demo p-8" ]
    [ E.h1_
        [ E.class_ "text-3xl font-bold mb-6" ]
        [ E.text "Spring Animation Demo" ]
    , E.div_
        [ E.class_ "relative h-32 bg-gray-100 rounded-lg mb-6" ]
        [ E.div_
            [ E.class_ "absolute top-1/2 -translate-y-1/2 w-16 h-16 bg-blue-500 rounded-full"
            , E.style "transform" ("translateX(" <> show currentX <> "px) translateY(-50%)")
            , E.style "transition" "none"  -- We're handling animation ourselves
            ]
            []
        ]
    , E.div_
        [ E.class_ "flex justify-center gap-4" ]
        [ springButton MoveLeft "← Left" "bg-purple-500 hover:bg-purple-600"
        , springButton MoveCenter "Center" "bg-gray-500 hover:bg-gray-600"
        , springButton MoveRight "Right →" "bg-purple-500 hover:bg-purple-600"
        ]
    , E.p_
        [ E.class_ "text-center text-sm text-gray-500 mt-4" ]
        [ E.text ("Position: " <> show currentX <> "px (target: " <> show state.targetX <> "px)") ]
    ]

-- | Spring demo button
springButton :: SpringDemoMsg -> String -> String -> E.Element SpringDemoMsg
springButton msg label colorClass =
  E.button_
    [ E.onClick msg
    , E.class_ ("px-6 py-3 text-white rounded-lg font-medium " <> colorClass)
    ]
    [ E.text label ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // http // fetch // example
-- ═══════════════════════════════════════════════════════════════════════════════

-- | HTTP fetch demo state
-- |
-- | Tracks loading state, response data, and structured errors.
type FetchState =
  { loading :: Boolean
  , result :: FetchResult
  , requestCount :: Int
  }

-- | Result of a fetch operation
-- |
-- | This type distinguishes between:
-- | - NotStarted: No request made yet
-- | - FetchSuccess: Server responded (check status for HTTP success/failure)
-- | - FetchError: Request never completed (network, CORS, timeout, etc.)
data FetchResult
  = NotStarted
  | FetchSuccess HttpSuccess
  | FetchError HttpError

-- | HTTP fetch messages
data FetchMsg
  = FetchData
  | FetchComplete HttpResult
  | ClearResult

-- | HTTP fetch application
-- |
-- | Demonstrates:
-- | - HTTP commands using fetch API
-- | - Loading states
-- | - Structured error handling with actionable suggestions
-- | - Response parsing
fetchApp :: AppCmd FetchState FetchMsg
fetchApp =
  { init: noCmd
      { loading: false
      , result: NotStarted
      , requestCount: 0
      }
  , update: fetchUpdate
  , view: fetchView
  }

-- | Update with HTTP effects
fetchUpdate :: FetchMsg -> FetchState -> Transition FetchState FetchMsg
fetchUpdate msg state = case msg of
  FetchData ->
    case state.loading of
      true -> noCmd state  -- Already loading
      false ->
        transition
          state { loading = true, requestCount = state.requestCount + 1 }
          (http
            { method: GET
            , url: "https://jsonplaceholder.typicode.com/posts/1"
            , headers: ([] :: Array (Tuple String String))
            , body: Nothing
            , expect: FetchComplete
            , timeout: Nothing
            })
  
  FetchComplete httpResult ->
    noCmd state 
      { loading = false
      , result = httpResultToFetchResult httpResult
      }
  
  ClearResult ->
    noCmd state { result = NotStarted }

-- | Convert HttpResult to our FetchResult
httpResultToFetchResult :: HttpResult -> FetchResult
httpResultToFetchResult httpResult = case httpResult of
  HttpOk success -> FetchSuccess success
  HttpErr err -> FetchError err

-- | Convert Foreign value to string representation
foreign import foreignToString :: Foreign -> String

-- | Fetch demo view
fetchView :: FetchState -> E.Element FetchMsg
fetchView state =
  E.div_
    [ E.class_ "fetch-demo p-8" ]
    [ E.h1_
        [ E.class_ "text-3xl font-bold mb-6" ]
        [ E.text "HTTP Fetch Demo" ]
    , E.p_
        [ E.class_ "text-sm text-gray-500 mb-4" ]
        [ E.text "Fetches data from JSONPlaceholder API" ]
    , E.div_
        [ E.class_ "mb-6" ]
        [ fetchButton state.loading ]
    , fetchResultView state.result
    , E.div_
        [ E.class_ "text-sm text-gray-400 mt-4" ]
        [ E.text ("Requests made: " <> show state.requestCount) ]
    ]

-- | Fetch button with loading state
fetchButton :: Boolean -> E.Element FetchMsg
fetchButton loading =
  E.button_
    [ E.onClick FetchData
    , E.class_ (buttonClass loading)
    , E.disabled loading
    ]
    [ E.text (buttonLabel loading) ]

-- | Button CSS class based on loading state
buttonClass :: Boolean -> String
buttonClass loading = case loading of
  true -> "px-6 py-3 bg-gray-400 text-white rounded-lg font-medium cursor-not-allowed"
  false -> "px-6 py-3 bg-blue-500 text-white rounded-lg font-medium hover:bg-blue-600"

-- | Button label based on loading state
buttonLabel :: Boolean -> String
buttonLabel loading = case loading of
  true -> "Loading..."
  false -> "Fetch Post"

-- | Display fetch result with comprehensive error information
fetchResultView :: FetchResult -> E.Element FetchMsg
fetchResultView result = case result of
  NotStarted ->
    E.div_
      [ E.class_ "p-4 bg-gray-100 rounded-lg text-gray-500" ]
      [ E.text "Click the button to fetch data" ]
  
  FetchSuccess success ->
    renderSuccess success
  
  FetchError err ->
    renderError err

-- | Render successful HTTP response
renderSuccess :: HttpSuccess -> E.Element FetchMsg
renderSuccess success =
  let 
    isHttpError = success.status > 399
    bgClass = case isHttpError of
      true -> "p-4 bg-yellow-100 rounded-lg"
      false -> "p-4 bg-green-100 rounded-lg"
    statusClass = case isHttpError of
      true -> "text-yellow-700 font-medium"
      false -> "text-green-700 font-medium"
  in E.div_
    [ E.class_ bgClass ]
    [ E.div_
        [ E.class_ "flex items-center justify-between mb-2" ]
        [ E.span_
            [ E.class_ statusClass ]
            [ E.text ("HTTP " <> show success.status <> " " <> success.statusText) ]
        , clearButton
        ]
    , E.pre_
        [ E.class_ "text-sm bg-white p-3 rounded overflow-x-auto max-h-48" ]
        [ E.text (foreignToString success.body) ]
    ]

-- | Render HTTP error with full context and actionable suggestions
renderError :: HttpError -> E.Element FetchMsg
renderError err =
  let ctx = errorContext err
  in E.div_
    [ E.class_ "bg-red-50 border border-red-200 rounded-lg overflow-hidden" ]
    [ -- Error header with type
      E.div_
        [ E.class_ "bg-red-100 px-4 py-3 flex items-center justify-between" ]
        [ E.div_
            [ E.class_ "flex items-center gap-2" ]
            [ E.span_
                [ E.class_ "text-red-600 font-bold" ]
                [ E.text (errorTypeName err) ]
            ]
        , clearButton
        ]
    
    -- What happened
    , E.div_
        [ E.class_ "px-4 py-3 border-b border-red-200" ]
        [ E.h4_
            [ E.class_ "text-sm font-semibold text-red-800 mb-1" ]
            [ E.text "What happened:" ]
        , E.p_
            [ E.class_ "text-red-700" ]
            [ E.text ctx.cause ]
        ]
    
    -- Request details
    , E.div_
        [ E.class_ "px-4 py-3 border-b border-red-200 bg-red-50" ]
        [ E.h4_
            [ E.class_ "text-sm font-semibold text-red-800 mb-2" ]
            [ E.text "Request details:" ]
        , E.div_
            [ E.class_ "text-sm text-red-700 space-y-1" ]
            [ E.div_ [] [ E.text ("URL: " <> ctx.url) ]
            , E.div_ [] [ E.text ("Method: " <> ctx.method) ]
            , E.div_ [] [ E.text ("Time: " <> ctx.timestamp) ]
            ]
        ]
    
    -- How to fix
    , E.div_
        [ E.class_ "px-4 py-3" ]
        [ E.h4_
            [ E.class_ "text-sm font-semibold text-red-800 mb-2" ]
            [ E.text "How to fix:" ]
        , E.ul_
            [ E.class_ "text-sm text-red-700 space-y-1" ]
            (map renderSuggestion ctx.suggestions)
        ]
    
    -- Debug info (collapsed by default in a real app)
    , E.div_
        [ E.class_ "px-4 py-2 bg-red-100 text-xs text-red-600" ]
        [ E.text ("Browser error: " <> ctx.browserError <> " — " <> ctx.browserMessage) ]
    ]

-- | Render a single suggestion
renderSuggestion :: String -> E.Element FetchMsg
renderSuggestion suggestion =
  E.li_
    [ E.class_ "pl-2" ]
    [ E.text suggestion ]

-- | Get human-readable error type name
errorTypeName :: HttpError -> String
errorTypeName err = case err of
  TimeoutError _ -> "Request Timeout"
  NetworkError _ -> "Network Error"
  CorsError _ -> "CORS Error"
  MixedContentError _ -> "Mixed Content Error"
  InvalidUrlError _ -> "Invalid URL"
  AbortedError _ -> "Request Aborted"
  UnknownError _ -> "Unknown Error"

-- | Extract error context from any HttpError variant
errorContext :: HttpError -> HttpErrorContext
errorContext err = case err of
  TimeoutError ctx -> ctx
  NetworkError ctx -> ctx
  CorsError ctx -> ctx
  MixedContentError ctx -> ctx
  InvalidUrlError ctx -> ctx
  AbortedError ctx -> ctx
  UnknownError ctx -> ctx

-- | Clear button used in multiple places
clearButton :: E.Element FetchMsg
clearButton =
  E.button_
    [ E.onClick ClearResult
    , E.class_ "text-sm text-gray-500 hover:text-gray-700"
    ]
    [ E.text "Clear" ]
