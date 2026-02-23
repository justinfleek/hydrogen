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
  
  -- * Color Animation Application
  , ColorDemoState
  , ColorDemoMsg(..)
  , colorDemoApp
  
  -- * Sequence Animation Application
  , SequenceDemoState
  , SequenceDemoMsg(..)
  , sequenceDemoApp
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
  , (#)
  )

import Data.Array (filter, length, snoc)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple)
import Foreign (Foreign)
import Hydrogen.Motion.Spring (SpringConfig, springConfig, springWobbly)
import Hydrogen.Render.Element as E
import Hydrogen.Runtime.Animate as Anim
import Hydrogen.Schema.Motion.Easing as Easing
import Hydrogen.Runtime.App (App, AppCmd)
import Hydrogen.Runtime.Cmd 
  ( HttpError(..)
  , HttpErrorContext
  , HttpMethod(GET)
  , HttpResult(..)
  , HttpSuccess
  , Transition
  , animationFrame
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

-- | Stopwatch state with millisecond precision and lap times
type TimerState =
  { elapsed :: Number        -- Total elapsed milliseconds
  , running :: Boolean
  , laps :: Array Number     -- Lap times in milliseconds
  , lastLapTime :: Number    -- Time of last lap for delta display
  , startTime :: Number      -- When current run started
  }

-- | Timer messages
data TimerMsg
  = StartTimer Number        -- Start with timestamp
  | StopTimer
  | ResetTimer
  | RecordLap
  | TimerTick Number         -- Animation frame tick

-- | Timer application with commands
-- |
-- | Demonstrates:
-- | - High-precision timing with requestAnimationFrame
-- | - Lap recording
-- | - Start/Stop/Reset controls
timerApp :: AppCmd TimerState TimerMsg
timerApp =
  { init: noCmd 
      { elapsed: 0.0
      , running: false
      , laps: []
      , lastLapTime: 0.0
      , startTime: 0.0
      }
  , update: timerUpdate
  , view: timerView
  }

-- | Timer update with commands
timerUpdate :: TimerMsg -> TimerState -> Transition TimerState TimerMsg
timerUpdate msg state = case msg of
  StartTimer timestamp -> 
    case state.running of
      true -> noCmd state
      false -> 
        transition 
          state 
            { running = true
            , startTime = timestamp - state.elapsed  -- Account for previous elapsed time
            }
          (animationFrame TimerTick)
  
  StopTimer ->
    noCmd state { running = false }
  
  ResetTimer ->
    noCmd state 
      { elapsed = 0.0
      , running = false
      , laps = []
      , lastLapTime = 0.0
      , startTime = 0.0
      }
  
  RecordLap ->
    case state.running of
      false -> noCmd state
      true ->
        let lapTime = state.elapsed - state.lastLapTime
        in noCmd state 
            { laps = snoc state.laps lapTime
            , lastLapTime = state.elapsed
            }
  
  TimerTick timestamp ->
    case state.running of
      false -> noCmd state
      true -> 
        let newElapsed = timestamp - state.startTime
        in transition
            state { elapsed = newElapsed }
            (animationFrame TimerTick)

-- | Timer view
timerView :: TimerState -> E.Element TimerMsg
timerView state =
  E.div_
    [ E.class_ "timer-app p-6 text-center" ]
    [ E.h1_
        [ E.class_ "text-2xl font-bold mb-4" ]
        [ E.text "Stopwatch" ]
    
    -- Main time display
    , E.div_
        [ E.class_ "text-5xl font-mono mb-2 tabular-nums" ]
        [ E.text (formatTimeMs state.elapsed) ]
    
    -- Milliseconds display (smaller, below main)
    , E.div_
        [ E.class_ "text-xl font-mono text-gray-400 mb-6" ]
        [ E.text (formatMillis state.elapsed) ]
    
    -- Control buttons
    , E.div_
        [ E.class_ "flex justify-center gap-3 mb-4" ]
        [ case state.running of
            true -> 
              E.button_
                [ E.onClick StopTimer
                , E.class_ "px-5 py-2 bg-red-500 hover:bg-red-600 text-white rounded-lg font-medium"
                ]
                [ E.text "Stop" ]
            false ->
              E.button_
                [ E.onClick (StartTimer 0.0)  -- Will be replaced with actual timestamp via animationFrame
                , E.class_ "px-5 py-2 bg-green-500 hover:bg-green-600 text-white rounded-lg font-medium"
                ]
                [ E.text (case state.elapsed > 0.0 of
                    true -> "Resume"
                    false -> "Start") ]
        , case state.running of
            true ->
              E.button_
                [ E.onClick RecordLap
                , E.class_ "px-5 py-2 bg-blue-500 hover:bg-blue-600 text-white rounded-lg font-medium"
                ]
                [ E.text "Lap" ]
            false ->
              E.button_
                [ E.onClick ResetTimer
                , E.class_ "px-5 py-2 bg-gray-500 hover:bg-gray-600 text-white rounded-lg font-medium"
                ]
                [ E.text "Reset" ]
        ]
    
    -- Lap times
    , case length state.laps of
        0 -> E.div_ [] []
        _ -> 
          E.div_
            [ E.class_ "mt-4 max-h-32 overflow-y-auto" ]
            [ E.div_
                [ E.class_ "text-xs text-gray-500 uppercase tracking-wide mb-2" ]
                [ E.text "Lap Times" ]
            , E.div_
                [ E.class_ "space-y-1 text-sm font-mono" ]
                (mapWithIndex renderLap state.laps)
            ]
    ]

-- | Render a single lap
renderLap :: Int -> Number -> E.Element TimerMsg
renderLap idx lapTime =
  E.div_
    [ E.class_ "flex justify-between px-4 py-1 bg-gray-100 rounded" ]
    [ E.span_ [ E.class_ "text-gray-600" ] [ E.text ("Lap " <> show (idx + 1)) ]
    , E.span_ [] [ E.text (formatTimeMs lapTime) ]
    ]

-- | Map with index helper using accumulator for correct order
mapWithIndex :: forall a b. (Int -> a -> b) -> Array a -> Array b
mapWithIndex f arr = mapWithIndexAcc 0 f arr []

mapWithIndexAcc :: forall a b. Int -> (Int -> a -> b) -> Array a -> Array b -> Array b
mapWithIndexAcc idx f arr acc = 
  case arrayIndex idx arr of
    Nothing -> acc
    Just item -> mapWithIndexAcc (idx + 1) f arr (snoc acc (f idx item))

-- | FFI for array indexing used in mapWithIndex (takes constructors)
foreign import arrayIndexImpl 
  :: forall a. (a -> Maybe a) -> Maybe a -> Int -> Array a -> Maybe a

-- | Safe array indexing
arrayIndex :: forall a. Int -> Array a -> Maybe a
arrayIndex = arrayIndexImpl Just Nothing

-- | Format milliseconds as MM:SS
formatTimeMs :: Number -> String
formatTimeMs ms =
  let 
    totalSeconds = ms / 1000.0
    minutes = floorToInt (totalSeconds / 60.0)
    seconds = floorToInt totalSeconds - (minutes * 60)
  in padZero minutes <> ":" <> padZero seconds

-- | Format just the milliseconds portion
formatMillis :: Number -> String
formatMillis ms =
  let millis = floorToInt ms - (floorToInt (ms / 1000.0) * 1000)
  in "." <> padZeroThree millis

-- | Pad a number with leading zero (2 digits)
padZero :: Int -> String
padZero n = case n < 10 of
  true -> "0" <> show n
  false -> show n

-- | Pad a number with leading zeros (3 digits)
padZeroThree :: Int -> String
padZeroThree n 
  | n < 10 = "00" <> show n
  | n < 100 = "0" <> show n
  | otherwise = show n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // spring // demo // example
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spring animation demo state with adjustable physics parameters
type SpringDemoState =
  { position :: Anim.SpringState
  , targetX :: Number
  , stiffness :: Number   -- 10-500, controls speed
  , damping :: Number     -- 1-50, controls bounciness
  }

-- | Spring animation messages
data SpringDemoMsg
  = MoveLeft
  | MoveRight
  | MoveCenter
  | SetStiffness String   -- From range input
  | SetDamping String     -- From range input
  | AnimTick Number       -- timestamp

-- | Spring animation demo application
-- |
-- | Demonstrates:
-- | - Physics-based spring animations
-- | - Self-scheduling animation loop via Cmd
-- | - Adjustable spring parameters via sliders
springDemoApp :: AppCmd SpringDemoState SpringDemoMsg
springDemoApp =
  { init: noCmd
      { position: Anim.springState springWobbly 200.0
      , targetX: 200.0
      , stiffness: 180.0   -- Default wobbly stiffness
      , damping: 12.0      -- Default wobbly damping
      }
  , update: springDemoUpdate
  , view: springDemoView
  }

-- | Build SpringConfig from current slider values
buildSpringConfig :: Number -> Number -> SpringConfig
buildSpringConfig stiffness damping = springConfig stiffness damping

-- | Update with spring physics
springDemoUpdate :: SpringDemoMsg -> SpringDemoState -> Transition SpringDemoState SpringDemoMsg
springDemoUpdate msg state = case msg of
  MoveLeft ->
    let cfg = buildSpringConfig state.stiffness state.damping
        newPos = Anim.springTo (state.position { config = cfg }) 50.0
    in transition state { position = newPos, targetX = 50.0 } (animationFrame AnimTick)
  
  MoveRight ->
    let cfg = buildSpringConfig state.stiffness state.damping
        newPos = Anim.springTo (state.position { config = cfg }) 350.0
    in transition state { position = newPos, targetX = 350.0 } (animationFrame AnimTick)
  
  MoveCenter ->
    let cfg = buildSpringConfig state.stiffness state.damping
        newPos = Anim.springTo (state.position { config = cfg }) 200.0
    in transition state { position = newPos, targetX = 200.0 } (animationFrame AnimTick)
  
  SetStiffness str ->
    let val = parseNumberSafe str 180.0
    in noCmd state { stiffness = val }
  
  SetDamping str ->
    let val = parseNumberSafe str 12.0
    in noCmd state { damping = val }
  
  AnimTick timestamp ->
    let newPos = Anim.tickSpring timestamp state.position
    in case Anim.springComplete newPos of
      true -> noCmd state { position = newPos }
      false -> transition state { position = newPos } (animationFrame AnimTick)

-- | Parse a number from string with default fallback
parseNumberSafe :: String -> Number -> Number
parseNumberSafe str def = parseNumberImpl str def

foreign import parseNumberImpl :: String -> Number -> Number

-- | Spring demo view
springDemoView :: SpringDemoState -> E.Element SpringDemoMsg
springDemoView state =
  let currentX = Anim.springValue state.position
  in E.div_
    [ E.class_ "spring-demo p-4" ]
    [ E.h1_
        [ E.class_ "text-xl font-bold mb-3" ]
        [ E.text "Spring Physics" ]
    
    -- Animation track
    , E.div_
        [ E.class_ "relative h-20 bg-gray-100 rounded-lg mb-4" ]
        [ E.div_
            [ E.class_ "absolute top-1/2 w-12 h-12 bg-blue-500 rounded-full shadow-lg"
            , E.style "transform" ("translateX(" <> show currentX <> "px) translateY(-50%)")
            , E.style "transition" "none"
            ]
            []
        ]
    
    -- Control buttons
    , E.div_
        [ E.class_ "flex justify-center gap-2 mb-4" ]
        [ springButton MoveLeft "←" "bg-purple-500 hover:bg-purple-600"
        , springButton MoveCenter "●" "bg-gray-500 hover:bg-gray-600"
        , springButton MoveRight "→" "bg-purple-500 hover:bg-purple-600"
        ]
    
    -- Sliders for spring parameters
    , E.div_
        [ E.class_ "space-y-3" ]
        [ -- Stiffness slider
          E.div_
            [ E.class_ "flex items-center gap-3" ]
            [ E.label_
                [ E.class_ "text-xs text-gray-500 w-16" ]
                [ E.text "Stiffness" ]
            , E.input_
                [ E.type_ "range"
                , E.min_ "10"
                , E.max_ "500"
                , E.step_ "10"
                , E.value (show (floorToInt state.stiffness))
                , E.onInput SetStiffness
                , E.class_ "flex-1 h-2 accent-purple-500"
                ]
            , E.span_
                [ E.class_ "text-xs font-mono w-10 text-right" ]
                [ E.text (show (floorToInt state.stiffness)) ]
            ]
        
        -- Damping slider
        , E.div_
            [ E.class_ "flex items-center gap-3" ]
            [ E.label_
                [ E.class_ "text-xs text-gray-500 w-16" ]
                [ E.text "Damping" ]
            , E.input_
                [ E.type_ "range"
                , E.min_ "1"
                , E.max_ "50"
                , E.step_ "1"
                , E.value (show (floorToInt state.damping))
                , E.onInput SetDamping
                , E.class_ "flex-1 h-2 accent-purple-500"
                ]
            , E.span_
                [ E.class_ "text-xs font-mono w-10 text-right" ]
                [ E.text (show (floorToInt state.damping)) ]
            ]
        ]
    
    -- Position readout
    , E.p_
        [ E.class_ "text-center text-xs text-gray-500 mt-3" ]
        [ E.text ("Position: " <> show (floorToInt currentX) <> "px") ]
    ]

-- | Spring demo button
springButton :: SpringDemoMsg -> String -> String -> E.Element SpringDemoMsg
springButton msg label colorClass =
  E.button_
    [ E.onClick msg
    , E.class_ ("px-4 py-2 text-white rounded-lg font-medium " <> colorClass)
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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // color // demo // example
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color animation demo state
-- |
-- | Demonstrates smooth color transitions with easing.
type ColorDemoState =
  { color :: Anim.ColorState
  , colorName :: String
  , duration :: Number    -- Transition duration in ms
  }

-- | Color animation messages
data ColorDemoMsg
  = SetRed
  | SetGreen
  | SetBlue
  | SetPurple
  | SetOrange
  | SetColorDuration String
  | ColorTick Number

-- | Color animation demo application
-- |
-- | Demonstrates:
-- | - RGB color interpolation
-- | - Easing applied to color channels
-- | - Adjustable transition duration
colorDemoApp :: AppCmd ColorDemoState ColorDemoMsg
colorDemoApp =
  { init: noCmd
      { color: Anim.colorState { r: 59.0, g: 130.0, b: 246.0 }  -- blue-500
      , colorName: "Blue"
      , duration: 500.0
      }
  , update: colorDemoUpdate
  , view: colorDemoView
  }

-- | Update with color animation
colorDemoUpdate :: ColorDemoMsg -> ColorDemoState -> Transition ColorDemoState ColorDemoMsg
colorDemoUpdate msg state = case msg of
  SetRed ->
    let newColor = Anim.colorTo state.color { r: 239.0, g: 68.0, b: 68.0 } state.duration Easing.easeOutCubic
    in transition state { color = newColor, colorName = "Red" } (animationFrame ColorTick)
  
  SetGreen ->
    let newColor = Anim.colorTo state.color { r: 34.0, g: 197.0, b: 94.0 } state.duration Easing.easeOutCubic
    in transition state { color = newColor, colorName = "Green" } (animationFrame ColorTick)
  
  SetBlue ->
    let newColor = Anim.colorTo state.color { r: 59.0, g: 130.0, b: 246.0 } state.duration Easing.easeOutCubic
    in transition state { color = newColor, colorName = "Blue" } (animationFrame ColorTick)
  
  SetPurple ->
    let newColor = Anim.colorTo state.color { r: 168.0, g: 85.0, b: 247.0 } state.duration Easing.easeOutCubic
    in transition state { color = newColor, colorName = "Purple" } (animationFrame ColorTick)
  
  SetOrange ->
    let newColor = Anim.colorTo state.color { r: 249.0, g: 115.0, b: 22.0 } state.duration Easing.easeOutCubic
    in transition state { color = newColor, colorName = "Orange" } (animationFrame ColorTick)
  
  SetColorDuration str ->
    let val = parseNumberSafe str 500.0
    in noCmd state { duration = val }
  
  ColorTick timestamp ->
    let newColor = Anim.tickColor timestamp state.color
    in case Anim.colorComplete newColor of
      true -> noCmd state { color = newColor }
      false -> transition state { color = newColor } (animationFrame ColorTick)

-- | Color demo view
colorDemoView :: ColorDemoState -> E.Element ColorDemoMsg
colorDemoView state =
  let 
    currentColor = Anim.colorValue state.color
    cssColor = Anim.rgbToCss currentColor
  in E.div_
    [ E.class_ "color-demo p-4" ]
    [ E.h1_
        [ E.class_ "text-xl font-bold mb-3" ]
        [ E.text "Color Transitions" ]
    
    -- Color preview box
    , E.div_
        [ E.class_ "w-full h-32 rounded-lg shadow-lg mb-4 flex items-center justify-center"
        , E.style "background-color" cssColor
        ]
        [ E.span_
            [ E.class_ "text-white text-xl font-bold drop-shadow-lg" ]
            [ E.text state.colorName ]
        ]
    
    -- Color buttons
    , E.div_
        [ E.class_ "flex justify-center gap-2 mb-4" ]
        [ colorButton SetRed "bg-red-500"
        , colorButton SetGreen "bg-green-500"
        , colorButton SetBlue "bg-blue-500"
        , colorButton SetPurple "bg-purple-500"
        , colorButton SetOrange "bg-orange-500"
        ]
    
    -- Duration slider
    , E.div_
        [ E.class_ "flex items-center gap-3 mb-3" ]
        [ E.label_
            [ E.class_ "text-xs text-gray-500 w-16" ]
            [ E.text "Duration" ]
        , E.input_
            [ E.type_ "range"
            , E.min_ "100"
            , E.max_ "2000"
            , E.step_ "100"
            , E.value (show (floorToInt state.duration))
            , E.onInput SetColorDuration
            , E.class_ "flex-1 h-2 accent-purple-500"
            ]
        , E.span_
            [ E.class_ "text-xs font-mono w-14 text-right" ]
            [ E.text (show (floorToInt state.duration) <> "ms") ]
        ]
    
    -- Current RGB values
    , E.div_
        [ E.class_ "text-xs text-gray-600 font-mono text-center" ]
        [ E.text ("RGB(" <> show (intPart currentColor.r) <> ", " 
                        <> show (intPart currentColor.g) <> ", " 
                        <> show (intPart currentColor.b) <> ")") ]
    ]

-- | Color picker button (shows the color itself)
colorButton :: ColorDemoMsg -> String -> E.Element ColorDemoMsg
colorButton msg colorClass =
  E.button_
    [ E.onClick msg
    , E.class_ ("w-12 h-12 rounded-full " <> colorClass <> " hover:scale-110 transition-transform shadow-md")
    ]
    []

-- | Convert Number to Int for display (truncate decimals)
intPart :: Number -> Int
intPart n = 
  let scaled = n * 1.0
  in case scaled < 0.0 of
    true -> 0 - (intPartPositive (0.0 - scaled))
    false -> intPartPositive scaled

-- | Helper for positive numbers
intPartPositive :: Number -> Int
intPartPositive n = 
  -- Simple truncation: subtract decimal part
  let asInt = n / 1.0
  in case asInt > 2147483647.0 of
    true -> 2147483647
    false -> floorToInt n

-- | Floor a number to int (FFI would be cleaner but keeping pure)
foreign import floorToInt :: Number -> Int

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // sequence // demo // example
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sequence animation demo state
-- |
-- | Demonstrates chained animations with delays.
type SequenceDemoState =
  { seq :: Anim.Sequence
  , running :: Boolean
  }

-- | Sequence animation messages
data SequenceDemoMsg
  = StartSequence
  | ResetSequence
  | SeqTick Number

-- | Sequence animation demo application
-- |
-- | Demonstrates:
-- | - Sequential animations (one after another)
-- | - Delay steps between animations
-- | - Building complex motion from simple primitives
sequenceDemoApp :: AppCmd SequenceDemoState SequenceDemoMsg
sequenceDemoApp =
  { init: noCmd
      { seq: buildDemoSequence 0.0
      , running: false
      }
  , update: sequenceDemoUpdate
  , view: sequenceDemoView
  }

-- | Build the demo sequence: move right, pause, move left, pause, center
buildDemoSequence :: Number -> Anim.Sequence
buildDemoSequence initial =
  Anim.sequence initial
    # Anim.andThen 300.0 400.0 Easing.easeOutBack    -- Move right with overshoot
    # Anim.withDelay 200.0                             -- Pause
    # Anim.andThen 100.0 400.0 Easing.easeOutBack    -- Move left with overshoot
    # Anim.withDelay 200.0                             -- Pause
    # Anim.andThen 200.0 600.0 Easing.easeInOutQuad  -- Return to center smoothly

-- | Update with sequence animation
sequenceDemoUpdate :: SequenceDemoMsg -> SequenceDemoState -> Transition SequenceDemoState SequenceDemoMsg
sequenceDemoUpdate msg state = case msg of
  StartSequence ->
    case state.running of
      true -> noCmd state
      false ->
        -- Build a fresh sequence from current position, will start on first tick
        let currentVal = Anim.sequenceValue state.seq
            newSeq = buildDemoSequence currentVal
        in transition state { seq = newSeq, running = true } (animationFrame SeqTick)
  
  ResetSequence ->
    noCmd state { seq = buildDemoSequence 200.0, running = false }
  
  SeqTick timestamp ->
    let newSeq = Anim.tickSequence timestamp state.seq
    in case Anim.sequenceComplete newSeq of
      true -> noCmd state { seq = newSeq, running = false }
      false -> transition state { seq = newSeq } (animationFrame SeqTick)

-- | Sequence demo view
sequenceDemoView :: SequenceDemoState -> E.Element SequenceDemoMsg
sequenceDemoView state =
  let currentX = Anim.sequenceValue state.seq
  in E.div_
    [ E.class_ "sequence-demo p-8" ]
    [ E.h1_
        [ E.class_ "text-3xl font-bold mb-6" ]
        [ E.text "Sequence Animation Demo" ]
    , E.p_
        [ E.class_ "text-sm text-gray-500 mb-4" ]
        [ E.text "Chained animations: right → pause → left → pause → center" ]
    
    -- Animation track
    , E.div_
        [ E.class_ "relative h-24 bg-gray-100 rounded-lg mb-6 overflow-hidden" ]
        [ -- Track markers
          E.div_ [ E.class_ "absolute inset-0 flex justify-between px-8 items-center text-xs text-gray-400" ]
            [ E.span_ [] [ E.text "100px" ]
            , E.span_ [] [ E.text "200px" ]
            , E.span_ [] [ E.text "300px" ]
            ]
        -- The animated ball
        , E.div_
            [ E.class_ "absolute top-1/2 w-12 h-12 bg-gradient-to-br from-purple-500 to-pink-500 rounded-full shadow-lg"
            , E.style "transform" ("translateX(" <> show currentX <> "px) translateY(-50%)")
            , E.style "transition" "none"
            ]
            []
        ]
    
    -- Controls
    , E.div_
        [ E.class_ "flex gap-4 mb-4" ]
        [ seqButton StartSequence 
            (case state.running of
              true -> "Running..."
              false -> "Start Sequence")
            (case state.running of
              true -> "bg-gray-400 cursor-not-allowed"
              false -> "bg-purple-500 hover:bg-purple-600")
            state.running
        , seqButton ResetSequence "Reset" "bg-gray-500 hover:bg-gray-600" false
        ]
    
    -- Position readout
    , E.div_
        [ E.class_ "text-sm text-gray-600 font-mono" ]
        [ E.text ("Position: " <> show (intPart currentX) <> "px") ]
    ]

-- | Sequence demo button
seqButton :: SequenceDemoMsg -> String -> String -> Boolean -> E.Element SequenceDemoMsg
seqButton msg label colorClass disabled =
  E.button_
    [ E.onClick msg
    , E.class_ ("px-6 py-3 text-white rounded-lg font-medium " <> colorClass)
    , E.disabled disabled
    ]
    [ E.text label ]
