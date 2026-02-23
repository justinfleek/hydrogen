-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // runtime // demo
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Runtime Demo Entry Point
-- |
-- | Browser-executable demo of the Hydrogen runtime, showcasing:
-- |
-- | 1. Counter App — Simple state management, event handling
-- | 2. Todo App — List rendering, input handling, filtering
-- | 3. Timer App — Commands (delay, interval), self-scheduling
-- | 4. Spring Demo — Physics-based animation with requestAnimationFrame
-- | 5. Fetch App — HTTP commands with fetch API
-- |
-- | ## Building
-- |
-- | ```bash
-- | nix develop --command spago bundle --module Hydrogen.Runtime.Demo --outfile showcase/runtime-demo.js
-- | ```
-- |
-- | ## Running
-- |
-- | Open `showcase/runtime-demo.html` in a browser.
module Hydrogen.Runtime.Demo
  ( main
  ) where

import Prelude
  ( Unit
  , bind
  , discard
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Effect.Console as Console
import Hydrogen.Runtime.App as App
import Hydrogen.Runtime.Example as Ex

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // main
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main entry point for browser demo.
-- |
-- | Mounts all four example applications to their respective containers.
-- | Each container should exist in the HTML:
-- |
-- | - #counter-app
-- | - #todo-app
-- | - #timer-app
-- | - #spring-app
-- | - #fetch-app
main :: Effect Unit
main = do
  Console.log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  Console.log "                    HYDROGEN RUNTIME DEMO"
  Console.log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  
  -- Mount Counter App (simple, no commands)
  Console.log "Mounting Counter App..."
  counterResult <- App.mount "#counter-app" Ex.counterApp
  logMountResult "Counter" counterResult
  
  -- Mount Todo App (simple, no commands)
  Console.log "Mounting Todo App..."
  todoResult <- App.mount "#todo-app" Ex.todoApp
  logMountResult "Todo" todoResult
  
  -- Mount Timer App (with commands)
  Console.log "Mounting Timer App..."
  timerResult <- App.mountCmd "#timer-app" Ex.timerApp
  logMountResult "Timer" timerResult
  
  -- Mount Spring Demo App (with animation commands)
  Console.log "Mounting Spring Demo App..."
  springResult <- App.mountCmd "#spring-app" Ex.springDemoApp
  logMountResult "Spring" springResult
  
  -- Mount Fetch App (with HTTP commands)
  Console.log "Mounting Fetch App..."
  fetchResult <- App.mountCmd "#fetch-app" Ex.fetchApp
  logMountResult "Fetch" fetchResult
  
  Console.log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  Console.log "All apps mounted. Check the browser for the demo."
  Console.log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

-- | Log the result of mounting an app.
logMountResult :: forall a. String -> Maybe a -> Effect Unit
logMountResult name result = case result of
  Just _ -> Console.log ("  ✓ " <> name <> " App mounted successfully")
  Nothing -> Console.log ("  ✗ " <> name <> " App failed to mount (container not found)")
