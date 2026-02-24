-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // tour // examples
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Comprehensive usage examples for Hydrogen Product Tours
-- |
-- | This module provides complete, production-ready examples demonstrating
-- | all major tour patterns:
-- |
-- | - **Basic Linear Tour**: Simple step-by-step onboarding
-- | - **Branching Tour**: User choices affect the tour path
-- | - **Interactive Tutorial**: Tours that wait for user actions
-- | - **Hotspot System**: Persistent discoverable hints
-- | - **Accessibility-First Tour**: WCAG 2.1 AA compliant patterns
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hydrogen.Tour as Tour
-- | import Hydrogen.Tour.Examples as Examples
-- |
-- | -- Use a pre-built example
-- | myApp state = case state.showTour of
-- |   true -> map TourMsg (Examples.basicTour TourMsg)
-- |   false -> mainContent
-- |
-- | -- Or use examples as templates for your own tours
-- | ```
-- |
-- | ## Architecture
-- |
-- | All tours follow the Elm architecture:
-- |
-- | ```
-- | TourState x TourMsg -> TourState x [TourCmd]
-- | view :: TourState -> Element TourMsg
-- | ```
-- |
-- | State changes are pure. Side effects (DOM, storage, analytics) are
-- | represented as commands that the runtime executes.
-- |
-- | ## Wiring Into Your App
-- |
-- | 1. Add `tourState :: Tour.TourState YourMsg` to your app state
-- | 2. Initialize: `Tour.initTour (Tour.mkTourId "my-tour") mySteps`
-- | 3. Render: `map TourAction (Tour.tour state.tourState)`
-- | 4. Handle messages in your update function
-- |
-- | See individual examples below for complete patterns.
-- |
-- | ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | ## Prop Builders Reference
-- |
-- | ### Step Configuration
-- |
-- | | Builder | Description | Example |
-- | |---------|-------------|---------|
-- | | `target` | Element to highlight | `target (ByTestId (mkTestId "btn"))` |
-- | | `title` | Step heading | `title "Welcome!"` |
-- | | `body` | Step description | `body "Click here to begin."` |
-- | | `placement` | Tooltip position | `placement Bottom Center` |
-- | | `placementWithOffset` | Position with offset | `placementWithOffset Right Center (Pixel 20) (Pixel 0)` |
-- | | `buttons` | Action buttons | `buttons [nextButton "Continue"]` |
-- | | `arrow` | Show pointer arrow | `arrow` (default) |
-- | | `noArrow` | Hide pointer arrow | `noArrow` |
-- | | `highlight` | Spotlight config | `highlight (highlightPadding (Pixel 12) defaultHighlight)` |
-- | | `scrollIntoView` | Auto-scroll config | `scrollIntoView defaultScroll` |
-- | | `noScroll` | Disable auto-scroll | `noScroll` |
-- |
-- | ### Button Builders
-- |
-- | | Builder | Description |
-- | |---------|-------------|
-- | | `nextButton "Label"` | Advance to next step (Primary style) |
-- | | `prevButton "Label"` | Go to previous step (Secondary style) |
-- | | `skipButton "Label"` | Skip/dismiss tour (Text style) |
-- | | `completeButton "Label"` | Complete tour (Primary style) |
-- | | `customButton "Label" msg variant` | Emit custom message |
-- | | `button "Label" action variant` | Full control |
-- |
-- | ### Target Selection
-- |
-- | | Target Type | Description | Example |
-- | |-------------|-------------|---------|
-- | | `ByTestId` | data-testid attribute | `ByTestId (mkTestId "submit-btn")` |
-- | | `BySelector` | CSS selector | `BySelector (unsafeSelector "#main-nav")` |
-- | | `ByRole` | ARIA role + name | `ByRole RoleButton (Just "Submit")` |
-- | | `NoTarget` | Centered modal | `NoTarget` |
-- |
-- | ### Tour Configuration
-- |
-- | | Builder | Description | Default |
-- | |---------|-------------|---------|
-- | | `withOverlayColor` | Overlay background | `"rgba(0,0,0,0.75)"` |
-- | | `withOverlayOpacity` | Overlay opacity | `0.75` |
-- | | `withKeyboardNav` | Arrow key navigation | `true` |
-- | | `withCloseOnOverlay` | Click overlay to close | `false` |
-- | | `withCloseOnEscape` | Escape key to close | `true` |
-- |
-- | ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | ## CSS Custom Properties
-- |
-- | The tour components respect these CSS custom properties for theming:
-- |
-- | ```css
-- | :root {
-- |   /* Overlay */
-- |   --tour-overlay-color: rgba(0, 0, 0, 0.75);
-- |   --tour-overlay-transition: opacity 300ms ease;
-- |
-- |   /* Spotlight */
-- |   --tour-spotlight-padding: 8px;
-- |   --tour-spotlight-radius: 4px;
-- |   --tour-spotlight-transition: all 300ms ease-out;
-- |   --tour-spotlight-ring-color: rgba(255, 255, 255, 0.1);
-- |
-- |   /* Tooltip */
-- |   --tour-tooltip-bg: hsl(var(--popover));
-- |   --tour-tooltip-fg: hsl(var(--popover-foreground));
-- |   --tour-tooltip-border: hsl(var(--border));
-- |   --tour-tooltip-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1);
-- |   --tour-tooltip-radius: 0.5rem;
-- |   --tour-tooltip-padding: 1rem;
-- |   --tour-tooltip-max-width: 20rem;
-- |
-- |   /* Progress */
-- |   --tour-progress-dot-size: 6px;
-- |   --tour-progress-dot-active: hsl(var(--primary));
-- |   --tour-progress-dot-inactive: hsl(var(--muted));
-- |   --tour-progress-gap: 6px;
-- |
-- |   /* Buttons */
-- |   --tour-button-height: 36px;
-- |   --tour-button-padding: 0 16px;
-- |   --tour-button-radius: 6px;
-- |
-- |   /* Animation */
-- |   --tour-enter-duration: 200ms;
-- |   --tour-exit-duration: 150ms;
-- |   --tour-morph-duration: 300ms;
-- | }
-- | ```
-- |
-- | ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | ## Data Attributes
-- |
-- | The tour runtime sets these data attributes for styling and testing:
-- |
-- | | Attribute | Element | Values | Description |
-- | |-----------|---------|--------|-------------|
-- | | `data-tour-active` | Container | `"true"` | Tour is active |
-- | | `data-tour-step` | Container | `"0"`, `"1"`, ... | Current step index |
-- | | `data-tour-total` | Container | `"5"` | Total step count |
-- | | `data-tour-spotlight` | Spotlight | `"true"` | Spotlight element |
-- | | `data-tour-tooltip` | Tooltip | `"true"` | Tooltip element |
-- | | `data-placement` | Tooltip | `"top"`, `"right"`, `"bottom"`, `"left"` | Tooltip placement |
-- | | `data-target` | Spotlight | CSS selector | Target element selector |
-- | | `data-padding` | Spotlight | `"8"` | Spotlight padding in px |
-- | | `data-radius` | Spotlight | `"4"` | Spotlight radius in px |
-- |
-- | ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | ## Keyboard Shortcuts
-- |
-- | When `keyboardNavEnabled` is true (default):
-- |
-- | | Key | Action |
-- | |-----|--------|
-- | | `ArrowRight` | Next step |
-- | | `ArrowLeft` | Previous step |
-- | | `Escape` | Dismiss tour (if `closeOnEscape` is true) |
-- | | `Tab` | Navigate within tooltip |
-- | | `Enter` / `Space` | Activate focused button |
-- |
-- | The tour traps focus within the tooltip for accessibility.
-- |
module Hydrogen.Tour.Examples
  ( -- * Example 1: Basic Linear Tour
    basicTour
  , basicTourSteps
  , BasicTourMsg
    -- * Example 2: Branching Tour
  , branchingTour
  , branchingTourSteps
  , BranchingTourMsg(..)
  , BranchPath(..)
    -- * Example 3: Interactive Tutorial
  , interactiveTour
  , interactiveTourSteps
  , InteractiveTourMsg(..)
  , InteractiveState
  , initialInteractiveState
    -- * Example 4: Hotspot System
  , hotspotExample
  , Hotspot
  , HotspotConfig
  , HotspotMsg(..)
  , mkHotspot
  , hotspotButton
    -- * Example 5: Accessibility-First Tour
  , accessibleTour
  , accessibleTourSteps
  , AccessibleTourMsg
    -- * Wiring Helpers
  , TourWiring
  , wireTour
  , handleTourCmd
  ) where

import Prelude

import Data.Array (filter, length)
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Effect.Console (log)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Tour.State (TourMsg, TourState, initTour)
import Hydrogen.Tour.Step (ButtonAction(ActionGoTo), ButtonVariant(Primary, Secondary), Step, body, button, buttons, completeButton, customButton, defaultHighlight, highlight, highlightPadding, nextButton, noArrow, placement, prevButton, skipButton, step, target, title)
import Hydrogen.Tour.Types (Alignment(Center, Start), AriaRole(RoleButton, RoleNavigation, RoleTextbox), Pixel(Pixel), Side(Bottom, Left, Right, Top), Target(ByRole, ByTestId, NoTarget), TourId, mkStepId, mkTestId, mkTourId)
import Hydrogen.Tour.Update (TourCmd(EmitAnalytics, FocusStep, PersistCompletion, PersistDismissal, PersistSnooze, ResolveTarget, RestoreFocus, ScheduleResume, ScrollToStep))
import Hydrogen.Tour.View (tour)
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                              // example 1: basic linear tour
-- ═══════════════════════════════════════════════════════════════════════════════

{-|
  EXAMPLE 1: BASIC LINEAR TOUR
  
  A simple 3-step onboarding tour. This is the most common pattern:
  - Welcome step (no target, centered modal)
  - Feature highlight step (targets an element)
  - Completion step
  
  USAGE:
  
  ```purescript
  import Hydrogen.Tour.Examples as Ex
  
  type AppState = { tour :: TourState BasicTourMsg, ... }
  
  data AppMsg = TourAction (TourMsg BasicTourMsg) | ...
  
  initialState :: AppState
  initialState = 
    { tour: initTour (mkTourId "onboarding") Ex.basicTourSteps
    , ...
    }
  
  render :: AppState -> HH.HTML _ AppMsg
  render state = HH.div_
    [ mainContent
    , map TourAction (tour state.tour)
    ]
  
  handleAction :: AppMsg -> HalogenM ...
  handleAction = case _ of
    TourAction msg -> do
      oldState <- H.gets _.tour
      let result = update msg oldState
      H.modify_ _ { tour = result.state }
      traverse_ handleTourCmd result.cmds
  ```
  
  EXPECTED BEHAVIOR:
  
  1. Tour starts when StartTour message is dispatched
  2. Step 1: Centered welcome modal with "Get Started" button
  3. Step 2: Highlights the sidebar navigation
  4. Step 3: Highlights settings with "Done" button
  5. Completion persists to localStorage, analytics event fired
-}

-- | Type alias for basic tour messages (no custom actions needed)
type BasicTourMsg = Unit

-- | Render the basic linear tour
-- |
-- | This renders the tour UI when active, or nothing when inactive.
-- | The tour state should live in your app state.
basicTour :: forall w. TourState BasicTourMsg -> HH.HTML w (TourMsg BasicTourMsg)
basicTour = tour

-- | Step definitions for the basic linear tour
basicTourSteps :: Array (Step BasicTourMsg)
basicTourSteps =
  [ -- Step 1: Welcome (no target, centered modal)
    step (mkStepId "welcome")
      [ target NoTarget
      , title "Welcome to Our App!"
      , body "Let's take a quick tour to help you get started. This will only take a minute."
      , noArrow
      , buttons
          [ nextButton "Get Started"
          , skipButton "Skip Tour"
          ]
      ]
  
  , -- Step 2: Sidebar Navigation
    step (mkStepId "sidebar")
      [ target (ByTestId (mkTestId "sidebar-nav"))
      , title "Navigation"
      , body "Use the sidebar to navigate between different sections of the app."
      , placement Left Center
      , buttons
          [ prevButton "Back"
          , nextButton "Next"
          ]
      ]
  
  , -- Step 3: Settings (final step)
    step (mkStepId "settings")
      [ target (ByTestId (mkTestId "settings-button"))
      , title "Settings"
      , body "Customize your experience in the settings panel."
      , placement Bottom Start
      , buttons
          [ prevButton "Back"
          , completeButton "Done"
          ]
      ]
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                // example 2: branching tour
-- ═══════════════════════════════════════════════════════════════════════════════

{-|
  EXAMPLE 2: BRANCHING TOUR
  
  A tour where the user's choices affect which steps they see.
  Common for:
  - Role-based onboarding (admin vs. user)
  - Feature-specific deep dives
  - Skill-based tutorials (beginner vs. advanced)
  
  USAGE:
  
  ```purescript
  type AppState = 
    { tour :: TourState BranchingTourMsg
    , selectedPath :: Maybe BranchPath
    }
  
  handleAction = case _ of
    TourAction (CustomAction (SelectPath path)) -> do
      H.modify_ _ { selectedPath = Just path }
      -- Jump to the appropriate step
      let stepId = case path of
            BasicPath -> mkStepId "basic-intro"
            AdvancedPath -> mkStepId "advanced-intro"
      handleAction (TourAction (GoToStepById stepId))
  ```
  
  EXPECTED BEHAVIOR:
  
  1. Welcome step asks "Are you new or experienced?"
  2. User clicks "I'm New" -> BasicPath steps
  3. User clicks "I'm Experienced" -> AdvancedPath steps
  4. Both paths converge at the final "Complete" step
-}

-- | Branch path options
data BranchPath
  = BasicPath
  | AdvancedPath

derive instance eqBranchPath :: Eq BranchPath

-- | Messages for the branching tour
data BranchingTourMsg
  = SelectPath BranchPath
  | BranchComplete

-- | Render the branching tour
branchingTour :: forall w. TourState BranchingTourMsg -> HH.HTML w (TourMsg BranchingTourMsg)
branchingTour = tour

-- | Step definitions for the branching tour
branchingTourSteps :: Array (Step BranchingTourMsg)
branchingTourSteps =
  [ -- Step 1: Branch selection
    step (mkStepId "choose-path")
      [ target NoTarget
      , title "Choose Your Path"
      , body "How familiar are you with our platform?"
      , noArrow
      , buttons
          [ customButton "I'm New" (SelectPath BasicPath) Primary
          , customButton "I'm Experienced" (SelectPath AdvancedPath) Secondary
          ]
      ]
  
  -- Basic Path Steps
  , step (mkStepId "basic-intro")
      [ target (ByTestId (mkTestId "dashboard"))
      , title "Your Dashboard"
      , body "This is your home base. Everything starts here. Let's walk through the basics."
      , placement Bottom Center
      , buttons
          [ nextButton "Continue"
          ]
      ]
  
  , step (mkStepId "basic-create")
      [ target (ByTestId (mkTestId "create-button"))
      , title "Create Your First Item"
      , body "Click this button whenever you want to create something new."
      , placement Right Center
      , buttons
          [ prevButton "Back"
          , button "Done with Basics" (ActionGoTo (mkStepId "complete")) Primary
          ]
      ]
  
  -- Advanced Path Steps
  , step (mkStepId "advanced-intro")
      [ target (ByTestId (mkTestId "power-menu"))
      , title "Power User Menu"
      , body "Access advanced features, keyboard shortcuts, and automation tools here."
      , placement Left Center
      , buttons
          [ nextButton "Show Me More"
          ]
      ]
  
  , step (mkStepId "advanced-shortcuts")
      [ target (ByTestId (mkTestId "keyboard-shortcuts"))
      , title "Keyboard Shortcuts"
      , body "Press '?' at any time to see all available shortcuts."
      , placement Bottom Center
      , buttons
          [ prevButton "Back"
          , button "Finish Tour" (ActionGoTo (mkStepId "complete")) Primary
          ]
      ]
  
  -- Convergence: Both paths end here
  , step (mkStepId "complete")
      [ target NoTarget
      , title "You're All Set!"
      , body "You've completed the tour. Explore on your own, and remember: help is always available in the '?' menu."
      , noArrow
      , buttons
          [ customButton "Start Exploring" BranchComplete Primary
          ]
      ]
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                             // example 3: interactive tutorial
-- ═══════════════════════════════════════════════════════════════════════════════

{-|
  EXAMPLE 3: INTERACTIVE TUTORIAL
  
  A tour that waits for the user to complete specific actions before proceeding.
  Uses the "paused" state to block navigation until conditions are met.
  
  USAGE:
  
  ```purescript
  type AppState = 
    { tour :: TourState InteractiveTourMsg
    , interactive :: InteractiveState
    }
  
  handleAction = case _ of
    -- User performed the required action
    UserTypedInInput value -> do
      H.modify_ \s -> s { interactive = s.interactive { textEntered = true } }
      -- Check if we can advance
      state <- H.get
      when state.interactive.textEntered $
        handleAction (TourAction NextStep)
    
    -- Custom tour action
    TourAction (CustomAction (WaitForAction _)) -> do
      -- Pause the tour until action is complete
      handleAction (TourAction PauseTour)
  ```
  
  EXPECTED BEHAVIOR:
  
  1. Step explains what user needs to do
  2. Tour pauses (waiting for action)
  3. User performs the action (e.g., types in a field)
  4. App detects action completion, resumes tour
  5. Next step celebrates success
-}

-- | State for tracking interactive actions
type InteractiveState =
  { textEntered :: Boolean
  , itemCreated :: Boolean
  , fileUploaded :: Boolean
  }

-- | Initial interactive state
initialInteractiveState :: InteractiveState
initialInteractiveState =
  { textEntered: false
  , itemCreated: false
  , fileUploaded: false
  }

-- | Messages for the interactive tutorial
data InteractiveTourMsg
  = WaitForAction String
  | ActionCompleted String
  | CelebrateSuccess

-- | Render the interactive tour
interactiveTour :: forall w. TourState InteractiveTourMsg -> HH.HTML w (TourMsg InteractiveTourMsg)
interactiveTour = tour

-- | Step definitions for the interactive tutorial
interactiveTourSteps :: Array (Step InteractiveTourMsg)
interactiveTourSteps =
  [ -- Step 1: Introduction
    step (mkStepId "interactive-intro")
      [ target NoTarget
      , title "Learn by Doing"
      , body "This tutorial will guide you through real actions. You'll actually use the app as we go!"
      , noArrow
      , buttons
          [ nextButton "Let's Start"
          , skipButton "Skip Tutorial"
          ]
      ]
  
  -- Step 2: Wait for text input
  , step (mkStepId "enter-text")
      [ target (ByRole RoleTextbox (Just "Project name"))
      , title "Name Your Project"
      , body "Type a name for your project in this field. We'll wait for you."
      , placement Top Center
      , highlight (highlightPadding (Pixel 12) defaultHighlight)
      , buttons
          [ customButton "I've entered a name" (ActionCompleted "text") Primary
          , skipButton "Skip this step"
          ]
      ]
  
  -- Step 3: Success feedback
  , step (mkStepId "text-success")
      [ target (ByRole RoleTextbox (Just "Project name"))
      , title "Great Job!"
      , body "You've named your project. Now let's create it."
      , placement Top Center
      , buttons
          [ nextButton "Continue"
          ]
      ]
  
  -- Step 4: Wait for button click
  , step (mkStepId "create-item")
      [ target (ByTestId (mkTestId "create-project-btn"))
      , title "Create the Project"
      , body "Click the Create button to make your project. Go ahead, we'll wait!"
      , placement Bottom Center
      , buttons
          [ customButton "I've clicked it" (ActionCompleted "create") Primary
          , prevButton "Go Back"
          ]
      ]
  
  -- Step 5: Completion
  , step (mkStepId "interactive-complete")
      [ target NoTarget
      , title "Congratulations!"
      , body "You've created your first project. You're ready to start using the app for real."
      , noArrow
      , buttons
          [ completeButton "Finish Tutorial"
          ]
      ]
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                 // example 4: hotspot system
-- ═══════════════════════════════════════════════════════════════════════════════

{-|
  EXAMPLE 4: HOTSPOT SYSTEM
  
  Persistent discoverable hints that users can click to learn about features.
  Unlike tours that interrupt, hotspots are opt-in and non-blocking.
  
  USAGE:
  
  ```purescript
  type AppState = 
    { hotspots :: Array Hotspot
    , activeHotspot :: Maybe String
    , dismissedHotspots :: Array String
    }
  
  render state = HH.div_
    [ mainContent
    , -- Render hotspot buttons
      HH.div [ cls [ "hotspot-container" ] ]
        (map (hotspotButton HotspotMsg state.dismissedHotspots) myHotspots)
    , -- Render active hotspot tooltip
      case state.activeHotspot of
        Just id -> hotspotTooltip id (findHotspot id state.hotspots)
        Nothing -> HH.text ""
    ]
  
  handleAction = case _ of
    HotspotMsg (ShowHotspot id) ->
      H.modify_ _ { activeHotspot = Just id }
    HotspotMsg (DismissHotspot id) ->
      H.modify_ \s -> s 
        { activeHotspot = Nothing
        , dismissedHotspots = snoc s.dismissedHotspots id
        }
  ```
  
  EXPECTED BEHAVIOR:
  
  1. Pulsing indicators appear near features
  2. User clicks indicator to see tooltip
  3. User can dismiss (remembers preference)
  4. Hotspots don't interfere with normal app usage
-}

-- | Hotspot definition
type Hotspot =
  { id :: String
  , target :: Target
  , title :: String
  , body :: String
  , placement :: Side
  }

-- | Hotspot configuration
type HotspotConfig =
  { showOnFirstVisit :: Boolean
  , persistDismissal :: Boolean
  , pulseAnimation :: Boolean
  }

-- | Messages for the hotspot system
data HotspotMsg
  = ShowHotspot String
  | HideHotspot String
  | DismissHotspot String

-- | Create a hotspot
mkHotspot :: String -> Target -> String -> String -> Side -> Hotspot
mkHotspot id targetEl title' body' placement' =
  { id
  , target: targetEl
  , title: title'
  , body: body'
  , placement: placement'
  }

-- | Render a hotspot button (the pulsing indicator)
hotspotButton 
  :: forall w msg
   . (HotspotMsg -> msg) 
  -> Array String 
  -> Hotspot 
  -> HH.HTML w msg
hotspotButton toMsg dismissed hotspot =
  if isDismissed hotspot.id dismissed
  then HH.text ""
  else
    HH.button
      [ cls 
          [ "absolute w-4 h-4 rounded-full bg-primary"
          , "animate-pulse cursor-pointer"
          , "hover:scale-125 transition-transform"
          , "focus:outline-none focus:ring-2 focus:ring-primary focus:ring-offset-2"
          ]
      , HP.type_ HP.ButtonButton
      , ARIA.label ("Learn about " <> hotspot.title)
      , ARIA.expanded "false"
      , HE.onClick \_ -> toMsg (ShowHotspot hotspot.id)
      ]
      [ -- Inner dot
        HH.span
          [ cls [ "absolute inset-1 rounded-full bg-primary-foreground" ] ]
          []
      ]

-- | Check if a hotspot has been dismissed
isDismissed :: String -> Array String -> Boolean
isDismissed id dismissed = id `elem` dismissed
  where
  elem :: forall a. Eq a => a -> Array a -> Boolean
  elem x xs = length (filter (_ == x) xs) > 0

-- | Complete hotspot example with multiple hotspots
hotspotExample :: Array Hotspot
hotspotExample =
  [ mkHotspot "search" 
      (ByTestId (mkTestId "search-bar"))
      "Quick Search"
      "Press Cmd+K to quickly search for anything in the app."
      Bottom
  
  , mkHotspot "notifications"
      (ByTestId (mkTestId "notification-bell"))
      "Notifications"
      "Click here to see your notifications and activity feed."
      Left
  
  , mkHotspot "profile"
      (ByTestId (mkTestId "profile-avatar"))
      "Your Profile"
      "Access your settings, preferences, and account options here."
      Left
  
  , mkHotspot "help"
      (ByTestId (mkTestId "help-button"))
      "Need Help?"
      "Click here for documentation, tutorials, and support options."
      Top
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                          // example 5: accessibility-first tour
-- ═══════════════════════════════════════════════════════════════════════════════

{-|
  EXAMPLE 5: ACCESSIBILITY-FIRST TOUR
  
  A tour designed with accessibility as the primary concern:
  - Proper ARIA announcements
  - Focus management
  - Screen reader friendly content
  - Keyboard navigation
  - Reduced motion support
  - High contrast support
  
  USAGE:
  
  ```purescript
  -- The tour automatically handles:
  -- 1. Focus trapping within tooltip
  -- 2. Screen reader announcements on step change
  -- 3. Escape key dismissal
  -- 4. Arrow key navigation
  
  -- For reduced motion users, CSS handles it:
  -- @media (prefers-reduced-motion: reduce) {
  --   [data-tour-spotlight],
  --   [data-tour-tooltip] {
  --     transition: none !important;
  --     animation: none !important;
  --   }
  -- }
  ```
  
  EXPECTED BEHAVIOR:
  
  1. Focus moves to tooltip when step opens
  2. Screen reader announces step title and content
  3. Tab cycles through tooltip buttons only
  4. Escape closes tour, focus returns to trigger
  5. Progress announced ("Step 2 of 5")
-}

-- | Type alias for accessible tour messages
type AccessibleTourMsg = Unit

-- | Render the accessibility-first tour
accessibleTour :: forall w. TourState AccessibleTourMsg -> HH.HTML w (TourMsg AccessibleTourMsg)
accessibleTour = tour

-- | Step definitions optimized for accessibility
accessibleTourSteps :: Array (Step AccessibleTourMsg)
accessibleTourSteps =
  [ -- Step 1: Welcome with clear context
    step (mkStepId "a11y-welcome")
      [ target NoTarget
      , title "Welcome to Our Accessible App"
      , body "This guided tour will help you learn the interface. Use Tab to navigate buttons, Enter to activate, and Escape to close at any time."
      , noArrow
      , buttons
          [ nextButton "Begin Tour"
          , skipButton "Skip Tour"
          ]
      ]
  
  -- Step 2: Navigation landmark
  , step (mkStepId "a11y-nav")
      [ target (ByRole RoleNavigation Nothing)
      , title "Main Navigation"
      , body "This navigation region contains links to all main sections. Use arrow keys to move between items when focused."
      , placement Right Center
      , buttons
          [ prevButton "Previous"
          , nextButton "Next"
          ]
      ]
  
  -- Step 3: Search with clear instructions
  , step (mkStepId "a11y-search")
      [ target (ByRole RoleTextbox (Just "Search"))
      , title "Search Feature"
      , body "Type your search terms here. Results update as you type. Press Enter to see all results, or use arrow keys to select from suggestions."
      , placement Bottom Start
      , buttons
          [ prevButton "Previous"
          , nextButton "Next"
          ]
      ]
  
  -- Step 4: Interactive element
  , step (mkStepId "a11y-button")
      [ target (ByRole RoleButton (Just "Create new item"))
      , title "Create Button"
      , body "Press Enter or Space on this button to create a new item. A dialog will open where you can enter details."
      , placement Top Center
      , buttons
          [ prevButton "Previous"
          , nextButton "Next"
          ]
      ]
  
  -- Step 5: Completion with next steps
  , step (mkStepId "a11y-complete")
      [ target NoTarget
      , title "Tour Complete"
      , body "You've completed the tour! Focus will return to the main content. Press the question mark key at any time to see keyboard shortcuts."
      , noArrow
      , buttons
          [ prevButton "Review Tour"
          , completeButton "Finish"
          ]
      ]
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // wiring helpers
-- ═══════════════════════════════════════════════════════════════════════════════

{-|
  WIRING HELPERS
  
  Convenience functions for integrating tours into your app.
  These handle the common patterns of:
  - Initializing tour state
  - Processing update results
  - Executing commands
-}

-- | Complete wiring for a tour
type TourWiring msg =
  { tourId :: TourId
  , steps :: Array (Step msg)
  , initialState :: TourState msg
  }

-- | Create a wired tour
wireTour :: forall msg. String -> Array (Step msg) -> TourWiring msg
wireTour id stepsArray =
  let tourId' = mkTourId id
  in
    { tourId: tourId'
    , steps: stepsArray
    , initialState: initTour tourId' stepsArray
    }

-- | Handle tour commands (example implementation)
-- |
-- | In a real app, you'd implement these effects:
-- | - `ScrollToStep`: Use scrollIntoView on target element
-- | - `ResolveTarget`: Query DOM for target element
-- | - `PersistCompletion`: Save to localStorage
-- | - `EmitAnalytics`: Send to analytics service
-- | - `FocusStep`: Focus the tooltip element
handleTourCmd :: forall msg. TourCmd msg -> Effect Unit
handleTourCmd = case _ of
  ScrollToStep idx -> 
    log ("Scrolling to step " <> show idx)
  
  ResolveTarget idx -> 
    log ("Resolving target for step " <> show idx)
  
  PersistCompletion -> 
    log "Persisting tour completion to localStorage"
  
  PersistDismissal -> 
    log "Persisting tour dismissal to localStorage"
  
  PersistSnooze ms -> 
    log ("Snoozing tour for " <> show ms <> "ms")
  
  EmitAnalytics _event -> 
    log "Analytics event emitted"
  
  FocusStep idx -> 
    log ("Focusing step " <> show idx <> " tooltip")
  
  RestoreFocus -> 
    log "Restoring focus to previous element"
  
  ScheduleResume ms -> 
    log ("Scheduling tour resume in " <> show ms <> "ms")
