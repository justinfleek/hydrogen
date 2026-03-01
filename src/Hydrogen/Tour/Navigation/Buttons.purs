-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // tour // navigation // buttons
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Button Configuration and Builders for Tour Navigation
-- |
-- | This module provides button types and builders:
-- | - Button styles (primary, secondary, ghost, destructive, outline)
-- | - Button sizes and positions
-- | - Standard buttons (next, prev, skip, complete)
-- | - Navigation button layouts
module Hydrogen.Tour.Navigation.Buttons
  ( -- * Button Configuration
    ButtonConfig
  , ButtonStyle(ButtonPrimary, ButtonSecondary, ButtonGhost, ButtonDestructive, ButtonOutline)
  , ButtonSize(ButtonSmall, ButtonMedium, ButtonLarge)
  , ButtonPosition(PositionStart, PositionCenter, PositionEnd)
  , ButtonIcon(IconArrowLeft, IconArrowRight, IconCheck, IconX, IconSkip, IconCustom)
  , defaultButtonConfig
    -- * Button Builders
  , nextButton
  , prevButton
  , skipButton
  , completeButton
  , customButton
    -- * Navigation Buttons
  , NavigationButtonsConfig
  , ButtonLayout(LayoutSpaceBetween, LayoutEnd, LayoutStacked)
  , NavigationElement
  , navigationButtons
  ) where

import Prelude (class Eq, class Show, (<>))

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // button configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button configuration
type ButtonConfig msg =
  { label :: String
  , action :: msg
  , style :: ButtonStyle
  , size :: ButtonSize
  , disabled :: Boolean
  , icon :: Maybe ButtonIcon
  , position :: ButtonPosition
  }

-- | Button visual style
data ButtonStyle
  = ButtonPrimary
    -- ^ Primary action (Next, Continue)
  | ButtonSecondary
    -- ^ Secondary action (Previous)
  | ButtonGhost
    -- ^ Ghost/text button (Skip)
  | ButtonDestructive
    -- ^ Warning action (Leave tour)
  | ButtonOutline
    -- ^ Outlined button

derive instance eqButtonStyle :: Eq ButtonStyle
derive instance genericButtonStyle :: Generic ButtonStyle _

instance showButtonStyle :: Show ButtonStyle where
  show = genericShow

-- | Button size
data ButtonSize
  = ButtonSmall
  | ButtonMedium
  | ButtonLarge

derive instance eqButtonSize :: Eq ButtonSize
derive instance genericButtonSize :: Generic ButtonSize _

instance showButtonSize :: Show ButtonSize where
  show = genericShow

-- | Button position in layout
data ButtonPosition
  = PositionStart
  | PositionCenter
  | PositionEnd

derive instance eqButtonPosition :: Eq ButtonPosition
derive instance genericButtonPosition :: Generic ButtonPosition _

instance showButtonPosition :: Show ButtonPosition where
  show = genericShow

-- | Button icon
data ButtonIcon
  = IconArrowLeft
  | IconArrowRight
  | IconCheck
  | IconX
  | IconSkip
  | IconCustom String

derive instance eqButtonIcon :: Eq ButtonIcon
derive instance genericButtonIcon :: Generic ButtonIcon _

instance showButtonIcon :: Show ButtonIcon where
  show = genericShow

-- | Default button configuration
defaultButtonConfig :: forall msg. String -> msg -> ButtonConfig msg
defaultButtonConfig label action =
  { label
  , action
  , style: ButtonPrimary
  , size: ButtonMedium
  , disabled: false
  , icon: Nothing
  , position: PositionEnd
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // button builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create next button
nextButton :: forall msg. String -> msg -> ButtonConfig msg
nextButton label action = (defaultButtonConfig label action)
  { style = ButtonPrimary
  , icon = Just IconArrowRight
  , position = PositionEnd
  }

-- | Create previous button
prevButton :: forall msg. String -> msg -> ButtonConfig msg
prevButton label action = (defaultButtonConfig label action)
  { style = ButtonSecondary
  , icon = Just IconArrowLeft
  , position = PositionStart
  }

-- | Create skip button
skipButton :: forall msg. String -> msg -> ButtonConfig msg
skipButton label action = (defaultButtonConfig label action)
  { style = ButtonGhost
  , icon = Just IconSkip
  , position = PositionStart
  }

-- | Create complete button
completeButton :: forall msg. String -> msg -> ButtonConfig msg
completeButton label action = (defaultButtonConfig label action)
  { style = ButtonPrimary
  , icon = Just IconCheck
  , position = PositionEnd
  }

-- | Create custom button
customButton :: forall msg. String -> msg -> ButtonStyle -> ButtonConfig msg
customButton label action style = (defaultButtonConfig label action) { style = style }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // navigation layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Navigation buttons configuration
type NavigationButtonsConfig msg =
  { showPrev :: Boolean
  , showNext :: Boolean
  , showSkip :: Boolean
  , prevConfig :: Maybe (ButtonConfig msg)
  , nextConfig :: Maybe (ButtonConfig msg)
  , skipConfig :: Maybe (ButtonConfig msg)
  , completeConfig :: Maybe (ButtonConfig msg)
  , layout :: ButtonLayout
  }

-- | Button layout
data ButtonLayout
  = LayoutSpaceBetween
    -- ^ Spread across width
  | LayoutEnd
    -- ^ Aligned to end
  | LayoutStacked
    -- ^ Vertical stack

derive instance eqButtonLayout :: Eq ButtonLayout
derive instance genericButtonLayout :: Generic ButtonLayout _

instance showButtonLayout :: Show ButtonLayout where
  show = genericShow

-- | Build navigation buttons element description
navigationButtons :: forall msg. NavigationButtonsConfig msg -> NavigationElement msg
navigationButtons cfg =
  { buttons: buildButtons cfg
  , layout: cfg.layout
  }

-- | Build button array from config
buildButtons :: forall msg. NavigationButtonsConfig msg -> Array (ButtonConfig msg)
buildButtons cfg =
  (if cfg.showSkip then maybeToArray cfg.skipConfig else []) <>
  (if cfg.showPrev then maybeToArray cfg.prevConfig else []) <>
  (if cfg.showNext then maybeToArray cfg.nextConfig else maybeToArray cfg.completeConfig)
  where
  maybeToArray :: forall a. Maybe a -> Array a
  maybeToArray = case _ of
    Just a -> [a]
    Nothing -> []

-- | Element description for navigation
type NavigationElement msg =
  { buttons :: Array (ButtonConfig msg)
  , layout :: ButtonLayout
  }
