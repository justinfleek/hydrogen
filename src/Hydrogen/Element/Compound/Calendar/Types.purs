-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // compound // calendar // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar Types — Core type definitions for the Calendar compound.
-- |
-- | This module defines the fundamental types used throughout the Calendar
-- | component: dates, ranges, selection modes, locales, and grid structures.

module Hydrogen.Element.Compound.Calendar.Types
  ( -- * Date Types
    CalendarDate
  , DateRange
  
  -- * Selection Mode
  , SelectionMode(Single, Range, Multiple)
  
  -- * Week Configuration
  , WeekStart(Sunday, Monday)
  , weekStartIndex
  
  -- * Locale
  , Locale(EnUS, EnGB, De, Fr, Es, Ja, Zh)
  
  -- * Grid Types
  , MonthDay(DayEmpty, DayDate)
  , MonthWeek
  , MonthGrid
  ) where

import Prelude
  ( class Eq
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // date types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A date represented as year, month (1-12), and day
type CalendarDate =
  { year :: Int
  , month :: Int  -- 1-indexed: 1 = January, 12 = December
  , day :: Int
  }

-- | A date range with start and end dates
type DateRange =
  { start :: CalendarDate
  , end :: CalendarDate
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // selection modes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection mode for the calendar
data SelectionMode
  = Single    -- ^ Select a single date
  | Range     -- ^ Select a date range (start to end)
  | Multiple  -- ^ Select multiple individual dates

derive instance eqSelectionMode :: Eq SelectionMode

instance showSelectionMode :: Show SelectionMode where
  show Single = "Single"
  show Range = "Range"
  show Multiple = "Multiple"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // week configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Which day the week starts on
data WeekStart
  = Sunday
  | Monday

derive instance eqWeekStart :: Eq WeekStart

instance showWeekStart :: Show WeekStart where
  show Sunday = "Sunday"
  show Monday = "Monday"

-- | Convert WeekStart to day index (0 = Sunday)
weekStartIndex :: WeekStart -> Int
weekStartIndex Sunday = 0
weekStartIndex Monday = 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // locales
-- ═════════════════════════════════════════════════════════════════════════════

-- | Locale for date formatting
data Locale
  = EnUS   -- English (United States)
  | EnGB   -- English (United Kingdom)
  | De     -- German
  | Fr     -- French
  | Es     -- Spanish
  | Ja     -- Japanese
  | Zh     -- Chinese

derive instance eqLocale :: Eq Locale

instance showLocale :: Show Locale where
  show EnUS = "en-US"
  show EnGB = "en-GB"
  show De = "de"
  show Fr = "fr"
  show Es = "es"
  show Ja = "ja"
  show Zh = "zh"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // grid types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A day cell in the month grid
data MonthDay
  = DayEmpty                           -- Empty cell (padding)
  | DayDate CalendarDate               -- A date cell

derive instance eqMonthDay :: Eq MonthDay

-- | A week row in the month grid
type MonthWeek =
  { weekNumber :: Int
  , days :: Array MonthDay
  }

-- | The complete month grid
type MonthGrid =
  { year :: Int
  , month :: Int
  , weeks :: Array MonthWeek
  }
