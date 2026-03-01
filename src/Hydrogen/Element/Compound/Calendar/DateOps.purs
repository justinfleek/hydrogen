-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // calendar // dateops
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar Date Operations — Pure Gregorian calendar arithmetic.
-- |
-- | This module provides all date manipulation functions needed by the
-- | Calendar component. Pure PureScript. No FFI. No JavaScript Date objects.

module Hydrogen.Element.Compound.Calendar.DateOps
  ( -- * Leap Year
    isLeapYear
  
  -- * Days in Month
  , getDaysInMonth
  
  -- * Day of Week
  , dayOfWeek
  , getFirstDayOfMonth
  
  -- * Date Comparison
  , compareDates
  , sameDate
  
  -- * Date Arithmetic
  , addDays
  , addMonths
  
  -- * Week Numbers
  , getWeekNumber
  
  -- * Internal (exported for testing)
  , dayOfYear
  , daysInYear
  , daysBetween
  ) where

import Prelude
  ( negate
  , otherwise
  , (+)
  , (-)
  , (<)
  , (==)
  , (/=)
  , (>)
  , (/)
  , (*)
  , (&&)
  , (||)
  )

import Data.Int (rem)

import Hydrogen.Element.Compound.Calendar.Types (CalendarDate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // leap year
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a year is a leap year
isLeapYear :: Int -> Boolean
isLeapYear year =
  (year `rem` 4 == 0 && year `rem` 100 /= 0) || year `rem` 400 == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // days in month
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get number of days in a month (1-indexed)
getDaysInMonth :: Int -> Int -> Int
getDaysInMonth year month = case month of
  1 -> 31
  2 -> if isLeapYear year then 29 else 28
  3 -> 31
  4 -> 30
  5 -> 31
  6 -> 30
  7 -> 31
  8 -> 31
  9 -> 30
  10 -> 31
  11 -> 30
  12 -> 31
  _ -> 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // day of week
-- ═════════════════════════════════════════════════════════════════════════════

-- | Day of week using Zeller's congruence (0 = Sunday, 6 = Saturday)
-- |
-- | Zeller's formula for Gregorian calendar:
-- |   h = (q + floor(13(m+1)/5) + K + floor(K/4) + floor(J/4) - 2J) mod 7
-- |
-- | January/February treated as months 13/14 of previous year.
dayOfWeek :: CalendarDate -> Int
dayOfWeek date =
  let
    adjustedYear = if date.month < 3 then date.year - 1 else date.year
    adjustedMonth = if date.month < 3 then date.month + 12 else date.month
    
    q = date.day
    m = adjustedMonth
    k = adjustedYear `rem` 100
    j = adjustedYear / 100
    
    h = (q + (13 * (m + 1)) / 5 + k + k / 4 + j / 4 - 2 * j) `rem` 7
    
    -- Zeller: 0=Saturday, 1=Sunday. Convert to 0=Sunday.
    dow = (h + 6) `rem` 7
  in
    if dow < 0 then dow + 7 else dow

-- | Get day of week for first day of month (0 = Sunday)
getFirstDayOfMonth :: Int -> Int -> Int
getFirstDayOfMonth year month = dayOfWeek { year, month, day: 1 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // date comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare two dates: -1 (a < b), 0 (equal), 1 (a > b)
compareDates :: CalendarDate -> CalendarDate -> Int
compareDates a b
  | a.year < b.year = -1
  | a.year > b.year = 1
  | a.month < b.month = -1
  | a.month > b.month = 1
  | a.day < b.day = -1
  | a.day > b.day = 1
  | otherwise = 0

-- | Check if two dates are the same
sameDate :: CalendarDate -> CalendarDate -> Boolean
sameDate a b = a.year == b.year && a.month == b.month && a.day == b.day

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // date arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add days to a date (handles month/year overflow)
addDays :: CalendarDate -> Int -> CalendarDate
addDays date n
  | n == 0 = date
  | n > 0 = addDaysPositive date n
  | otherwise = addDaysNegative date (negate n)

-- | Add positive number of days
addDaysPositive :: CalendarDate -> Int -> CalendarDate
addDaysPositive date n =
  let
    daysInCurrentMonth = getDaysInMonth date.year date.month
    daysRemaining = daysInCurrentMonth - date.day
  in
    if n < daysRemaining + 1
      then date { day = date.day + n }
      else
        let
          nextMonth = if date.month == 12 then 1 else date.month + 1
          nextYear = if date.month == 12 then date.year + 1 else date.year
          nextDate = { year: nextYear, month: nextMonth, day: 1 }
          remaining = n - daysRemaining - 1
        in
          addDaysPositive nextDate remaining

-- | Subtract positive number of days
addDaysNegative :: CalendarDate -> Int -> CalendarDate
addDaysNegative date n =
  if n < date.day
    then date { day = date.day - n }
    else
      let
        prevMonth = if date.month == 1 then 12 else date.month - 1
        prevYear = if date.month == 1 then date.year - 1 else date.year
        daysInPrevMonth = getDaysInMonth prevYear prevMonth
        prevDate = { year: prevYear, month: prevMonth, day: daysInPrevMonth }
        remaining = n - date.day
      in
        addDaysNegative prevDate remaining

-- | Add months to a date (clamps day to valid range)
addMonths :: CalendarDate -> Int -> CalendarDate
addMonths date n =
  let
    totalMonths = date.year * 12 + (date.month - 1) + n
    newYear = totalMonths / 12
    newMonth = (totalMonths `rem` 12) + 1
    adjustedMonth = if newMonth < 1 then newMonth + 12 else newMonth
    adjustedYear = if newMonth < 1 then newYear - 1 else newYear
    maxDay = getDaysInMonth adjustedYear adjustedMonth
    newDay = if date.day > maxDay then maxDay else date.day
  in
    { year: adjustedYear, month: adjustedMonth, day: newDay }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // week numbers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get ISO 8601 week number (1-53)
-- |
-- | Week 1 contains the first Thursday of the year. Weeks start Monday.
getWeekNumber :: CalendarDate -> Int
getWeekNumber date =
  let
    dow = dayOfWeek date
    daysToThursday = (4 - dow + 7) `rem` 7
    thursday = addDays date daysToThursday
    jan1 = { year: thursday.year, month: 1, day: 1 }
    daysSinceJan1 = daysBetween jan1 thursday
  in
    daysSinceJan1 / 7 + 1

-- | Days between two dates (assumes b >= a)
daysBetween :: CalendarDate -> CalendarDate -> Int
daysBetween a b =
  let
    doyA = dayOfYear a
    doyB = dayOfYear b
  in
    if a.year == b.year
      then doyB - doyA
      else
        let
          daysRemainingInYearA = daysInYear a.year - doyA
          fullYears = countDaysInYears (a.year + 1) (b.year - 1)
        in
          daysRemainingInYearA + fullYears + doyB

-- | Day of year (1-365 or 1-366)
dayOfYear :: CalendarDate -> Int
dayOfYear date = go 1 0
  where
  go :: Int -> Int -> Int
  go m acc
    | m == date.month = acc + date.day
    | otherwise = go (m + 1) (acc + getDaysInMonth date.year m)

-- | Total days in a year
daysInYear :: Int -> Int
daysInYear year = if isLeapYear year then 366 else 365

-- | Sum days in range of years (inclusive)
countDaysInYears :: Int -> Int -> Int
countDaysInYears startYear endYear
  | startYear > endYear = 0
  | otherwise = daysInYear startYear + countDaysInYears (startYear + 1) endYear
