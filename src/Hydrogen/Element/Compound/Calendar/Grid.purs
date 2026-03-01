-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // compound // calendar // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar Grid — Month grid building functions.
-- |
-- | This module builds the MonthGrid data structure that represents
-- | a calendar month as a grid of weeks and days.

module Hydrogen.Element.Compound.Calendar.Grid
  ( -- * Grid Building
    buildMonthGrid
  ) where

import Prelude
  ( otherwise
  , (+)
  , (-)
  , (<)
  , (>)
  , (<>)
  )

import Data.Array (snoc, take, drop)
import Data.Array as Array
import Data.Int (rem)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Element.Compound.Calendar.Types
  ( CalendarDate
  , MonthDay(DayEmpty, DayDate)
  , MonthWeek
  , MonthGrid
  , WeekStart
  , weekStartIndex
  )
import Hydrogen.Element.Compound.Calendar.DateOps
  ( getDaysInMonth
  , getFirstDayOfMonth
  , getWeekNumber
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // grid building
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the month grid for a given year/month
buildMonthGrid :: Int -> Int -> WeekStart -> MonthGrid
buildMonthGrid year month weekStart =
  let
    daysInMonth = getDaysInMonth year month
    firstDayOfWeek = getFirstDayOfMonth year month
    startOffset = weekStartIndex weekStart
    
    -- Adjust first day based on week start
    adjustedFirstDay = (firstDayOfWeek - startOffset + 7) `rem` 7
    
    -- Build all day cells
    allDays = buildDayCells year month daysInMonth adjustedFirstDay
    
    -- Split into weeks
    weeks = splitIntoWeeks allDays year month
  in
    { year, month, weeks }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cell helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build day cells with padding
buildDayCells :: Int -> Int -> Int -> Int -> Array MonthDay
buildDayCells year month daysInMonth offset =
  let
    -- Leading empty cells
    leadingEmpty = buildEmptyCells offset
    
    -- Actual day cells
    dayCells = buildDateCells year month daysInMonth
    
    -- Trailing empty cells to complete last week
    totalCells = offset + daysInMonth
    trailingCount = (7 - (totalCells `rem` 7)) `rem` 7
    trailingEmpty = buildEmptyCells trailingCount
  in
    leadingEmpty <> dayCells <> trailingEmpty

-- | Build empty cells
buildEmptyCells :: Int -> Array MonthDay
buildEmptyCells count = go count []
  where
  go :: Int -> Array MonthDay -> Array MonthDay
  go n acc
    | n < 1 = acc
    | otherwise = go (n - 1) (acc `snoc` DayEmpty)

-- | Build date cells
buildDateCells :: Int -> Int -> Int -> Array MonthDay
buildDateCells year month daysInMonth = go 1 []
  where
  go :: Int -> Array MonthDay -> Array MonthDay
  go day acc
    | day > daysInMonth = acc
    | otherwise = go (day + 1) (acc `snoc` DayDate { year, month, day })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // week helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Split day cells into weeks
splitIntoWeeks :: Array MonthDay -> Int -> Int -> Array MonthWeek
splitIntoWeeks days _year _month = go 0 days []
  where
  go :: Int -> Array MonthDay -> Array MonthWeek -> Array MonthWeek
  go _ [] acc = acc
  go weekIdx remaining acc =
    let
      week = take 7 remaining
      rest = drop 7 remaining
      -- Calculate week number from first non-empty day
      weekNum = case Array.findMap getDateFromDay week of
        Just d -> getWeekNumber d
        Nothing -> weekIdx + 1
    in
      go (weekIdx + 1) rest (acc `snoc` { weekNumber: weekNum, days: week })
  
  getDateFromDay :: MonthDay -> Maybe CalendarDate
  getDateFromDay (DayDate d) = Just d
  getDateFromDay DayEmpty = Nothing
