-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // calendar // locale
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar Locale — Internationalization support for month names.
-- |
-- | This module provides localized month names for supported locales.

module Hydrogen.Element.Compound.Calendar.Locale
  ( -- * Month Names
    monthName
  , monthNameEnUS
  , monthNameDe
  , monthNameFr
  , monthNameEs
  , monthNameJa
  , monthNameZh
  ) where

import Hydrogen.Element.Compound.Calendar.Types
  ( Locale(EnUS, EnGB, De, Fr, Es, Ja, Zh)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // month names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Month name lookup by locale
monthName :: Locale -> Int -> String
monthName locale month = case locale of
  EnUS -> monthNameEnUS month
  EnGB -> monthNameEnUS month  -- Same as US English
  De -> monthNameDe month
  Fr -> monthNameFr month
  Es -> monthNameEs month
  Ja -> monthNameJa month
  Zh -> monthNameZh month

-- | English month names
monthNameEnUS :: Int -> String
monthNameEnUS = case _ of
  1 -> "January"
  2 -> "February"
  3 -> "March"
  4 -> "April"
  5 -> "May"
  6 -> "June"
  7 -> "July"
  8 -> "August"
  9 -> "September"
  10 -> "October"
  11 -> "November"
  12 -> "December"
  _ -> "Unknown"

-- | German month names
monthNameDe :: Int -> String
monthNameDe = case _ of
  1 -> "Januar"
  2 -> "Februar"
  3 -> "März"
  4 -> "April"
  5 -> "Mai"
  6 -> "Juni"
  7 -> "Juli"
  8 -> "August"
  9 -> "September"
  10 -> "Oktober"
  11 -> "November"
  12 -> "Dezember"
  _ -> "Unbekannt"

-- | French month names
monthNameFr :: Int -> String
monthNameFr = case _ of
  1 -> "janvier"
  2 -> "février"
  3 -> "mars"
  4 -> "avril"
  5 -> "mai"
  6 -> "juin"
  7 -> "juillet"
  8 -> "août"
  9 -> "septembre"
  10 -> "octobre"
  11 -> "novembre"
  12 -> "décembre"
  _ -> "inconnu"

-- | Spanish month names
monthNameEs :: Int -> String
monthNameEs = case _ of
  1 -> "enero"
  2 -> "febrero"
  3 -> "marzo"
  4 -> "abril"
  5 -> "mayo"
  6 -> "junio"
  7 -> "julio"
  8 -> "agosto"
  9 -> "septiembre"
  10 -> "octubre"
  11 -> "noviembre"
  12 -> "diciembre"
  _ -> "desconocido"

-- | Japanese month names
monthNameJa :: Int -> String
monthNameJa = case _ of
  1 -> "1月"
  2 -> "2月"
  3 -> "3月"
  4 -> "4月"
  5 -> "5月"
  6 -> "6月"
  7 -> "7月"
  8 -> "8月"
  9 -> "9月"
  10 -> "10月"
  11 -> "11月"
  12 -> "12月"
  _ -> "不明"

-- | Chinese month names
monthNameZh :: Int -> String
monthNameZh = case _ of
  1 -> "一月"
  2 -> "二月"
  3 -> "三月"
  4 -> "四月"
  5 -> "五月"
  6 -> "六月"
  7 -> "七月"
  8 -> "八月"
  9 -> "九月"
  10 -> "十月"
  11 -> "十一月"
  12 -> "十二月"
  _ -> "未知"
