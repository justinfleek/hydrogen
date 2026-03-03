-- | Surgical JSON extraction for Hydrogen Scraper
-- |
-- | Port of Slide.Parse pattern to PureScript.
-- |
-- | Instead of parsing full JSON with Argonaut, we surgically extract
-- | just the fields we need. This avoids parsing 650 bytes of garbage
-- | per element when we only need a few values.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | let json = """{"backgroundColor":{"l":0.5,"c":0.1,"h":180,"a":1},...}"""
-- | case extractColor "backgroundColor" json of
-- |   Just color -> -- OKLCH { l: 0.5, c: 0.1, h: 180.0, a: 1.0 }
-- |   Nothing -> -- field not found or null
-- | ```

module Hydrogen.Scraper.Wire.Parse
  ( -- * Color extraction
    extractColor
  , extractMaybeColor
  
  -- * Number extraction
  , extractNumber
  , extractMaybeNumber
  , extractInt
  
  -- * String extraction
  , extractString
  , extractMaybeString
  
  -- * Boolean extraction
  , extractBoolean
  
  -- * Object extraction
  , extractObject
  
  -- * Array extraction
  , extractArray
  , extractArrayElements
  , iterateArray
  
  -- * Transform extraction
  , extractTransform
  
  -- * Shadow extraction
  , extractShadow
  
  -- * Bounding box extraction
  , extractBoundingBox
  
  -- * Low-level
  , findField
  , parseJSONString
  , parseJSONNumber
  
  -- * Types (re-exported for consumers)
  , ExtractedColor
  , ExtractedTransform
  , ExtractedShadow
  , ExtractedBoundingBox
  ) where

import Prelude
  ( class Eq
  , Unit
  , bind
  , discard
  , otherwise
  , pure
  , unit
  , ($)
  , (&&)
  , (+)
  , (-)
  , (<>)
  , (==)
  , (>=)
  , (>)
  , (||)
  , (/=)
  , (<=)
  , (>>>)
  )

import Data.Array (head, snoc, tail) as Array
import Data.Enum (fromEnum, toEnum) as Enum
import Data.Int (floor, fromStringAs, hexadecimal) as Int
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Number (fromString) as Number
import Data.String (Pattern(Pattern), drop, indexOf, length, null, take, takeWhile) as String
import Data.String.CodeUnits (charAt, singleton) as CU
import Data.String.CodePoints (CodePoint, singleton) as CP

-- | Extracted OKLCH color
type ExtractedColor =
  { l :: Number
  , c :: Number
  , h :: Number
  , a :: Number
  }

-- | Extracted transform matrix
type ExtractedTransform =
  { a :: Number, b :: Number
  , c :: Number, d :: Number
  , e :: Number, f :: Number
  , is3D :: Boolean
  }

-- | Extracted shadow
type ExtractedShadow =
  { inset :: Boolean
  , offsetX :: Number
  , offsetY :: Number
  , blurRadius :: Number
  , spreadRadius :: Number
  , color :: Maybe ExtractedColor
  }

-- | Extracted bounding box
type ExtractedBoundingBox =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- | Extract a color field as OKLCH
-- |
-- | Looks for: `"fieldName":{"l":...,"c":...,"h":...,"a":...}`
extractColor :: String -> String -> Maybe ExtractedColor
extractColor fieldName json = do
  objStr <- findField fieldName json
  -- Check for null
  if String.take 4 objStr == "null" then Nothing
  else do
    l <- extractNumber "l" objStr
    c <- extractNumber "c" objStr
    h <- extractNumber "h" objStr
    a <- extractNumber "a" objStr
    Just { l, c, h, a }

-- | Extract a maybe-color field (returns Nothing for null)
extractMaybeColor :: String -> String -> Maybe (Maybe ExtractedColor)
extractMaybeColor fieldName json = case findField fieldName json of
  Nothing -> Just Nothing  -- field not present
  Just objStr -> 
    if String.take 4 objStr == "null" then Just Nothing
    else case extractColor fieldName json of
      Just color -> Just (Just color)
      Nothing -> Nothing  -- parse error

-- | Extract a number field
extractNumber :: String -> String -> Maybe Number
extractNumber fieldName json = do
  valueStr <- findField fieldName json
  parseJSONNumber valueStr

-- | Extract a maybe-number field
extractMaybeNumber :: String -> String -> Maybe (Maybe Number)
extractMaybeNumber fieldName json = case findField fieldName json of
  Nothing -> Just Nothing
  Just valueStr ->
    if String.take 4 valueStr == "null" then Just Nothing
    else case parseJSONNumber valueStr of
      Just n -> Just (Just n)
      Nothing -> Nothing

-- | Extract an integer field
extractInt :: String -> String -> Maybe Int
extractInt fieldName json = do
  n <- extractNumber fieldName json
  Just (Int.floor n)

-- | Extract a string field
extractString :: String -> String -> Maybe String
extractString fieldName json = do
  valueStr <- findField fieldName json
  parseJSONString valueStr

-- | Extract a maybe-string field
extractMaybeString :: String -> String -> Maybe (Maybe String)
extractMaybeString fieldName json = case findField fieldName json of
  Nothing -> Just Nothing
  Just valueStr ->
    if String.take 4 valueStr == "null" then Just Nothing
    else case parseJSONString valueStr of
      Just s -> Just (Just s)
      Nothing -> Nothing

-- | Extract a boolean field
extractBoolean :: String -> String -> Maybe Boolean
extractBoolean fieldName json = do
  valueStr <- findField fieldName json
  case String.take 4 valueStr of
    "true" -> Just true
    "fals" -> Just false  -- "false"
    _ -> Nothing

-- | Extract a nested object as raw JSON string
extractObject :: String -> String -> Maybe String
extractObject fieldName json = do
  valueStr <- findField fieldName json
  if CU.charAt 0 valueStr == Just '{' then
    Just (extractBalancedBraces valueStr)
  else Nothing

-- | Extract an array as raw JSON string  
extractArray :: String -> String -> Maybe String
extractArray fieldName json = do
  valueStr <- findField fieldName json
  if CU.charAt 0 valueStr == Just '[' then
    Just (extractBalancedBrackets valueStr)
  else Nothing

-- | Extract array and split into individual element JSON strings
-- |
-- | Given: `[{"a":1},{"a":2},{"a":3}]`
-- | Returns: `["{\"a\":1}", "{\"a\":2}", "{\"a\":3}"]`
extractArrayElements :: String -> Array String
extractArrayElements arrJson = 
  if CU.charAt 0 arrJson /= Just '[' then []
  else splitArrayElements (String.drop 1 arrJson) []

-- | Split array elements by iterating through balanced JSON
splitArrayElements :: String -> Array String -> Array String
splitArrayElements remaining acc =
  let trimmed = dropWhitespace remaining
  in case CU.charAt 0 trimmed of
       Nothing -> acc
       Just ']' -> acc  -- end of array
       Just ',' -> splitArrayElements (String.drop 1 trimmed) acc  -- skip comma
       Just '{' -> 
         let element = extractBalancedBraces trimmed
             rest = String.drop (String.length element) trimmed
         in splitArrayElements rest (Array.snoc acc element)
       Just '[' ->
         let element = extractBalancedBrackets trimmed
             rest = String.drop (String.length element) trimmed
         in splitArrayElements rest (Array.snoc acc element)
       Just '"' ->
         let element = extractQuotedString trimmed
             rest = String.drop (String.length element) trimmed
         in splitArrayElements rest (Array.snoc acc element)
       _ ->
         -- Primitive value (number, boolean, null)
         let element = String.takeWhile isPrimitiveChar trimmed
             rest = String.drop (String.length element) trimmed
         in splitArrayElements rest (Array.snoc acc element)

-- | Check if character is part of a primitive value
isPrimitiveChar :: CP.CodePoint -> Boolean
isPrimitiveChar cp =
  let c = Enum.fromEnum cp
  in (c >= 48 && c <= 57)   -- '0'-'9'
     || (c >= 97 && c <= 122)  -- 'a'-'z' (true, false, null)
     || c == 45             -- '-'
     || c == 46             -- '.'
     || c == 43             -- '+'
     || c == 101            -- 'e'
     || c == 69             -- 'E'

-- | Iterate over array elements applying a parser to each
-- |
-- | ```purescript
-- | let parsed = iterateArray extractElement "[{...},{...}]"
-- | ```
iterateArray :: forall a. (String -> Maybe a) -> String -> Array a
iterateArray parser arrJson =
  let elements = extractArrayElements arrJson
  in collectJust parser elements []

-- | Collect Just values from parsing
collectJust :: forall a. (String -> Maybe a) -> Array String -> Array a -> Array a
collectJust parser elements acc =
  case arrayHead elements of
    Nothing -> acc
    Just element ->
      case parser element of
        Just parsed -> collectJust parser (arrayTail elements) (Array.snoc acc parsed)
        Nothing -> collectJust parser (arrayTail elements) acc

-- | Get first element of array (safe)
arrayHead :: forall a. Array a -> Maybe a
arrayHead = Array.head

-- | Get tail of array (safe, returns empty array if input is empty)
arrayTail :: forall a. Array a -> Array a
arrayTail arr = fromMaybe [] (Array.tail arr)

-- | Drop leading whitespace
dropWhitespace :: String -> String
dropWhitespace = String.takeWhile isWhitespace >>> dropPrefix
  where
    dropPrefix :: String -> String
    dropPrefix s = 
      let ws = String.takeWhile isWhitespace s
      in String.drop (String.length ws) s

-- | Extract a transform matrix
extractTransform :: String -> String -> Maybe ExtractedTransform
extractTransform fieldName json = do
  objStr <- findField fieldName json
  if String.take 4 objStr == "null" then Nothing
  else do
    a <- extractNumber "a" objStr
    b <- extractNumber "b" objStr
    c <- extractNumber "c" objStr
    d <- extractNumber "d" objStr
    e <- extractNumber "e" objStr
    f <- extractNumber "f" objStr
    let is3D = case extractBoolean "is3D" objStr of
                 Just b' -> b'
                 Nothing -> false
    Just { a, b, c, d, e, f, is3D }

-- | Extract a shadow
extractShadow :: String -> String -> Maybe ExtractedShadow
extractShadow fieldName json = do
  objStr <- findField fieldName json
  if String.take 4 objStr == "null" then Nothing
  else do
    inset <- case extractBoolean "inset" objStr of
               Just b -> Just b
               Nothing -> Just false
    offsetX <- extractNumber "offsetX" objStr
    offsetY <- extractNumber "offsetY" objStr
    blurRadius <- extractNumber "blurRadius" objStr
    spreadRadius <- extractNumber "spreadRadius" objStr
    let color = extractColor "color" objStr
    Just { inset, offsetX, offsetY, blurRadius, spreadRadius, color }

-- | Extract a bounding box
extractBoundingBox :: String -> String -> Maybe ExtractedBoundingBox
extractBoundingBox fieldName json = do
  objStr <- findField fieldName json
  if String.take 4 objStr == "null" then Nothing
  else do
    x <- extractNumber "x" objStr
    y <- extractNumber "y" objStr
    width <- extractNumber "width" objStr
    height <- extractNumber "height" objStr
    Just { x, y, width, height }

-- | Find a field in JSON and return the value portion
-- |
-- | Searches for `"fieldName":` and returns everything after the colon
-- | until the value ends (comma, closing brace, or end of string)
findField :: String -> String -> Maybe String
findField fieldName json =
  let pattern = "\"" <> fieldName <> "\":"
      patternLen = String.length pattern
  in case String.indexOf (String.Pattern pattern) json of
       Nothing -> Nothing
       Just idx ->
         let afterColon = String.drop (idx + patternLen) json
             trimmed = String.takeWhile isWhitespace afterColon
             result = String.drop (String.length trimmed) afterColon
         in Just result

-- | Check if a code point is whitespace
isWhitespace :: CP.CodePoint -> Boolean
isWhitespace cp =
  let c = Enum.fromEnum cp
  in c == 32 || c == 10 || c == 13 || c == 9  -- space, newline, carriage return, tab

-- | Parse a JSON string value (handles escapes)
parseJSONString :: String -> Maybe String
parseJSONString str =
  if CU.charAt 0 str /= Just '"' then Nothing
  else parseStringContents (String.drop 1 str) ""

parseStringContents :: String -> String -> Maybe String
parseStringContents remaining acc =
  case CU.charAt 0 remaining of
    Nothing -> Nothing  -- unterminated string
    Just '"' -> Just acc
    Just '\\' -> case CU.charAt 1 remaining of
      Just 'n' -> parseStringContents (String.drop 2 remaining) (acc <> "\n")
      Just 'r' -> parseStringContents (String.drop 2 remaining) (acc <> "\r")
      Just 't' -> parseStringContents (String.drop 2 remaining) (acc <> "\t")
      Just '"' -> parseStringContents (String.drop 2 remaining) (acc <> "\"")
      Just '\\' -> parseStringContents (String.drop 2 remaining) (acc <> "\\")
      Just '/' -> parseStringContents (String.drop 2 remaining) (acc <> "/")
      Just 'u' -> -- Unicode escape \uXXXX - convert to actual character
        let hex = String.take 4 (String.drop 2 remaining)
            codePoint = hexToInt hex
            char = fromCodePoint codePoint
        in parseStringContents (String.drop 6 remaining) (acc <> char)
      _ -> Nothing
    Just c -> parseStringContents (String.drop 1 remaining) (acc <> CU.singleton c)

-- | Convert hex string to int (returns 0 for invalid input)
hexToInt :: String -> Int
hexToInt hex = fromMaybe 0 (Int.fromStringAs Int.hexadecimal hex)

-- | Convert code point to string
fromCodePoint :: Int -> String
fromCodePoint n = case Enum.toEnum n of
  Just (cp :: CP.CodePoint) -> CP.singleton cp
  Nothing -> ""

-- | Parse a JSON number
parseJSONNumber :: String -> Maybe Number
parseJSONNumber str =
  let numChars = String.takeWhile isNumCodePoint str
  in if String.null numChars then Nothing
     else Number.fromString numChars

-- | Check if a code point is a valid number character
isNumCodePoint :: CP.CodePoint -> Boolean
isNumCodePoint cp = 
  let c = Enum.fromEnum cp
  in (c >= 48 && c <= 57)  -- '0'-'9'
     || c == 46            -- '.'
     || c == 45            -- '-'
     || c == 43            -- '+'
     || c == 101           -- 'e'
     || c == 69            -- 'E'

-- | Extract balanced braces { }
extractBalancedBraces :: String -> String
extractBalancedBraces = extractBalanced '{' '}'

-- | Extract balanced brackets [ ]
extractBalancedBrackets :: String -> String
extractBalancedBrackets = extractBalanced '[' ']'

-- | Extract balanced delimiters
extractBalanced :: Char -> Char -> String -> String
extractBalanced open close str = go str 0 ""
  where
    go :: String -> Int -> String -> String
    go remaining depth acc =
      case CU.charAt 0 remaining of
        Nothing -> acc
        Just c
          | c == open -> go (String.drop 1 remaining) (depth + 1) (acc <> CU.singleton c)
          | c == close -> 
              if depth <= 1 then acc <> CU.singleton c
              else go (String.drop 1 remaining) (depth - 1) (acc <> CU.singleton c)
          | c == '"' -> 
              let quoted = extractQuotedString remaining
                  rest = String.drop (String.length quoted) remaining
              in go rest depth (acc <> quoted)
          | otherwise -> go (String.drop 1 remaining) depth (acc <> CU.singleton c)

-- | Extract a quoted string including quotes
extractQuotedString :: String -> String
extractQuotedString str =
  if CU.charAt 0 str /= Just '"' then ""
  else goQuote (String.drop 1 str) "\""
  where
    goQuote :: String -> String -> String
    goQuote remaining acc =
      case CU.charAt 0 remaining of
        Nothing -> acc
        Just '"' -> acc <> "\""
        Just '\\' -> goQuote (String.drop 2 remaining) (acc <> String.take 2 remaining)
        Just c -> goQuote (String.drop 1 remaining) (acc <> CU.singleton c)
