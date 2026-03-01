-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // text // code // document
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Document — Code document type and core operations.
-- |
-- | ## Design Philosophy
-- |
-- | A CodeDocument is the complete representation of a code file:
-- | - Lines of code (each with content and tokens)
-- | - Language for syntax highlighting
-- | - Active cursors (supports multi-cursor editing)
-- |
-- | Documents are immutable. All operations return new documents.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (map)
-- | - Data.Array
-- | - Data.String
-- | - Hydrogen.Schema.Text.Code.Line
-- | - Hydrogen.Schema.Text.Code.Cursor
-- | - Hydrogen.Schema.Text.RichText (Language)
-- | - Hydrogen.Schema.Text.Selection

module Hydrogen.Schema.Text.Code.Document
  ( -- * Document Type
    CodeDocument
  , codeDocument
  , emptyCodeDocument
  , documentContent
  , documentLanguage
  , documentCursors
  , setContent
  , setLanguage
  , setCursors
  
  -- * Line Access
  , documentLines
  , documentLineCount
  , getLine
  , setLine
  
  -- * Line Manipulation
  , insertLine
  , deleteLine
  , splitLine
  , joinLines
  
  -- * Text Operations
  , insertTextAt
  , deleteTextAt
  , replaceTextAt
  , getTextInRange
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , (==)
  , (+)
  , (-)
  , (<>)
  , ($)
  , otherwise
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String
import Data.String.Pattern (Pattern(Pattern))

import Hydrogen.Schema.Text.Code.Line 
  ( CodeLine
  , codeLine
  , lineContent
  )
import Hydrogen.Schema.Text.Code.Cursor (Cursor, cursor)
import Hydrogen.Schema.Text.RichText (Language)
import Hydrogen.Schema.Text.Selection (codePosition)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // code document
-- ═════════════════════════════════════════════════════════════════════════════

-- | A complete code document.
-- |
-- | Documents contain:
-- | - Lines of code
-- | - Language for syntax highlighting
-- | - Active cursors (supports multi-cursor)
type CodeDocument =
  { lines :: Array CodeLine
  , language :: Language
  , cursors :: Array Cursor
  }

-- | Create a code document from content and language.
codeDocument :: String -> Language -> CodeDocument
codeDocument content' lang =
  let
    rawLines = String.split (Pattern "\n") content'
    indexed = Array.mapWithIndex (\i s -> codeLine s i) rawLines
  in
    { lines: indexed
    , language: lang
    , cursors: [ cursor (codePosition 0 0) ]
    }

-- | Create an empty code document.
emptyCodeDocument :: Language -> CodeDocument
emptyCodeDocument lang =
  { lines: [ codeLine "" 0 ]
  , language: lang
  , cursors: [ cursor (codePosition 0 0) ]
  }

-- | Get document content as a single string.
documentContent :: CodeDocument -> String
documentContent doc =
  String.joinWith "\n" (map lineContent doc.lines)

-- | Get document language.
documentLanguage :: CodeDocument -> Language
documentLanguage doc = doc.language

-- | Get document cursors.
documentCursors :: CodeDocument -> Array Cursor
documentCursors doc = doc.cursors

-- | Set document content (replaces all lines).
setContent :: String -> CodeDocument -> CodeDocument
setContent content' doc =
  let
    rawLines = String.split (Pattern "\n") content'
    indexed = Array.mapWithIndex (\i s -> codeLine s i) rawLines
  in
    doc { lines = indexed }

-- | Set document language.
setLanguage :: Language -> CodeDocument -> CodeDocument
setLanguage lang doc = doc { language = lang }

-- | Set document cursors.
setCursors :: Array Cursor -> CodeDocument -> CodeDocument
setCursors cs doc = doc { cursors = cs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // line access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all lines.
documentLines :: CodeDocument -> Array CodeLine
documentLines doc = doc.lines

-- | Get line count.
documentLineCount :: CodeDocument -> Int
documentLineCount doc = Array.length doc.lines

-- | Get a line by index.
getLine :: Int -> CodeDocument -> Maybe CodeLine
getLine idx doc = Array.index doc.lines idx

-- | Set a line by index.
setLine :: Int -> CodeLine -> CodeDocument -> CodeDocument
setLine idx line doc =
  case Array.updateAt idx line doc.lines of
    Just newLines -> doc { lines = newLines }
    Nothing -> doc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // line manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Renumber lines after insertion/deletion.
renumberLines :: Array CodeLine -> Array CodeLine
renumberLines = Array.mapWithIndex (\i l -> l { lineNum = i })

-- | Insert a line at index.
insertLine :: Int -> String -> CodeDocument -> CodeDocument
insertLine idx content' doc =
  let
    newLine = codeLine content' idx
    updatedLines = case Array.insertAt idx newLine doc.lines of
      Just ls -> renumberLines ls
      Nothing -> doc.lines
  in
    doc { lines = updatedLines }

-- | Delete a line by index.
deleteLine :: Int -> CodeDocument -> CodeDocument
deleteLine idx doc =
  let
    updatedLines = case Array.deleteAt idx doc.lines of
      Just ls -> if Array.null ls then [ codeLine "" 0 ] else renumberLines ls
      Nothing -> doc.lines
  in
    doc { lines = updatedLines }

-- | Split a line at a column.
splitLine :: Int -> Int -> CodeDocument -> CodeDocument
splitLine lineIdx colIdx doc =
  case getLine lineIdx doc of
    Nothing -> doc
    Just line ->
      let
        before = String.take colIdx (lineContent line)
        after = String.drop colIdx (lineContent line)
        line1 = line { content = before }
        line2 = codeLine after (lineIdx + 1)
        beforeLines = Array.take lineIdx doc.lines
        afterLines = Array.drop (lineIdx + 1) doc.lines
        newLines = beforeLines <> [ line1, line2 ] <> afterLines
      in
        doc { lines = renumberLines newLines }

-- | Join two adjacent lines.
joinLines :: Int -> CodeDocument -> CodeDocument
joinLines lineIdx doc =
  case getLine lineIdx doc of
    Nothing -> doc
    Just line1 ->
      case getLine (lineIdx + 1) doc of
        Nothing -> doc
        Just line2 ->
          let
            joined = line1 { content = lineContent line1 <> lineContent line2 }
          in
            setLine lineIdx joined (deleteLine (lineIdx + 1) doc)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // text operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Insert text at a position.
insertTextAt :: Int -> Int -> String -> CodeDocument -> CodeDocument
insertTextAt lineIdx colIdx text doc =
  case getLine lineIdx doc of
    Nothing -> doc
    Just line ->
      let
        content' = lineContent line
        before = String.take colIdx content'
        after = String.drop colIdx content'
        newContent = before <> text <> after
        newLine = line { content = newContent, tokens = [] }
      in
        setLine lineIdx newLine doc

-- | Delete text at a position.
deleteTextAt :: Int -> Int -> Int -> CodeDocument -> CodeDocument
deleteTextAt lineIdx startCol length doc =
  case getLine lineIdx doc of
    Nothing -> doc
    Just line ->
      let
        content' = lineContent line
        before = String.take startCol content'
        after = String.drop (startCol + length) content'
        newContent = before <> after
        newLine = line { content = newContent, tokens = [] }
      in
        setLine lineIdx newLine doc

-- | Replace text at a position.
replaceTextAt :: Int -> Int -> Int -> String -> CodeDocument -> CodeDocument
replaceTextAt lineIdx startCol length newText doc =
  insertTextAt lineIdx startCol newText (deleteTextAt lineIdx startCol length doc)

-- | Get text in a range.
getTextInRange :: Int -> Int -> Int -> Int -> CodeDocument -> String
getTextInRange startLine startCol endLine endCol doc
  | startLine == endLine =
      case getLine startLine doc of
        Nothing -> ""
        Just line -> 
          String.take (endCol - startCol) (String.drop startCol (lineContent line))
  | otherwise =
      let
        firstLineText = case getLine startLine doc of
          Nothing -> ""
          Just line -> String.drop startCol (lineContent line)
        middleLines = Array.mapMaybe (\i -> map lineContent (getLine i doc)) 
                        (Array.range (startLine + 1) (endLine - 1))
        lastLineText = case getLine endLine doc of
          Nothing -> ""
          Just line -> String.take endCol (lineContent line)
      in
        String.joinWith "\n" ([ firstLineText ] <> middleLines <> [ lastLineText ])
