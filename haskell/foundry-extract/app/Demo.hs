{- |
-- ===========================================================================
--                               // foundry // demo
-- ===========================================================================

Demo application that extracts brand components from jbreenconsulting.com
and generates Hydrogen PureScript atoms/molecules/compounds.

Usage:
  cabal run foundry-demo

Output:
  generated/Brand/Atoms/Colors.purs
  generated/Brand/Atoms/Typography.purs
  generated/Brand/Atoms/Spacing.purs
  generated/Brand/Molecules/Button.purs
  generated/Brand/Compounds/Hero.purs
  generated/Brand/Theme.purs

-- ===========================================================================
-}
module Main where

import Data.Aeson qualified as Aeson
import Data.ByteString.Lazy qualified as LBS
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Vector qualified as V
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))

import Foundry.Extract.Component
  ( ExtractedRegistry (..)
  , extractComponentRegistry
  )
import Foundry.Extract.Hydrogen
  ( GeneratedCode (..)
  , generateAll
  )
import Foundry.Extract.Types
  ( ScrapeResult (..)
  )

-- ===========================================================================
-- Main
-- ===========================================================================

main :: IO ()
main = do
  putStrLn "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  putStrLn "                        // foundry // brand demo"
  putStrLn "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  putStrLn ""

  -- Load extracted data
  putStrLn "[1/5] Loading jbreenconsulting_extracted.json..."
  jsonData <- LBS.readFile "jbreenconsulting_extracted.json"

  case Aeson.decode jsonData of
    Nothing -> do
      putStrLn "ERROR: Failed to parse JSON"
      putStrLn "Make sure jbreenconsulting_extracted.json exists in the current directory"
    Just scrapeResult -> do
      putStrLn $ "     Domain: " <> T.unpack (srDomain scrapeResult)
      putStrLn $ "     URL: " <> T.unpack (srURL scrapeResult)
      putStrLn ""

      -- Extract components
      putStrLn "[2/5] Extracting components..."
      let registry = extractComponentRegistry scrapeResult
      putStrLn $ "     Colors: " <> show (V.length (erColors registry))
      putStrLn $ "     Fonts: " <> show (V.length (erFonts registry))
      putStrLn $ "     Spacing: " <> show (V.length (erSpacing registry))
      putStrLn $ "     Buttons: " <> show (V.length (erButtons registry))
      putStrLn ""

      -- Generate PureScript
      putStrLn "[3/5] Generating PureScript..."
      let code = generateAll registry
      putStrLn "     Generated modules:"
      putStrLn "       - Brand.Atoms.Colors"
      putStrLn "       - Brand.Atoms.Typography"
      putStrLn "       - Brand.Atoms.Spacing"
      putStrLn "       - Brand.Molecules.Button"
      putStrLn "       - Brand.Compounds.Hero"
      putStrLn "       - Brand.Theme"
      putStrLn ""

      -- Write files
      putStrLn "[4/5] Writing files..."
      let outDir = "generated"
      createDirectoryIfMissing True (outDir </> "Brand" </> "Atoms")
      createDirectoryIfMissing True (outDir </> "Brand" </> "Molecules")
      createDirectoryIfMissing True (outDir </> "Brand" </> "Compounds")

      TIO.writeFile (outDir </> "Brand" </> "Atoms" </> "Colors.purs") (gcColors code)
      TIO.writeFile (outDir </> "Brand" </> "Atoms" </> "Typography.purs") (gcTypography code)
      TIO.writeFile (outDir </> "Brand" </> "Atoms" </> "Spacing.purs") (gcSpacing code)
      TIO.writeFile (outDir </> "Brand" </> "Molecules" </> "Button.purs") (gcButtons code)
      TIO.writeFile (outDir </> "Brand" </> "Compounds" </> "Hero.purs") (gcHero code)
      TIO.writeFile (outDir </> "Brand" </> "Theme.purs") (gcTheme code)

      putStrLn $ "     Written to: " <> outDir <> "/"
      putStrLn ""

      -- Summary
      putStrLn "[5/5] Summary"
      putStrLn "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
      putStrLn ""
      putStrLn "Brand: jbreenconsulting.com"
      putStrLn ""
      putStrLn "Atoms extracted:"
      putStrLn $ "  Colors:    " <> show (V.length (erColors registry)) <> " (primary: #8e43f0)"
      putStrLn $ "  Fonts:     " <> show (V.length (erFonts registry)) <> " (Raleway, Roboto, Open Sans)"
      putStrLn $ "  Spacing:   " <> show (V.length (erSpacing registry)) <> " tokens"
      putStrLn ""
      putStrLn "Molecules composed:"
      putStrLn "  - Primary Button (purple bg, white text)"
      putStrLn "  - Secondary Button (white bg, purple text)"
      putStrLn ""
      putStrLn "Compounds composed:"
      putStrLn "  - Hero Section (purple gradient, Raleway headings)"
      putStrLn "  - Card (white bg, rounded, shadow)"
      putStrLn ""
      putStrLn "Files generated:"
      putStrLn "  generated/Brand/Atoms/Colors.purs"
      putStrLn "  generated/Brand/Atoms/Typography.purs"
      putStrLn "  generated/Brand/Atoms/Spacing.purs"
      putStrLn "  generated/Brand/Molecules/Button.purs"
      putStrLn "  generated/Brand/Compounds/Hero.purs"
      putStrLn "  generated/Brand/Theme.purs"
      putStrLn ""
      putStrLn "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
      putStrLn "                                                  // demo complete"
      putStrLn "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
