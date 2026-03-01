-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // color // serialization
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Record serialization conversions for backend persistence
-- |
-- | **Purpose:**
-- | Convert color types to/from plain records for JSON serialization.
-- | Used when persisting colors to databases or APIs.
-- |
-- | **Re-exports:**
-- | These functions delegate to the underlying type modules.
-- | Gathered here for convenience in the Conversion namespace.

module Hydrogen.Schema.Color.Conversion.Serialization
  ( -- * RGB Records
    rgbToRecord
  , rgbFromRecord
  
  -- * HSL Records
  , hslToRecord
  , hslFromRecord
  
  -- * CMYK Records
  , cmykToRecord
  , cmykFromRecord
  
  -- * LAB Records
  , labToRecord
  , labFromRecord
  
  -- * LCH Records
  , lchToRecord
  , lchFromRecord
  
  -- * XYZ Records
  , xyzToRecord
  , xyzFromRecord
  ) where

import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.CMYK as CMYK
import Hydrogen.Schema.Color.LAB as LAB
import Hydrogen.Schema.Color.LCH as LCH
import Hydrogen.Schema.Color.XYZ as XYZ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // rgb // records
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB → Record (for JSON serialization / backend persistence)
rgbToRecord :: RGB.RGB -> { r :: Int, g :: Int, b :: Int }
rgbToRecord = RGB.rgbToRecord

-- | Record → RGB (from JSON deserialization / backend)
rgbFromRecord :: { r :: Int, g :: Int, b :: Int } -> RGB.RGB
rgbFromRecord = RGB.rgbFromRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // hsl // records
-- ═════════════════════════════════════════════════════════════════════════════

-- | HSL → Record (for JSON serialization / backend persistence)
hslToRecord :: HSL.HSL -> { h :: Int, s :: Int, l :: Int }
hslToRecord = HSL.hslToRecord

-- | Record → HSL (from JSON deserialization / backend)
hslFromRecord :: { h :: Int, s :: Int, l :: Int } -> HSL.HSL
hslFromRecord = HSL.hslFromRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // cmyk // records
-- ═════════════════════════════════════════════════════════════════════════════

-- | CMYK → Record (for JSON serialization / backend persistence)
cmykToRecord :: CMYK.CMYK -> { c :: Int, m :: Int, y :: Int, k :: Int }
cmykToRecord = CMYK.cmykToRecord

-- | Record → CMYK (from JSON deserialization / backend)
cmykFromRecord :: { c :: Int, m :: Int, y :: Int, k :: Int } -> CMYK.CMYK
cmykFromRecord = CMYK.cmykFromRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // lab // records
-- ═════════════════════════════════════════════════════════════════════════════

-- | LAB → Record (for JSON serialization / backend persistence)
labToRecord :: LAB.LAB -> { l :: Number, a :: Number, b :: Number }
labToRecord = LAB.labToRecord

-- | Record → LAB (from JSON deserialization / backend)
labFromRecord :: { l :: Number, a :: Number, b :: Number } -> LAB.LAB
labFromRecord = LAB.labFromRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // lch // records
-- ═════════════════════════════════════════════════════════════════════════════

-- | LCH → Record (for JSON serialization / backend persistence)
lchToRecord :: LCH.LCH -> { l :: Number, c :: Number, h :: Number }
lchToRecord = LCH.lchToRecord

-- | Record → LCH (from JSON deserialization / backend)
lchFromRecord :: { l :: Number, c :: Number, h :: Number } -> LCH.LCH
lchFromRecord = LCH.lchFromRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // xyz // records
-- ═════════════════════════════════════════════════════════════════════════════

-- | XYZ → Record (for JSON serialization / backend persistence)
xyzToRecord :: XYZ.XYZ -> { x :: Number, y :: Number, z :: Number }
xyzToRecord = XYZ.xyzToRecord

-- | Record → XYZ (from JSON deserialization / backend)
xyzFromRecord :: { x :: Number, y :: Number, z :: Number } -> XYZ.XYZ
xyzFromRecord = XYZ.xyzFromRecord
