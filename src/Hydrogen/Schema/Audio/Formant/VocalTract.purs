-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // audio // formant // vocaltract
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vocal tract modeling atoms for speech synthesis.
-- |
-- | ## Vocal Tract Model
-- |
-- | The vocal tract acts as a series of resonant filters. Tract length
-- | affects all formant frequencies (shorter tract = higher formants).
-- |
-- | ## Vocoder Parameters
-- |
-- | Vocoder atoms for frequency band analysis and formant manipulation.

module Hydrogen.Schema.Audio.Formant.VocalTract
  ( -- * Vocal Tract Atoms
    TractLength(TractLength)
  , tractLength
  , unwrapTractLength
  , tractLengthMale
  , tractLengthFemale
  , tractLengthChild
  
  -- * Vocoder Parameters
  , VocoderBands(VocoderBands)
  , vocoderBands
  , unwrapVocoderBands
  
  -- * Formant Shift
  , FormantShift(FormantShift)
  , formantShift
  , unwrapFormantShift
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<)
  , (>)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // vocal tract
-- ═════════════════════════════════════════════════════════════════════════════

-- | TractLength - vocal tract length in cm.
-- | Affects all formant frequencies (shorter tract = higher formants).
-- | Adult male ~17cm, female ~14cm, child ~10cm.
newtype TractLength = TractLength Number

derive instance eqTractLength :: Eq TractLength
derive instance ordTractLength :: Ord TractLength

instance showTractLength :: Show TractLength where
  show (TractLength n) = show n <> " cm"

-- | Create a TractLength value (clamped to 8-22)
tractLength :: Number -> TractLength
tractLength n
  | n < 8.0 = TractLength 8.0
  | n > 22.0 = TractLength 22.0
  | otherwise = TractLength n

unwrapTractLength :: TractLength -> Number
unwrapTractLength (TractLength n) = n

-- | Typical adult male vocal tract length
tractLengthMale :: TractLength
tractLengthMale = TractLength 17.0

-- | Typical adult female vocal tract length
tractLengthFemale :: TractLength
tractLengthFemale = TractLength 14.0

-- | Typical child vocal tract length
tractLengthChild :: TractLength
tractLengthChild = TractLength 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // vocoder parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | VocoderBands - number of frequency bands in vocoder.
-- | More bands = higher resolution but more computation.
-- | Common values: 8, 16, 32, 64.
newtype VocoderBands = VocoderBands Int

derive instance eqVocoderBands :: Eq VocoderBands
derive instance ordVocoderBands :: Ord VocoderBands

instance showVocoderBands :: Show VocoderBands where
  show (VocoderBands n) = show n <> " bands"

-- | Create a VocoderBands value (clamped to 4-128)
vocoderBands :: Int -> VocoderBands
vocoderBands n
  | n < 4 = VocoderBands 4
  | n > 128 = VocoderBands 128
  | otherwise = VocoderBands n

unwrapVocoderBands :: VocoderBands -> Int
unwrapVocoderBands (VocoderBands n) = n

-- | FormantShift - shift all formants by a ratio.
-- | 1.0 = no shift, <1.0 = lower (larger person), >1.0 = higher (smaller).
-- | Used for voice morphing and character voices.
newtype FormantShift = FormantShift Number

derive instance eqFormantShift :: Eq FormantShift
derive instance ordFormantShift :: Ord FormantShift

instance showFormantShift :: Show FormantShift where
  show (FormantShift n) = show n <> "x shift"

-- | Create a FormantShift value (clamped to 0.5-2.0)
formantShift :: Number -> FormantShift
formantShift n
  | n < 0.5 = FormantShift 0.5
  | n > 2.0 = FormantShift 2.0
  | otherwise = FormantShift n

unwrapFormantShift :: FormantShift -> Number
unwrapFormantShift (FormantShift n) = n
