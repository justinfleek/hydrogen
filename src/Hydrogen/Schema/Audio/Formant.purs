-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // audio // formant
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Formant and vocal tract modeling atoms for speech synthesis.
-- |
-- | ## Formant Theory
-- |
-- | Formants are resonant frequencies of the vocal tract. The first two
-- | formants (F1, F2) are sufficient to distinguish most vowels. F1 relates
-- | to tongue height (open/closed), F2 to front/back position.
-- |
-- | ## Vowel Space
-- |
-- | The F1×F2 plane defines the vowel space. Every vowel sound corresponds
-- | to a point in this plane, enabling deterministic vowel synthesis.
-- |
-- | ## Vocal Tract Model
-- |
-- | The vocal tract acts as a series of resonant filters. Formant frequencies
-- | and bandwidths define the filter characteristics. This enables both
-- | speech synthesis and voice transformation (vocoding).
-- |
-- | ## Usage
-- | ```purescript
-- | import Hydrogen.Schema.Audio.Formant as Formant
-- |
-- | -- Define the vowel /a/ (as in "father")
-- | vowelA = Formant.vowel
-- |   (Formant.f1 800.0)   -- Low F1 = open
-- |   (Formant.f2 1200.0)  -- Mid F2 = central
-- |   (Formant.f3 2500.0)
-- | ```

module Hydrogen.Schema.Audio.Formant
  ( module Types
  , module Vowels
  , module Molecules
  , module VocalTract
  , module Bounds
  ) where

import Hydrogen.Schema.Audio.Formant.Types
  ( F1(F1)
  , F2(F2)
  , F3(F3)
  , F4(F4)
  , F5(F5)
  , FormantAmplitude(FormantAmplitude)
  , FormantBandwidth(FormantBandwidth)
  , bandwidthMedium
  , bandwidthNarrow
  , bandwidthWide
  , f1
  , f2
  , f3
  , f4
  , f5
  , formantAmplitude
  , formantBandwidth
  , unwrapF1
  , unwrapF2
  , unwrapF3
  , unwrapF4
  , unwrapF5
  , unwrapFormantAmplitude
  , unwrapFormantBandwidth
  ) as Types

import Hydrogen.Schema.Audio.Formant.Vowels
  ( IPAVowel(VowelI, VowelY, VowelE, VowelOE, VowelEpsilon, VowelSchwa, VowelA, VowelAE, VowelOpenO, VowelO, VowelU, VowelUpsilon, VowelWedge, VowelAsh)
  , VowelBackness(BacknessFront, BacknessCentral, BacknessBack)
  , VowelHeight(HeightClose, HeightCloseMid, HeightMid, HeightOpenMid, HeightOpen)
  , VowelRounding(RoundingUnrounded, RoundingRounded)
  , ipaVowelExample
  , ipaVowelSymbol
  , ipaVowelToFormants
  , vowelBacknessName
  , vowelHeightName
  , vowelRoundingName
  ) as Vowels

import Hydrogen.Schema.Audio.Formant.Molecules
  ( FormantSet
  , Vowel
  , formantSet
  , formantSetFromVowel
  , vowel
  , vowelFromIPA
  ) as Molecules

import Hydrogen.Schema.Audio.Formant.VocalTract
  ( FormantShift(FormantShift)
  , TractLength(TractLength)
  , VocoderBands(VocoderBands)
  , formantShift
  , tractLength
  , tractLengthChild
  , tractLengthFemale
  , tractLengthMale
  , unwrapFormantShift
  , unwrapTractLength
  , unwrapVocoderBands
  , vocoderBands
  ) as VocalTract

import Hydrogen.Schema.Audio.Formant.Bounds
  ( f1Bounds
  , f2Bounds
  , f3Bounds
  , f4Bounds
  , f5Bounds
  , formantAmplitudeBounds
  , formantBandwidthBounds
  , formantShiftBounds
  , tractLengthBounds
  , vocoderBandsBounds
  ) as Bounds
