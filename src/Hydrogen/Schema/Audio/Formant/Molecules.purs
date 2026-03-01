-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // audio // formant // molecules
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Formant and vowel molecules composed from atomic types.
-- |
-- | ## FormantSet
-- |
-- | Complete set of formant frequencies for synthesis, including
-- | frequencies and bandwidths for five formants.
-- |
-- | ## Vowel
-- |
-- | Complete vowel specification combining articulatory features
-- | with acoustic formants.

module Hydrogen.Schema.Audio.Formant.Molecules
  ( -- * Formant Set Molecule
    FormantSet
  , formantSet
  , formantSetFromVowel
  
  -- * Vowel Molecule
  , Vowel
  , vowel
  , vowelFromIPA
  ) where

import Prelude
  ( otherwise
  , (<)
  , (>)
  )

import Hydrogen.Schema.Audio.Formant.Types
  ( F1(F1)
  , F2(F2)
  , F3(F3)
  , F4(F4)
  , F5(F5)
  , FormantBandwidth
  , bandwidthMedium
  , bandwidthWide
  , unwrapF1
  , unwrapF2
  )

import Hydrogen.Schema.Audio.Formant.Vowels
  ( IPAVowel
    ( VowelI
    , VowelY
    , VowelE
    , VowelOE
    , VowelEpsilon
    , VowelSchwa
    , VowelA
    , VowelAE
    , VowelOpenO
    , VowelO
    , VowelU
    , VowelUpsilon
    , VowelWedge
    , VowelAsh
    )
  , VowelHeight
    ( HeightClose
    , HeightCloseMid
    , HeightMid
    , HeightOpenMid
    , HeightOpen
    )
  , VowelBackness
    ( BacknessFront
    , BacknessCentral
    , BacknessBack
    )
  , VowelRounding
    ( RoundingUnrounded
    , RoundingRounded
    )
  , ipaVowelToFormants
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // formant set molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | FormantSet - Complete set of formant frequencies for synthesis.
-- | Includes frequencies, bandwidths, and amplitudes for five formants.
type FormantSet =
  { f1 :: F1
  , f2 :: F2
  , f3 :: F3
  , f4 :: F4
  , f5 :: F5
  , bw1 :: FormantBandwidth
  , bw2 :: FormantBandwidth
  , bw3 :: FormantBandwidth
  , bw4 :: FormantBandwidth
  , bw5 :: FormantBandwidth
  }

-- | Create a formant set from the first three formants.
-- | F4 and F5 are estimated, bandwidths are set to defaults.
formantSet :: F1 -> F2 -> F3 -> FormantSet
formantSet formant1 formant2 formant3 =
  { f1: formant1
  , f2: formant2
  , f3: formant3
  , f4: F4 3500.0
  , f5: F5 4500.0
  , bw1: bandwidthMedium
  , bw2: bandwidthMedium
  , bw3: bandwidthMedium
  , bw4: bandwidthWide
  , bw5: bandwidthWide
  }

-- | Create a formant set from an IPA vowel.
formantSetFromVowel :: IPAVowel -> FormantSet
formantSetFromVowel v =
  let formants = ipaVowelToFormants v
  in formantSet formants.f1 formants.f2 formants.f3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // vowel molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vowel - Complete vowel specification.
-- | Combines articulatory features with acoustic formants.
type Vowel =
  { height :: VowelHeight
  , backness :: VowelBackness
  , rounding :: VowelRounding
  , formants :: FormantSet
  }

-- | Create a vowel from formants (features inferred from F1/F2).
vowel :: F1 -> F2 -> F3 -> Vowel
vowel formant1 formant2 formant3 =
  { height: inferHeight (unwrapF1 formant1)
  , backness: inferBackness (unwrapF2 formant2)
  , rounding: RoundingUnrounded  -- Default to unrounded
  , formants: formantSet formant1 formant2 formant3
  }
  where
    inferHeight f1val
      | f1val < 350.0 = HeightClose
      | f1val < 450.0 = HeightCloseMid
      | f1val < 550.0 = HeightMid
      | f1val < 650.0 = HeightOpenMid
      | otherwise = HeightOpen
    inferBackness f2val
      | f2val > 1800.0 = BacknessFront
      | f2val > 1200.0 = BacknessCentral
      | otherwise = BacknessBack

-- | Create a vowel from an IPA vowel.
vowelFromIPA :: IPAVowel -> Vowel
vowelFromIPA v =
  let fset = formantSetFromVowel v
  in { height: inferHeightFromIPA v
     , backness: inferBacknessFromIPA v
     , rounding: inferRoundingFromIPA v
     , formants: fset
     }
  where
    inferHeightFromIPA VowelI = HeightClose
    inferHeightFromIPA VowelY = HeightClose
    inferHeightFromIPA VowelU = HeightClose
    inferHeightFromIPA VowelE = HeightCloseMid
    inferHeightFromIPA VowelOE = HeightCloseMid
    inferHeightFromIPA VowelO = HeightCloseMid
    inferHeightFromIPA VowelUpsilon = HeightCloseMid
    inferHeightFromIPA VowelSchwa = HeightMid
    inferHeightFromIPA VowelEpsilon = HeightOpenMid
    inferHeightFromIPA VowelOpenO = HeightOpenMid
    inferHeightFromIPA VowelWedge = HeightOpenMid
    inferHeightFromIPA VowelA = HeightOpen
    inferHeightFromIPA VowelAE = HeightOpen
    inferHeightFromIPA VowelAsh = HeightOpen
    
    inferBacknessFromIPA VowelI = BacknessFront
    inferBacknessFromIPA VowelY = BacknessFront
    inferBacknessFromIPA VowelE = BacknessFront
    inferBacknessFromIPA VowelOE = BacknessFront
    inferBacknessFromIPA VowelEpsilon = BacknessFront
    inferBacknessFromIPA VowelAE = BacknessFront
    inferBacknessFromIPA VowelSchwa = BacknessCentral
    inferBacknessFromIPA VowelWedge = BacknessCentral
    inferBacknessFromIPA VowelA = BacknessCentral
    inferBacknessFromIPA VowelU = BacknessBack
    inferBacknessFromIPA VowelO = BacknessBack
    inferBacknessFromIPA VowelOpenO = BacknessBack
    inferBacknessFromIPA VowelUpsilon = BacknessBack
    inferBacknessFromIPA VowelAsh = BacknessBack
    
    inferRoundingFromIPA VowelY = RoundingRounded
    inferRoundingFromIPA VowelOE = RoundingRounded
    inferRoundingFromIPA VowelU = RoundingRounded
    inferRoundingFromIPA VowelO = RoundingRounded
    inferRoundingFromIPA VowelOpenO = RoundingRounded
    inferRoundingFromIPA VowelUpsilon = RoundingRounded
    inferRoundingFromIPA _ = RoundingUnrounded
