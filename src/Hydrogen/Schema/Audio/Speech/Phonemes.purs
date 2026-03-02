-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // audio // speech // phonemes
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | IPA phoneme atoms for speech recognition.
-- |
-- | This module provides a representative subset of IPA (International Phonetic
-- | Alphabet) phonemes commonly used in English speech recognition. Each phoneme
-- | is categorized by its manner of articulation.
-- |
-- | ## Phoneme Categories
-- |
-- | - **Vowel**: Open vocal tract sounds (i, e, ɛ, æ, etc.)
-- | - **Plosive**: Stop consonants with complete closure (p, b, t, d, k, g)
-- | - **Fricative**: Friction sounds (f, v, s, z, ʃ, ʒ)
-- | - **Affricate**: Plosive+fricative combinations (tʃ, dʒ)
-- | - **Nasal**: Nasal consonants (m, n, ŋ)
-- | - **Approximant**: Glides and liquids (w, j, r, l)
-- | - **Silence**: Pause or silence marker

module Hydrogen.Schema.Audio.Speech.Phonemes
  ( -- * Phoneme Category
    PhonemeCategory(CategoryVowel, CategoryPlosive, CategoryFricative, CategoryAffricate, CategoryNasal, CategoryApproximant, CategorySilence)
  , phonemeCategoryName
  
  -- * IPA Phonemes
  , IPAPhoneme(PhonemeI, PhonemeE, PhonemeEpsilon, PhonemeAE, PhonemeA, PhonemeO, PhonemeU, PhonemeUpsilon, PhonemeSchwa, PhonemeWedge, PhonemeP, PhonemeB, PhonemeT, PhonemeD, PhonemeK, PhonemeG, PhonemeF, PhonemeV, PhonemeTheta, PhonemeEth, PhonemeS, PhonemeZ, PhonemeSH, PhonemeZH, PhonemeH, PhonemeCH, PhonemeJH, PhonemeM, PhonemeN, PhonemeNG, PhonemeW, PhonemeY, PhonemeR, PhonemeL, PhonemeSilence)
  , ipaPhonemeSymbol
  , ipaPhonemeCategory
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // phoneme categories
-- ═════════════════════════════════════════════════════════════════════════════

-- | PhonemeCategory - broad phoneme classification.
data PhonemeCategory
  = CategoryVowel       -- ^ Vowel sounds
  | CategoryPlosive     -- ^ Stop consonants (p, b, t, d, k, g)
  | CategoryFricative   -- ^ Friction sounds (f, v, s, z, ʃ, ʒ)
  | CategoryAffricate   -- ^ Plosive+fricative (tʃ, dʒ)
  | CategoryNasal       -- ^ Nasal consonants (m, n, ŋ)
  | CategoryApproximant -- ^ Glides/liquids (w, j, r, l)
  | CategorySilence     -- ^ Pause/silence

derive instance eqPhonemeCategory :: Eq PhonemeCategory
derive instance ordPhonemeCategory :: Ord PhonemeCategory

instance showPhonemeCategory :: Show PhonemeCategory where
  show = phonemeCategoryName

-- | Get display name for phoneme category
phonemeCategoryName :: PhonemeCategory -> String
phonemeCategoryName CategoryVowel = "Vowel"
phonemeCategoryName CategoryPlosive = "Plosive"
phonemeCategoryName CategoryFricative = "Fricative"
phonemeCategoryName CategoryAffricate = "Affricate"
phonemeCategoryName CategoryNasal = "Nasal"
phonemeCategoryName CategoryApproximant = "Approximant"
phonemeCategoryName CategorySilence = "Silence"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // ipa phonemes
-- ═════════════════════════════════════════════════════════════════════════════

-- | IPAPhoneme - Common IPA phonemes for English speech recognition.
-- | This is a representative subset; full IPA would have ~100+ phonemes.
data IPAPhoneme
  -- Vowels
  = PhonemeI      -- ^ /i/ as in "beat"
  | PhonemeE      -- ^ /e/ as in "bait"
  | PhonemeEpsilon -- ^ /ɛ/ as in "bet"
  | PhonemeAE     -- ^ /æ/ as in "bat"
  | PhonemeA      -- ^ /ɑ/ as in "bot"
  | PhonemeO      -- ^ /o/ as in "boat"
  | PhonemeU      -- ^ /u/ as in "boot"
  | PhonemeUpsilon -- ^ /ʊ/ as in "book"
  | PhonemeSchwa  -- ^ /ə/ as in "about"
  | PhonemeWedge  -- ^ /ʌ/ as in "but"
  -- Plosives
  | PhonemeP      -- ^ /p/ as in "pat"
  | PhonemeB      -- ^ /b/ as in "bat"
  | PhonemeT      -- ^ /t/ as in "tap"
  | PhonemeD      -- ^ /d/ as in "dad"
  | PhonemeK      -- ^ /k/ as in "cat"
  | PhonemeG      -- ^ /g/ as in "gap"
  -- Fricatives
  | PhonemeF      -- ^ /f/ as in "fat"
  | PhonemeV      -- ^ /v/ as in "vat"
  | PhonemeTheta  -- ^ /θ/ as in "think"
  | PhonemeEth    -- ^ /ð/ as in "this"
  | PhonemeS      -- ^ /s/ as in "sat"
  | PhonemeZ      -- ^ /z/ as in "zap"
  | PhonemeSH     -- ^ /ʃ/ as in "ship"
  | PhonemeZH     -- ^ /ʒ/ as in "measure"
  | PhonemeH      -- ^ /h/ as in "hat"
  -- Affricates
  | PhonemeCH     -- ^ /tʃ/ as in "chip"
  | PhonemeJH     -- ^ /dʒ/ as in "judge"
  -- Nasals
  | PhonemeM      -- ^ /m/ as in "mat"
  | PhonemeN      -- ^ /n/ as in "nap"
  | PhonemeNG     -- ^ /ŋ/ as in "sing"
  -- Approximants
  | PhonemeW      -- ^ /w/ as in "wet"
  | PhonemeY      -- ^ /j/ as in "yes"
  | PhonemeR      -- ^ /ɹ/ as in "rat"
  | PhonemeL      -- ^ /l/ as in "lap"
  -- Special
  | PhonemeSilence -- ^ Silence/pause

derive instance eqIPAPhoneme :: Eq IPAPhoneme
derive instance ordIPAPhoneme :: Ord IPAPhoneme

instance showIPAPhoneme :: Show IPAPhoneme where
  show = ipaPhonemeSymbol

-- | Get IPA symbol for phoneme
ipaPhonemeSymbol :: IPAPhoneme -> String
ipaPhonemeSymbol PhonemeI = "i"
ipaPhonemeSymbol PhonemeE = "e"
ipaPhonemeSymbol PhonemeEpsilon = "ɛ"
ipaPhonemeSymbol PhonemeAE = "æ"
ipaPhonemeSymbol PhonemeA = "ɑ"
ipaPhonemeSymbol PhonemeO = "o"
ipaPhonemeSymbol PhonemeU = "u"
ipaPhonemeSymbol PhonemeUpsilon = "ʊ"
ipaPhonemeSymbol PhonemeSchwa = "ə"
ipaPhonemeSymbol PhonemeWedge = "ʌ"
ipaPhonemeSymbol PhonemeP = "p"
ipaPhonemeSymbol PhonemeB = "b"
ipaPhonemeSymbol PhonemeT = "t"
ipaPhonemeSymbol PhonemeD = "d"
ipaPhonemeSymbol PhonemeK = "k"
ipaPhonemeSymbol PhonemeG = "g"
ipaPhonemeSymbol PhonemeF = "f"
ipaPhonemeSymbol PhonemeV = "v"
ipaPhonemeSymbol PhonemeTheta = "θ"
ipaPhonemeSymbol PhonemeEth = "ð"
ipaPhonemeSymbol PhonemeS = "s"
ipaPhonemeSymbol PhonemeZ = "z"
ipaPhonemeSymbol PhonemeSH = "ʃ"
ipaPhonemeSymbol PhonemeZH = "ʒ"
ipaPhonemeSymbol PhonemeH = "h"
ipaPhonemeSymbol PhonemeCH = "tʃ"
ipaPhonemeSymbol PhonemeJH = "dʒ"
ipaPhonemeSymbol PhonemeM = "m"
ipaPhonemeSymbol PhonemeN = "n"
ipaPhonemeSymbol PhonemeNG = "ŋ"
ipaPhonemeSymbol PhonemeW = "w"
ipaPhonemeSymbol PhonemeY = "j"
ipaPhonemeSymbol PhonemeR = "ɹ"
ipaPhonemeSymbol PhonemeL = "l"
ipaPhonemeSymbol PhonemeSilence = "SIL"

-- | Get category for phoneme
ipaPhonemeCategory :: IPAPhoneme -> PhonemeCategory
ipaPhonemeCategory PhonemeI = CategoryVowel
ipaPhonemeCategory PhonemeE = CategoryVowel
ipaPhonemeCategory PhonemeEpsilon = CategoryVowel
ipaPhonemeCategory PhonemeAE = CategoryVowel
ipaPhonemeCategory PhonemeA = CategoryVowel
ipaPhonemeCategory PhonemeO = CategoryVowel
ipaPhonemeCategory PhonemeU = CategoryVowel
ipaPhonemeCategory PhonemeUpsilon = CategoryVowel
ipaPhonemeCategory PhonemeSchwa = CategoryVowel
ipaPhonemeCategory PhonemeWedge = CategoryVowel
ipaPhonemeCategory PhonemeP = CategoryPlosive
ipaPhonemeCategory PhonemeB = CategoryPlosive
ipaPhonemeCategory PhonemeT = CategoryPlosive
ipaPhonemeCategory PhonemeD = CategoryPlosive
ipaPhonemeCategory PhonemeK = CategoryPlosive
ipaPhonemeCategory PhonemeG = CategoryPlosive
ipaPhonemeCategory PhonemeF = CategoryFricative
ipaPhonemeCategory PhonemeV = CategoryFricative
ipaPhonemeCategory PhonemeTheta = CategoryFricative
ipaPhonemeCategory PhonemeEth = CategoryFricative
ipaPhonemeCategory PhonemeS = CategoryFricative
ipaPhonemeCategory PhonemeZ = CategoryFricative
ipaPhonemeCategory PhonemeSH = CategoryFricative
ipaPhonemeCategory PhonemeZH = CategoryFricative
ipaPhonemeCategory PhonemeH = CategoryFricative
ipaPhonemeCategory PhonemeCH = CategoryAffricate
ipaPhonemeCategory PhonemeJH = CategoryAffricate
ipaPhonemeCategory PhonemeM = CategoryNasal
ipaPhonemeCategory PhonemeN = CategoryNasal
ipaPhonemeCategory PhonemeNG = CategoryNasal
ipaPhonemeCategory PhonemeW = CategoryApproximant
ipaPhonemeCategory PhonemeY = CategoryApproximant
ipaPhonemeCategory PhonemeR = CategoryApproximant
ipaPhonemeCategory PhonemeL = CategoryApproximant
ipaPhonemeCategory PhonemeSilence = CategorySilence
