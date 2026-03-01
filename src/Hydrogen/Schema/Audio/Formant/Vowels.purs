-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // audio // formant // vowels
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vowel features and IPA vowel atoms for speech synthesis.
-- |
-- | ## Vowel Features
-- |
-- | Vowels are characterized by three articulatory features:
-- | - Height (tongue position: close to open)
-- | - Backness (tongue position: front to back)
-- | - Rounding (lip shape)
-- |
-- | ## IPA Vowels
-- |
-- | Standard IPA vowel phonemes with associated formant frequencies
-- | based on Peterson & Barney (1952) adult male averages.

module Hydrogen.Schema.Audio.Formant.Vowels
  ( -- * Vowel Atoms
    VowelHeight(..)
  , VowelBackness(..)
  , VowelRounding(..)
  , vowelHeightName
  , vowelBacknessName
  , vowelRoundingName
  
  -- * IPA Vowels
  , IPAVowel(..)
  , ipaVowelSymbol
  , ipaVowelExample
  , ipaVowelToFormants
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Hydrogen.Schema.Audio.Formant.Types
  ( F1(F1)
  , F2(F2)
  , F3(F3)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // vowel features
-- ═════════════════════════════════════════════════════════════════════════════

-- | VowelHeight - tongue height position.
-- | Corresponds inversely to F1 frequency.
data VowelHeight
  = HeightClose     -- ^ High tongue position (/i/, /u/)
  | HeightCloseMid  -- ^ Between close and mid (/e/, /o/)
  | HeightMid       -- ^ Mid position (schwa)
  | HeightOpenMid   -- ^ Between mid and open (/ɛ/, /ɔ/)
  | HeightOpen      -- ^ Low tongue position (/a/, /ɑ/)

derive instance eqVowelHeight :: Eq VowelHeight
derive instance ordVowelHeight :: Ord VowelHeight

instance showVowelHeight :: Show VowelHeight where
  show = vowelHeightName

-- | Get display name for vowel height
vowelHeightName :: VowelHeight -> String
vowelHeightName HeightClose = "Close"
vowelHeightName HeightCloseMid = "Close-Mid"
vowelHeightName HeightMid = "Mid"
vowelHeightName HeightOpenMid = "Open-Mid"
vowelHeightName HeightOpen = "Open"

-- | VowelBackness - tongue front/back position.
-- | Corresponds to F2 frequency.
data VowelBackness
  = BacknessFront    -- ^ Front vowels (/i/, /e/)
  | BacknessCentral  -- ^ Central vowels (schwa)
  | BacknessBack     -- ^ Back vowels (/u/, /o/, /ɑ/)

derive instance eqVowelBackness :: Eq VowelBackness
derive instance ordVowelBackness :: Ord VowelBackness

instance showVowelBackness :: Show VowelBackness where
  show = vowelBacknessName

-- | Get display name for vowel backness
vowelBacknessName :: VowelBackness -> String
vowelBacknessName BacknessFront = "Front"
vowelBacknessName BacknessCentral = "Central"
vowelBacknessName BacknessBack = "Back"

-- | VowelRounding - lip rounding.
-- | Rounded vowels have lower formants (especially F2, F3).
data VowelRounding
  = RoundingUnrounded  -- ^ Spread lips (/i/, /e/, /a/)
  | RoundingRounded    -- ^ Rounded lips (/u/, /o/, /y/)

derive instance eqVowelRounding :: Eq VowelRounding
derive instance ordVowelRounding :: Ord VowelRounding

instance showVowelRounding :: Show VowelRounding where
  show = vowelRoundingName

-- | Get display name for vowel rounding
vowelRoundingName :: VowelRounding -> String
vowelRoundingName RoundingUnrounded = "Unrounded"
vowelRoundingName RoundingRounded = "Rounded"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // ipa vowels
-- ═════════════════════════════════════════════════════════════════════════════

-- | IPAVowel - Standard IPA vowel phonemes.
-- | Each has defined formant frequencies for synthesis.
data IPAVowel
  = VowelI      -- ^ /i/ as in "beat"
  | VowelY      -- ^ /y/ as in French "lune"
  | VowelE      -- ^ /e/ as in "bait"
  | VowelOE     -- ^ /ø/ as in French "deux"
  | VowelEpsilon -- ^ /ɛ/ as in "bet"
  | VowelSchwa  -- ^ /ə/ as in "about"
  | VowelA      -- ^ /a/ as in "father"
  | VowelAE     -- ^ /æ/ as in "bat"
  | VowelOpenO  -- ^ /ɔ/ as in "bought"
  | VowelO      -- ^ /o/ as in "boat"
  | VowelU      -- ^ /u/ as in "boot"
  | VowelUpsilon -- ^ /ʊ/ as in "book"
  | VowelWedge  -- ^ /ʌ/ as in "but"
  | VowelAsh    -- ^ /ɑ/ as in "father" (back)

derive instance eqIPAVowel :: Eq IPAVowel
derive instance ordIPAVowel :: Ord IPAVowel

instance showIPAVowel :: Show IPAVowel where
  show v = ipaVowelSymbol v

-- | Get IPA symbol for vowel
ipaVowelSymbol :: IPAVowel -> String
ipaVowelSymbol VowelI = "i"
ipaVowelSymbol VowelY = "y"
ipaVowelSymbol VowelE = "e"
ipaVowelSymbol VowelOE = "ø"
ipaVowelSymbol VowelEpsilon = "ɛ"
ipaVowelSymbol VowelSchwa = "ə"
ipaVowelSymbol VowelA = "a"
ipaVowelSymbol VowelAE = "æ"
ipaVowelSymbol VowelOpenO = "ɔ"
ipaVowelSymbol VowelO = "o"
ipaVowelSymbol VowelU = "u"
ipaVowelSymbol VowelUpsilon = "ʊ"
ipaVowelSymbol VowelWedge = "ʌ"
ipaVowelSymbol VowelAsh = "ɑ"

-- | Get example word for vowel
ipaVowelExample :: IPAVowel -> String
ipaVowelExample VowelI = "beat"
ipaVowelExample VowelY = "lune (FR)"
ipaVowelExample VowelE = "bait"
ipaVowelExample VowelOE = "deux (FR)"
ipaVowelExample VowelEpsilon = "bet"
ipaVowelExample VowelSchwa = "about"
ipaVowelExample VowelA = "father"
ipaVowelExample VowelAE = "bat"
ipaVowelExample VowelOpenO = "bought"
ipaVowelExample VowelO = "boat"
ipaVowelExample VowelU = "boot"
ipaVowelExample VowelUpsilon = "book"
ipaVowelExample VowelWedge = "but"
ipaVowelExample VowelAsh = "bot"

-- | Get standard formant frequencies for an IPA vowel.
-- | Values based on Peterson & Barney (1952) adult male averages.
ipaVowelToFormants :: IPAVowel -> { f1 :: F1, f2 :: F2, f3 :: F3 }
ipaVowelToFormants VowelI = { f1: F1 270.0, f2: F2 2290.0, f3: F3 3010.0 }
ipaVowelToFormants VowelY = { f1: F1 280.0, f2: F2 1900.0, f3: F3 2500.0 }
ipaVowelToFormants VowelE = { f1: F1 390.0, f2: F2 2100.0, f3: F3 2900.0 }
ipaVowelToFormants VowelOE = { f1: F1 370.0, f2: F2 1600.0, f3: F3 2400.0 }
ipaVowelToFormants VowelEpsilon = { f1: F1 530.0, f2: F2 1840.0, f3: F3 2480.0 }
ipaVowelToFormants VowelSchwa = { f1: F1 500.0, f2: F2 1500.0, f3: F3 2500.0 }
ipaVowelToFormants VowelA = { f1: F1 730.0, f2: F2 1200.0, f3: F3 2440.0 }
ipaVowelToFormants VowelAE = { f1: F1 660.0, f2: F2 1720.0, f3: F3 2410.0 }
ipaVowelToFormants VowelOpenO = { f1: F1 570.0, f2: F2 840.0, f3: F3 2410.0 }
ipaVowelToFormants VowelO = { f1: F1 400.0, f2: F2 750.0, f3: F3 2400.0 }
ipaVowelToFormants VowelU = { f1: F1 300.0, f2: F2 870.0, f3: F3 2240.0 }
ipaVowelToFormants VowelUpsilon = { f1: F1 440.0, f2: F2 1020.0, f3: F3 2240.0 }
ipaVowelToFormants VowelWedge = { f1: F1 640.0, f2: F2 1190.0, f3: F3 2390.0 }
ipaVowelToFormants VowelAsh = { f1: F1 730.0, f2: F2 1090.0, f3: F3 2440.0 }
