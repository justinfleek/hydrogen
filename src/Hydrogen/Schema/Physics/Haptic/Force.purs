-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // physics // haptic // force
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Haptic force feedback primitives for BMI/tactile interfaces.
-- |
-- | ## What is Haptic Force Feedback?
-- |
-- | Haptic force feedback provides physical resistance or vibration to simulate
-- | touch. This enables:
-- | - Feeling virtual button clicks
-- | - Sensing object weight and resistance
-- | - Texture simulation through vibration patterns
-- | - Impact and collision feedback
-- |
-- | ## Physical Units
-- |
-- | - Force: Newtons (N) — 1 N = 1 kg·m/s²
-- | - Torque: Newton-meters (N·m)
-- | - Frequency: Hertz (Hz)
-- | - Duration: Milliseconds (ms)
-- |
-- | ## Human Perception Bounds
-- |
-- | - Minimum perceptible force: ~0.01 N (fingertip)
-- | - Maximum comfortable force: ~50 N (whole hand grip)
-- | - Vibration frequency range: 1-1000 Hz (peak sensitivity 200-300 Hz)
-- | - Just-noticeable difference: ~7% force change
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, haptic feedback enables:
-- | - Realistic virtual object manipulation
-- | - Non-visual interfaces for accessibility
-- | - Training simulations (surgery, piloting, manufacturing)
-- | - Remote telepresence with physical sensation
-- |
-- | ## Data Sources
-- |
-- | Haptic perception research, IEEE haptics standards, human factors data.

module Hydrogen.Schema.Physics.Haptic.Force
  ( -- * Force Types
    Force
  , force
  , forceUnsafe
  , unwrapForce
  , forceBounds
  , newtons
  , millinewtons
  , gramsForce
  , poundsForce
  
  -- * Torque Types
  , Torque
  , torque
  , torqueUnsafe
  , unwrapTorque
  , torqueBounds
  , newtonMeters
  , newtonCentimeters
  
  -- * Vibration Types
  , Frequency
  , frequency
  , frequencyUnsafe
  , unwrapFrequency
  , frequencyBounds
  , hertz
  
  -- * Duration Types
  , Duration
  , duration
  , durationUnsafe
  , unwrapDuration
  , durationBounds
  , milliseconds
  , seconds
  
  -- * Haptic Effect Types
  , HapticPulse
  , pulse
  , HapticVibration
  , vibration
  , HapticTexture
  , texture
  , HapticImpact
  , impact
  , HapticResistance
  , resistance
  
  -- * Preset Effects — Clicks
  , buttonClick
  , softClick
  , hardClick
  , toggleOn
  , toggleOff
  
  -- * Preset Effects — Notifications
  , notificationLight
  , notificationMedium
  , notificationStrong
  , warningBuzz
  , errorBuzz
  , successPulse
  
  -- * Preset Effects — Textures
  , smoothSurface
  , roughSurface
  , sandpaper
  , corduroy
  , bumpyRoad
  
  -- * Preset Effects — Impacts
  , lightTap
  , mediumImpact
  , heavyImpact
  , collision
  
  -- * Preset Effects — Resistance
  , freeSpin
  , lightResistance
  , mediumResistance
  , heavyResistance
  , hardStop
  
  -- * Operations
  , scaleForce
  , scaleTorque
  , combineForces
  , isPerceptible
  , isComfortable
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, abs, sin, cos, exp) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // force // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Force in Newtons [0.0, 1000.0].
-- |
-- | ## Bounds Rationale
-- |
-- | - Lower bound 0.0: No force
-- | - Upper bound 1000: Well above maximum haptic device output (~100N)
-- |
-- | Most haptic feedback is in the 0.1-50N range for comfort.
newtype Force = Force Number

derive instance eqForce :: Eq Force
derive instance ordForce :: Ord Force

instance showForce :: Show Force where
  show (Force n) = "Force(" <> show n <> " N)"

-- | Create Force with validation.
force :: Number -> Maybe Force
force n
  | n >= 0.0 && n <= 1000.0 = Just (Force n)
  | otherwise = Nothing

-- | Create Force with clamping.
forceUnsafe :: Number -> Force
forceUnsafe n = Force (Bounded.clampNumber 0.0 1000.0 n)

-- | Extract the underlying Number.
unwrapForce :: Force -> Number
unwrapForce (Force n) = n

-- | Bounds documentation for force.
forceBounds :: Bounded.NumberBounds
forceBounds = Bounded.numberBounds 0.0 1000.0 Bounded.Clamps
  "force"
  "Force in Newtons (0.01=threshold, 50=max comfortable)"

-- | Create force from Newtons.
newtons :: Number -> Force
newtons = forceUnsafe

-- | Create force from millinewtons.
millinewtons :: Number -> Force
millinewtons n = forceUnsafe (n / 1000.0)

-- | Create force from grams-force (1 gf ≈ 0.00981 N).
gramsForce :: Number -> Force
gramsForce n = forceUnsafe (n * 0.00980665)

-- | Create force from pounds-force (1 lbf ≈ 4.448 N).
poundsForce :: Number -> Force
poundsForce n = forceUnsafe (n * 4.44822)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // torque // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Torque in Newton-meters [0.0, 100.0].
-- |
-- | Used for rotational haptic feedback (steering wheels, knobs, etc.)
newtype Torque = Torque Number

derive instance eqTorque :: Eq Torque
derive instance ordTorque :: Ord Torque

instance showTorque :: Show Torque where
  show (Torque n) = "Torque(" <> show n <> " N·m)"

-- | Create Torque with validation.
torque :: Number -> Maybe Torque
torque n
  | n >= 0.0 && n <= 100.0 = Just (Torque n)
  | otherwise = Nothing

-- | Create Torque with clamping.
torqueUnsafe :: Number -> Torque
torqueUnsafe n = Torque (Bounded.clampNumber 0.0 100.0 n)

-- | Extract the underlying Number.
unwrapTorque :: Torque -> Number
unwrapTorque (Torque n) = n

-- | Bounds documentation for torque.
torqueBounds :: Bounded.NumberBounds
torqueBounds = Bounded.numberBounds 0.0 100.0 Bounded.Clamps
  "torque"
  "Torque in Newton-meters"

-- | Create torque from Newton-meters.
newtonMeters :: Number -> Torque
newtonMeters = torqueUnsafe

-- | Create torque from Newton-centimeters.
newtonCentimeters :: Number -> Torque
newtonCentimeters n = torqueUnsafe (n / 100.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // frequency // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vibration frequency in Hertz [1.0, 1000.0].
-- |
-- | Human tactile perception range for vibration.
-- | Peak sensitivity around 200-300 Hz.
newtype Frequency = Frequency Number

derive instance eqFrequency :: Eq Frequency
derive instance ordFrequency :: Ord Frequency

instance showFrequency :: Show Frequency where
  show (Frequency n) = "Frequency(" <> show n <> " Hz)"

-- | Create Frequency with validation.
frequency :: Number -> Maybe Frequency
frequency n
  | n >= 1.0 && n <= 1000.0 = Just (Frequency n)
  | otherwise = Nothing

-- | Create Frequency with clamping.
frequencyUnsafe :: Number -> Frequency
frequencyUnsafe n = Frequency (Bounded.clampNumber 1.0 1000.0 n)

-- | Extract the underlying Number.
unwrapFrequency :: Frequency -> Number
unwrapFrequency (Frequency n) = n

-- | Bounds documentation for frequency.
frequencyBounds :: Bounded.NumberBounds
frequencyBounds = Bounded.numberBounds 1.0 1000.0 Bounded.Clamps
  "frequency"
  "Vibration frequency in Hz (peak sensitivity 200-300 Hz)"

-- | Create frequency from Hertz.
hertz :: Number -> Frequency
hertz = frequencyUnsafe

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // duration // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Duration in milliseconds [0.0, 10000.0].
-- |
-- | Haptic effects typically range from 1ms (sharp click) to 1000ms (long buzz).
newtype Duration = Duration Number

derive instance eqDuration :: Eq Duration
derive instance ordDuration :: Ord Duration

instance showDuration :: Show Duration where
  show (Duration n) = "Duration(" <> show n <> " ms)"

-- | Create Duration with validation.
duration :: Number -> Maybe Duration
duration n
  | n >= 0.0 && n <= 10000.0 = Just (Duration n)
  | otherwise = Nothing

-- | Create Duration with clamping.
durationUnsafe :: Number -> Duration
durationUnsafe n = Duration (Bounded.clampNumber 0.0 10000.0 n)

-- | Extract the underlying Number.
unwrapDuration :: Duration -> Number
unwrapDuration (Duration n) = n

-- | Bounds documentation for duration.
durationBounds :: Bounded.NumberBounds
durationBounds = Bounded.numberBounds 0.0 10000.0 Bounded.Clamps
  "duration"
  "Duration in milliseconds"

-- | Create duration from milliseconds.
milliseconds :: Number -> Duration
milliseconds = durationUnsafe

-- | Create duration from seconds.
seconds :: Number -> Duration
seconds n = durationUnsafe (n * 1000.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // haptic effect types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single haptic pulse — a brief force application.
type HapticPulse =
  { force :: Force
  , duration :: Duration
  }

-- | Create a haptic pulse.
pulse :: Number -> Number -> HapticPulse
pulse f d =
  { force: forceUnsafe f
  , duration: durationUnsafe d
  }

-- | Continuous vibration at a frequency.
type HapticVibration =
  { frequency :: Frequency
  , amplitude :: Force
  , duration :: Duration
  }

-- | Create a vibration effect.
vibration :: Number -> Number -> Number -> HapticVibration
vibration freq amp dur =
  { frequency: frequencyUnsafe freq
  , amplitude: forceUnsafe amp
  , duration: durationUnsafe dur
  }

-- | Texture simulation through modulated vibration.
type HapticTexture =
  { baseFrequency :: Frequency
  , roughness :: Number  -- 0.0 (smooth) to 1.0 (rough)
  , amplitude :: Force
  }

-- | Create a texture effect.
texture :: Number -> Number -> Number -> HapticTexture
texture freq rough amp =
  { baseFrequency: frequencyUnsafe freq
  , roughness: Bounded.clampNumber 0.0 1.0 rough
  , amplitude: forceUnsafe amp
  }

-- | Impact simulation — sharp onset with decay.
type HapticImpact =
  { peakForce :: Force
  , attackTime :: Duration   -- rise time to peak
  , decayTime :: Duration    -- fall time to zero
  }

-- | Create an impact effect.
impact :: Number -> Number -> Number -> HapticImpact
impact peak attack decay =
  { peakForce: forceUnsafe peak
  , attackTime: durationUnsafe attack
  , decayTime: durationUnsafe decay
  }

-- | Continuous resistance (spring-like feedback).
type HapticResistance =
  { stiffness :: Force     -- Force per unit displacement
  , damping :: Force       -- Velocity-dependent resistance
  , maxForce :: Force      -- Saturation limit
  }

-- | Create a resistance effect.
resistance :: Number -> Number -> Number -> HapticResistance
resistance stiff damp maxF =
  { stiffness: forceUnsafe stiff
  , damping: forceUnsafe damp
  , maxForce: forceUnsafe maxF
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // preset effects — clicks
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard button click — tactile confirmation.
buttonClick :: HapticPulse
buttonClick = pulse 2.0 10.0

-- | Soft click — subtle feedback.
softClick :: HapticPulse
softClick = pulse 0.5 8.0

-- | Hard click — definite feedback.
hardClick :: HapticPulse
hardClick = pulse 5.0 15.0

-- | Toggle switch turning on.
toggleOn :: HapticPulse
toggleOn = pulse 3.0 12.0

-- | Toggle switch turning off.
toggleOff :: HapticPulse
toggleOff = pulse 2.0 8.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // preset effects — notifications
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light notification — gentle alert.
notificationLight :: HapticVibration
notificationLight = vibration 150.0 0.5 100.0

-- | Medium notification — standard alert.
notificationMedium :: HapticVibration
notificationMedium = vibration 200.0 1.0 200.0

-- | Strong notification — urgent alert.
notificationStrong :: HapticVibration
notificationStrong = vibration 250.0 2.0 300.0

-- | Warning buzz — attention required.
warningBuzz :: HapticVibration
warningBuzz = vibration 100.0 3.0 500.0

-- | Error buzz — something went wrong.
errorBuzz :: HapticVibration
errorBuzz = vibration 80.0 4.0 400.0

-- | Success pulse — operation completed.
successPulse :: HapticVibration
successPulse = vibration 250.0 1.5 150.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // preset effects — textures
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smooth surface — minimal texture.
smoothSurface :: HapticTexture
smoothSurface = texture 300.0 0.1 0.2

-- | Rough surface — noticeable texture.
roughSurface :: HapticTexture
roughSurface = texture 200.0 0.5 0.5

-- | Sandpaper — coarse texture.
sandpaper :: HapticTexture
sandpaper = texture 150.0 0.8 0.8

-- | Corduroy — periodic ridges.
corduroy :: HapticTexture
corduroy = texture 50.0 0.6 0.6

-- | Bumpy road — low frequency, high amplitude.
bumpyRoad :: HapticTexture
bumpyRoad = texture 20.0 0.9 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // preset effects — impacts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light tap — gentle touch.
lightTap :: HapticImpact
lightTap = impact 1.0 2.0 10.0

-- | Medium impact — normal collision.
mediumImpact :: HapticImpact
mediumImpact = impact 5.0 5.0 30.0

-- | Heavy impact — strong collision.
heavyImpact :: HapticImpact
heavyImpact = impact 15.0 8.0 50.0

-- | Full collision — maximum impact.
collision :: HapticImpact
collision = impact 30.0 3.0 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // preset effects — resistance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Free spin — no resistance (free movement).
freeSpin :: HapticResistance
freeSpin = resistance 0.0 0.0 0.0

-- | Light resistance — slight pushback.
lightResistance :: HapticResistance
lightResistance = resistance 1.0 0.5 5.0

-- | Medium resistance — noticeable pushback.
mediumResistance :: HapticResistance
mediumResistance = resistance 5.0 2.0 20.0

-- | Heavy resistance — strong pushback.
heavyResistance :: HapticResistance
heavyResistance = resistance 15.0 5.0 50.0

-- | Hard stop — cannot move past this point.
hardStop :: HapticResistance
hardStop = resistance 100.0 20.0 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale a force by a factor.
scaleForce :: Number -> Force -> Force
scaleForce factor (Force n) = forceUnsafe (n * factor)

-- | Scale a torque by a factor.
scaleTorque :: Number -> Torque -> Torque
scaleTorque factor (Torque n) = torqueUnsafe (n * factor)

-- | Combine two forces (simple addition).
combineForces :: Force -> Force -> Force
combineForces (Force a) (Force b) = forceUnsafe (a + b)

-- | Check if force is above human perception threshold (~0.01 N).
isPerceptible :: Force -> Boolean
isPerceptible (Force n) = n > 0.01

-- | Check if force is within comfortable range (< 50 N).
isComfortable :: Force -> Boolean
isComfortable (Force n) = n >= 0.0 && n <= 50.0
