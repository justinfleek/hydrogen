-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // dimension // device // profile
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Device profiles for viewport initialization.
-- |
-- | Contains complete hardware characteristics needed to properly configure
-- | a viewport for a specific device, including:
-- | - Form factor classification
-- | - Viewport dimensions
-- | - Pixel density and device pixel ratio
-- | - Safe area insets (notch, home indicator, etc.)
-- | - Input/output capabilities (touch, stylus, haptics, etc.)

module Hydrogen.Schema.Dimension.Device.Profile
  ( -- * Device Form Factor
    DeviceFormFactor
      ( FormFactorPhone
      , FormFactorTablet
      , FormFactorWatch
      , FormFactorDesktop
      , FormFactorTV
      , FormFactorXR
      )
  
  -- * Device Capabilities
  , DeviceCapabilities
  
  -- * Device Profile
  , DeviceProfile
  , deviceProfile
  
  -- * Common Device Profiles
  , iPhoneProfile
  , iPhone15ProProfile
  , iPadProfile
  , iPadProProfile
  , galaxyS24Profile
  , galaxyWatchProfile
  , pixelProfile
  , macBookProfile
  , desktopProfile
  
  -- * Device Profile Accessors
  , profileWidth
  , profileHeight
  , profileDpr
  , profilePpi
  , profileSafeArea
  , profileCapabilities
  , profileFormFactor
  , supportsTouch
  , supportsStylus
  , supportsHaptics
  , supportsFaceID
  , supportsForceTouch
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Hydrogen.Schema.Dimension.Device.Types
  ( Pixel(Pixel)
  , PixelsPerInch(PixelsPerInch)
  , DevicePixelRatio(DevicePixelRatio)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // device form factor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Device form factor classification.
data DeviceFormFactor
  = FormFactorPhone     -- ^ Smartphone (iPhone, Android phone)
  | FormFactorTablet    -- ^ Tablet (iPad, Android tablet)
  | FormFactorWatch     -- ^ Smartwatch (Apple Watch, Galaxy Watch)
  | FormFactorDesktop   -- ^ Desktop/laptop computer
  | FormFactorTV        -- ^ Television or large display
  | FormFactorXR        -- ^ AR/VR headset (Vision Pro, Quest)

derive instance eqDeviceFormFactor :: Eq DeviceFormFactor
derive instance ordDeviceFormFactor :: Ord DeviceFormFactor

instance showDeviceFormFactor :: Show DeviceFormFactor where
  show FormFactorPhone = "(DeviceFormFactor Phone)"
  show FormFactorTablet = "(DeviceFormFactor Tablet)"
  show FormFactorWatch = "(DeviceFormFactor Watch)"
  show FormFactorDesktop = "(DeviceFormFactor Desktop)"
  show FormFactorTV = "(DeviceFormFactor TV)"
  show FormFactorXR = "(DeviceFormFactor XR)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // device capabilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Device input and feedback capabilities.
-- |
-- | Tracks what input methods and feedback mechanisms a device supports.
-- | Used by gestural and haptic modules to enable appropriate interactions.
type DeviceCapabilities =
  { touch :: Boolean          -- ^ Multi-touch input
  , stylus :: Boolean         -- ^ Stylus/pen input (tablet stylus)
  , haptics :: Boolean        -- ^ Haptic feedback (Taptic Engine, vibration)
  , forceTouch :: Boolean     -- ^ Pressure-sensitive touch (3D Touch, Force Touch)
  , faceID :: Boolean         -- ^ Face recognition (Face ID)
  , touchID :: Boolean        -- ^ Fingerprint recognition (Touch ID)
  , lidar :: Boolean          -- ^ LiDAR depth sensor
  , spatialAudio :: Boolean   -- ^ Spatial audio support
  , hdr :: Boolean            -- ^ HDR display support
  , proMotion :: Boolean      -- ^ Variable refresh rate (ProMotion)
  , alwaysOnDisplay :: Boolean -- ^ Always-on display capability
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // device profiles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete device profile for viewport initialization.
-- |
-- | Contains all hardware characteristics needed to properly configure
-- | a viewport for a specific device.
type DeviceProfile =
  { name :: String                  -- ^ Device name (e.g., "iPhone 15 Pro")
  , formFactor :: DeviceFormFactor  -- ^ Device category
  , width :: Pixel                  -- ^ Logical viewport width
  , height :: Pixel                 -- ^ Logical viewport height
  , devicePixelRatio :: DevicePixelRatio  -- ^ DPR for retina scaling
  , ppi :: PixelsPerInch            -- ^ Physical pixel density
  , safeAreaTop :: Pixel            -- ^ Top safe area (notch, Dynamic Island)
  , safeAreaRight :: Pixel          -- ^ Right safe area
  , safeAreaBottom :: Pixel         -- ^ Bottom safe area (home indicator)
  , safeAreaLeft :: Pixel           -- ^ Left safe area
  , capabilities :: DeviceCapabilities  -- ^ Input/output capabilities
  }

-- | Create a device profile with all parameters.
deviceProfile 
  :: String 
  -> DeviceFormFactor 
  -> Pixel -> Pixel 
  -> DevicePixelRatio 
  -> PixelsPerInch
  -> Pixel -> Pixel -> Pixel -> Pixel
  -> DeviceCapabilities
  -> DeviceProfile
deviceProfile name formFactor width height ratio density saTop saRight saBottom saLeft caps =
  { name
  , formFactor
  , width
  , height
  , devicePixelRatio: ratio
  , ppi: density
  , safeAreaTop: saTop
  , safeAreaRight: saRight
  , safeAreaBottom: saBottom
  , safeAreaLeft: saLeft
  , capabilities: caps
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // capability definitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default phone capabilities
phoneCapabilities :: DeviceCapabilities
phoneCapabilities =
  { touch: true
  , stylus: false
  , haptics: true
  , forceTouch: false
  , faceID: false
  , touchID: false
  , lidar: false
  , spatialAudio: false
  , hdr: true
  , proMotion: false
  , alwaysOnDisplay: false
  }

-- | iPhone 15 Pro capabilities (flagship)
iPhoneProCapabilities :: DeviceCapabilities
iPhoneProCapabilities =
  { touch: true
  , stylus: false
  , haptics: true
  , forceTouch: false  -- Removed in iPhone 11
  , faceID: true
  , touchID: false
  , lidar: true
  , spatialAudio: true
  , hdr: true
  , proMotion: true
  , alwaysOnDisplay: true
  }

-- | iPad Pro capabilities
iPadProCapabilities :: DeviceCapabilities
iPadProCapabilities =
  { touch: true
  , stylus: true   -- tablet stylus support
  , haptics: false -- iPads don't have Taptic Engine
  , forceTouch: false
  , faceID: true
  , touchID: false
  , lidar: true
  , spatialAudio: true
  , hdr: true
  , proMotion: true
  , alwaysOnDisplay: false
  }

-- | Galaxy Watch capabilities
watchCapabilities :: DeviceCapabilities
watchCapabilities =
  { touch: true
  , stylus: false
  , haptics: true
  , forceTouch: false
  , faceID: false
  , touchID: false
  , lidar: false
  , spatialAudio: false
  , hdr: false
  , proMotion: false
  , alwaysOnDisplay: true
  }

-- | Desktop capabilities
desktopCapabilities :: DeviceCapabilities
desktopCapabilities =
  { touch: false
  , stylus: false
  , haptics: false
  , forceTouch: false
  , faceID: false
  , touchID: false
  , lidar: false
  , spatialAudio: false
  , hdr: true
  , proMotion: false
  , alwaysOnDisplay: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // common device profiles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic iPhone profile (iPhone 13/14 standard)
iPhoneProfile :: DeviceProfile
iPhoneProfile = deviceProfile
  "iPhone"
  FormFactorPhone
  (Pixel 390.0) (Pixel 844.0)   -- Logical points
  (DevicePixelRatio 3.0)        -- 3x Retina
  (PixelsPerInch 460.0)         -- Super Retina XDR
  (Pixel 47.0)                  -- Status bar + notch
  (Pixel 0.0)
  (Pixel 34.0)                  -- Home indicator
  (Pixel 0.0)
  phoneCapabilities

-- | iPhone 15 Pro profile
iPhone15ProProfile :: DeviceProfile
iPhone15ProProfile = deviceProfile
  "iPhone 15 Pro"
  FormFactorPhone
  (Pixel 393.0) (Pixel 852.0)   -- Slightly larger
  (DevicePixelRatio 3.0)
  (PixelsPerInch 460.0)
  (Pixel 59.0)                  -- Dynamic Island
  (Pixel 0.0)
  (Pixel 34.0)
  (Pixel 0.0)
  iPhoneProCapabilities

-- | Standard iPad profile (10.9" iPad)
iPadProfile :: DeviceProfile
iPadProfile = deviceProfile
  "iPad"
  FormFactorTablet
  (Pixel 820.0) (Pixel 1180.0)
  (DevicePixelRatio 2.0)
  (PixelsPerInch 264.0)
  (Pixel 24.0)                  -- Status bar
  (Pixel 0.0)
  (Pixel 20.0)                  -- Home indicator
  (Pixel 0.0)
  phoneCapabilities             -- Basic iPad

-- | iPad Pro 12.9" profile
iPadProProfile :: DeviceProfile
iPadProProfile = deviceProfile
  "iPad Pro 12.9"
  FormFactorTablet
  (Pixel 1024.0) (Pixel 1366.0)
  (DevicePixelRatio 2.0)
  (PixelsPerInch 264.0)
  (Pixel 24.0)
  (Pixel 0.0)
  (Pixel 20.0)
  (Pixel 0.0)
  iPadProCapabilities

-- | Samsung Galaxy S24 profile
galaxyS24Profile :: DeviceProfile
galaxyS24Profile = deviceProfile
  "Galaxy S24"
  FormFactorPhone
  (Pixel 360.0) (Pixel 780.0)   -- Android logical pixels
  (DevicePixelRatio 3.0)
  (PixelsPerInch 425.0)
  (Pixel 28.0)                  -- Status bar
  (Pixel 0.0)
  (Pixel 16.0)                  -- Navigation hint
  (Pixel 0.0)
  phoneCapabilities

-- | Samsung Galaxy Watch profile
galaxyWatchProfile :: DeviceProfile
galaxyWatchProfile = deviceProfile
  "Galaxy Watch"
  FormFactorWatch
  (Pixel 396.0) (Pixel 396.0)   -- Circular, 1.4" display
  (DevicePixelRatio 2.0)
  (PixelsPerInch 330.0)
  (Pixel 0.0)                   -- No safe area on circular
  (Pixel 0.0)
  (Pixel 0.0)
  (Pixel 0.0)
  watchCapabilities

-- | Google Pixel profile
pixelProfile :: DeviceProfile
pixelProfile = deviceProfile
  "Pixel 8"
  FormFactorPhone
  (Pixel 412.0) (Pixel 915.0)
  (DevicePixelRatio 2.625)      -- Android's weird DPR
  (PixelsPerInch 428.0)
  (Pixel 24.0)
  (Pixel 0.0)
  (Pixel 16.0)
  (Pixel 0.0)
  phoneCapabilities

-- | MacBook Pro profile
macBookProfile :: DeviceProfile
macBookProfile = deviceProfile
  "MacBook Pro 14"
  FormFactorDesktop
  (Pixel 1512.0) (Pixel 982.0)  -- Scaled resolution
  (DevicePixelRatio 2.0)
  (PixelsPerInch 254.0)
  (Pixel 0.0)                   -- No notch in logical space
  (Pixel 0.0)
  (Pixel 0.0)
  (Pixel 0.0)
  desktopCapabilities

-- | Generic desktop profile (1080p at standard DPR)
desktopProfile :: DeviceProfile
desktopProfile = deviceProfile
  "Desktop 1080p"
  FormFactorDesktop
  (Pixel 1920.0) (Pixel 1080.0)
  (DevicePixelRatio 1.0)
  (PixelsPerInch 96.0)
  (Pixel 0.0)
  (Pixel 0.0)
  (Pixel 0.0)
  (Pixel 0.0)
  desktopCapabilities

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // device profile accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get profile viewport width.
profileWidth :: DeviceProfile -> Pixel
profileWidth p = p.width

-- | Get profile viewport height.
profileHeight :: DeviceProfile -> Pixel
profileHeight p = p.height

-- | Get profile device pixel ratio.
profileDpr :: DeviceProfile -> DevicePixelRatio
profileDpr p = p.devicePixelRatio

-- | Get profile pixels per inch.
profilePpi :: DeviceProfile -> PixelsPerInch
profilePpi p = p.ppi

-- | Get profile safe area insets.
profileSafeArea :: DeviceProfile -> { top :: Pixel, right :: Pixel, bottom :: Pixel, left :: Pixel }
profileSafeArea p =
  { top: p.safeAreaTop
  , right: p.safeAreaRight
  , bottom: p.safeAreaBottom
  , left: p.safeAreaLeft
  }

-- | Get profile capabilities.
profileCapabilities :: DeviceProfile -> DeviceCapabilities
profileCapabilities p = p.capabilities

-- | Get profile form factor.
profileFormFactor :: DeviceProfile -> DeviceFormFactor
profileFormFactor p = p.formFactor

-- | Check if device supports touch input.
supportsTouch :: DeviceProfile -> Boolean
supportsTouch p = p.capabilities.touch

-- | Check if device supports stylus input.
supportsStylus :: DeviceProfile -> Boolean
supportsStylus p = p.capabilities.stylus

-- | Check if device supports haptic feedback.
supportsHaptics :: DeviceProfile -> Boolean
supportsHaptics p = p.capabilities.haptics

-- | Check if device supports Face ID.
supportsFaceID :: DeviceProfile -> Boolean
supportsFaceID p = p.capabilities.faceID

-- | Check if device supports force/3D touch.
supportsForceTouch :: DeviceProfile -> Boolean
supportsForceTouch p = p.capabilities.forceTouch
