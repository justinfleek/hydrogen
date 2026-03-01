-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // dimension // device
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Device-dependent units - measurements that depend on display hardware.
-- |
-- | A pixel has no inherent physical size. A "1920px" image could be:
-- | - 20 inches wide on a 96 PPI monitor
-- | - 13 inches wide on a 144 PPI laptop
-- | - 200 inches wide on a projector
-- |
-- | ## Unit Distinctions
-- |
-- | - **DevicePixel**: Actual hardware pixels on the display
-- | - **CSSPixel**: Reference pixel at 96 PPI (CSS spec)
-- | - **Pixel**: Generic discrete pixel (context determines meaning)
-- |
-- | ## Conversion Requires Context
-- |
-- | To convert between device units and physical units, you need:
-- | - PPI (pixels per inch) of the display
-- | - Device pixel ratio (for HiDPI/Retina displays)
-- |
-- | See `Dimension.Context` for conversion functions.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Device.Types` - Core pixel and display property types
-- | - `Device.Operations` - Constructors, operations, accessors, conversions
-- | - `Device.Profile` - Device profiles and capabilities

module Hydrogen.Schema.Dimension.Device
  ( module Types
  , module Operations
  , module Profile
  ) where

import Hydrogen.Schema.Dimension.Device.Types as Types
import Hydrogen.Schema.Dimension.Device.Operations as Operations
import Hydrogen.Schema.Dimension.Device.Profile as Profile
