-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // runtime // animate // style
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Style Helpers
-- |
-- | Utility functions for generating CSS transform and style strings
-- | from animated values. These helpers convert numeric animation values
-- | into properly formatted CSS strings.
module Hydrogen.Runtime.Animate.Style
  ( -- * Transform Helpers
    translateX
  , translateY
  , translate
  , scale
  , rotate
  
  -- * Style Helpers
  , opacity
  ) where

import Prelude
  ( show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // style // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate translateX transform style value.
translateX :: Number -> String
translateX x = "translateX(" <> show x <> "px)"

-- | Generate translateY transform style value.
translateY :: Number -> String
translateY y = "translateY(" <> show y <> "px)"

-- | Generate translate transform style value.
translate :: Number -> Number -> String
translate x y = "translate(" <> show x <> "px, " <> show y <> "px)"

-- | Generate scale transform style value.
scale :: Number -> String
scale s = "scale(" <> show s <> ")"

-- | Generate rotate transform style value (degrees).
rotate :: Number -> String
rotate deg = "rotate(" <> show deg <> "deg)"

-- | Generate opacity style value.
opacity :: Number -> String
opacity o = show o
