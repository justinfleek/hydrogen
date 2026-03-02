-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // motion // effects // misc
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Miscellaneous Simulation Effects — Ball Action, Bubbles, and Star Burst.
-- |
-- | ## Industry Standard
-- |
-- | - **CC Ball Action**: Ball grid effect
-- | - **CC Bubbles**: Rising bubbles effect
-- | - **CC Star Burst**: Star burst effect
-- |
-- | ## GPU Simulation
-- |
-- | These effects use GPU instancing for efficient particle rendering.

module Hydrogen.Schema.Motion.Effects.Simulation.Misc
  ( -- * CC Ball Action
    BallActionEffect
  , defaultBallAction
  , ballActionWithGrid
  
  -- * CC Bubbles
  , BubblesEffect
  , defaultBubbles
  , bubblesWithSize
  
  -- * CC Star Burst
  , StarBurstEffect
  , defaultStarBurst
  , starBurstWithCount
  
  -- * Effect Names
  , ballActionEffectName
  , bubblesEffectName
  , starBurstEffectName
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<)
  , (>)
  , otherwise
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Motion.Composition (BlendMode(BMAdd))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // ball // action
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Ball Action Effect — grid of balls.
-- |
-- | Divides layer into grid and displaces as balls.
type BallActionEffect =
  { -- Grid
    gridSpacing :: Number            -- ^ Grid cell size (1-100)
  , ballSize :: Number               -- ^ Ball size (0-100)
  
  -- Scatter
  , scatterPosition :: Point2D       -- ^ Scatter center
  , scatterAmount :: Number          -- ^ Scatter strength (0-100)
  
  -- Twist
  , twistAngle :: Number             -- ^ Twist amount (-180 to 180)
  , twistAmount :: Number            -- ^ Twist strength (0-100)
  
  -- Appearance
  , useSourceAlpha :: Boolean        -- ^ Use source alpha
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default ball action.
defaultBallAction :: BallActionEffect
defaultBallAction =
  { gridSpacing: 10.0
  , ballSize: 80.0
  , scatterPosition: point2D 100.0 100.0
  , scatterAmount: 0.0
  , twistAngle: 0.0
  , twistAmount: 0.0
  , useSourceAlpha: false
  , randomSeed: 0
  }

-- | Create ball action with specific grid.
ballActionWithGrid :: Number -> Number -> BallActionEffect
ballActionWithGrid spacing size =
  { gridSpacing: clampNumber 1.0 100.0 spacing
  , ballSize: clampNumber 0.0 100.0 size
  , scatterPosition: point2D 100.0 100.0
  , scatterAmount: 0.0
  , twistAngle: 0.0
  , twistAmount: 0.0
  , useSourceAlpha: false
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // bubbles
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Bubbles Effect — simple rising bubbles.
type BubblesEffect =
  { bubbleAmount :: Number           -- ^ Bubble density (0-100)
  , bubbleSize :: Number             -- ^ Bubble size (1-100)
  , bubbleSpeed :: Number            -- ^ Rise speed (0-100)
  , wobbleAmount :: Number           -- ^ Wobble strength (0-100)
  , spreadAmount :: Number           -- ^ Horizontal spread (0-100)
  , groundHeight :: Number           -- ^ Where bubbles start (0-100 %)
  , reflectionStrength :: Number     -- ^ Bubble reflection (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default bubbles.
defaultBubbles :: BubblesEffect
defaultBubbles =
  { bubbleAmount: 50.0
  , bubbleSize: 20.0
  , bubbleSpeed: 50.0
  , wobbleAmount: 30.0
  , spreadAmount: 50.0
  , groundHeight: 100.0
  , reflectionStrength: 50.0
  , randomSeed: 0
  }

-- | Create bubbles with specific size.
bubblesWithSize :: Number -> Number -> BubblesEffect
bubblesWithSize amount size =
  { bubbleAmount: clampNumber 0.0 100.0 amount
  , bubbleSize: clampNumber 1.0 100.0 size
  , bubbleSpeed: 50.0
  , wobbleAmount: 30.0
  , spreadAmount: 50.0
  , groundHeight: 100.0
  , reflectionStrength: 50.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // star // burst
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Star Burst Effect — radial star/streak burst.
type StarBurstEffect =
  { center :: Point2D                -- ^ Burst center
  , starCount :: Int                 -- ^ Number of stars (1-10000)
  , starSize :: Number               -- ^ Star size (0-100)
  , starLength :: Number             -- ^ Streak length (0-500)
  , speed :: Number                  -- ^ Animation speed (0-100)
  , rotation :: Number               -- ^ Burst rotation (0-360)
  , randomness :: Number             -- ^ Random variation (0-100)
  , color :: RGB                     -- ^ Star color
  , opacity :: Number                -- ^ Star opacity (0-100)
  , transferMode :: BlendMode        -- ^ Blend mode
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default star burst.
defaultStarBurst :: StarBurstEffect
defaultStarBurst =
  { center: point2D 100.0 100.0
  , starCount: 50
  , starSize: 5.0
  , starLength: 100.0
  , speed: 50.0
  , rotation: 0.0
  , randomness: 30.0
  , color: rgb 255 255 255
  , opacity: 100.0
  , transferMode: BMAdd
  , randomSeed: 0
  }

-- | Create star burst with specific count.
starBurstWithCount :: Int -> Number -> StarBurstEffect
starBurstWithCount count length' =
  { center: point2D 100.0 100.0
  , starCount: clampInt 1 10000 count
  , starSize: 5.0
  , starLength: clampNumber 0.0 500.0 length'
  , speed: 50.0
  , rotation: 0.0
  , randomness: 30.0
  , color: rgb 255 255 255
  , opacity: 100.0
  , transferMode: BMAdd
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Ball Action.
ballActionEffectName :: BallActionEffect -> String
ballActionEffectName _ = "CC Ball Action"

-- | Effect name for Bubbles.
bubblesEffectName :: BubblesEffect -> String
bubblesEffectName _ = "CC Bubbles"

-- | Effect name for Star Burst.
starBurstEffectName :: StarBurstEffect -> String
starBurstEffectName _ = "CC Star Burst"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp integer to bounds.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n
