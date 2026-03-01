-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // reactive // feedback // queue
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NotificationQueue - queue management compound.
-- |
-- | Manages a queue of toast notifications, ensuring orderly
-- | display and automatic dequeuing when notifications expire.

module Hydrogen.Schema.Reactive.Feedback.Queue
  ( -- * Notification Queue (Compound)
    NotificationQueue
  , emptyQueue
  , enqueue
  , dequeue
  , queueLength
  , currentNotification
  ) where

import Data.Array (drop, head, length, snoc)
import Data.Maybe (Maybe)

import Hydrogen.Schema.Reactive.Feedback.Toast (Toast)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // notification queue compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Queue of pending notifications
type NotificationQueue =
  { items :: Array Toast
  , maxVisible :: Int
  }

-- | Empty notification queue
emptyQueue :: Int -> NotificationQueue
emptyQueue maxVisible =
  { items: []
  , maxVisible
  }

-- | Add notification to queue
enqueue :: Toast -> NotificationQueue -> NotificationQueue
enqueue item queue =
  queue { items = snoc queue.items item }

-- | Remove oldest notification
dequeue :: NotificationQueue -> NotificationQueue
dequeue queue =
  queue { items = drop 1 queue.items }

-- | Get queue length
queueLength :: NotificationQueue -> Int
queueLength queue = length queue.items

-- | Get current notification (head of queue)
currentNotification :: NotificationQueue -> Maybe Toast
currentNotification queue = head queue.items
