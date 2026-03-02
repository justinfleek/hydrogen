-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // media // upload
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Upload — Pure file upload state and types.
-- |
-- | ## Design Philosophy
-- |
-- | File upload is modeled as pure state transitions. No File API or
-- | XMLHttpRequest/fetch calls leak into this module. The runtime
-- | interprets upload state against actual browser APIs.
-- |
-- | This enables:
-- | - Deterministic upload UI testing
-- | - Server-side upload state planning
-- | - Agent composition of upload interfaces
-- |
-- | ## Bounded Types
-- |
-- | - Progress: [0.0, 1.0] clamped
-- | - FileSize: non-negative bytes
-- | - Chunk progress: [0, total chunks]
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (bounded type foundations)
-- | - Hydrogen.Schema.Temporal.Duration (estimated time)
-- |
-- | ## Dependents
-- |
-- | - Component.FileUpload (file upload UI)
-- | - Component.DropZone (drag-and-drop upload)
-- | - Component.AvatarUpload (avatar upload)

module Hydrogen.Schema.Media.Upload
  ( -- * File ID
    FileId
  , fileId
  , unwrapFileId
  
  -- * Progress
  , Progress
  , progress
  , unwrapProgress
  , progressZero
  , progressComplete
  , progressFromPercent
  , progressToPercent
  , progressBounds
  
  -- * File Size
  , FileSize
  , fileSize
  , fileSizeFromKB
  , fileSizeFromMB
  , unwrapFileSize
  , toKilobytes
  , toMegabytes
  , formatFileSize
  , fileSizeBounds
  
  -- * File Entry
  , FileEntry
  , fileEntry
  , entryId
  , entryName
  , entrySize
  , entryType
  , entryLastModified
  
  -- * Upload Status
  , UploadStatus(Pending, Uploading, Processing, Complete, Failed, Cancelled)
  , isUploading
  , isComplete
  , isFailed
  , isPending
  
  -- * Upload Progress
  , UploadProgress
  , uploadProgress
  , progressLoaded
  , progressTotal
  , progressPercent
  , progressBytesPerSecond
  , estimatedTimeRemaining
  
  -- * Upload State
  , FileUploadState
  , UploadState
  , initialUploadState
  , addFile
  , removeFile
  , clearFiles
  , updateFileProgress
  , updateFileStatus
  , totalProgress
  , pendingCount
  , uploadingCount
  , completedCount
  , failedCount
  
  -- * Upload Command
  , UploadCommand(StartUpload, CancelUpload, RetryUpload, PauseUpload, ResumeUpload, RemoveUpload, ClearCompleted, ClearFailed)
  , applyUploadCommand
  
  -- * Upload Config
  , UploadConfig
  , defaultUploadConfig
  , configMaxFileSize
  , configAllowedTypes
  , configMaxFiles
  , validateFile
  
  -- * Validation
  , ValidationError(FileTooLarge, InvalidFileType, TooManyFiles)
  , validateFileEntry
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)
  , (<>)
  )

import Data.Array (length, snoc, filter, foldl, any, index) as Array
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // file id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a file in an upload session.
-- |
-- | Generated client-side for tracking purposes.
newtype FileId = FileId String

derive instance eqFileId :: Eq FileId
derive instance ordFileId :: Ord FileId

instance showFileId :: Show FileId where
  show (FileId id) = "(FileId " <> id <> ")"

-- | Create a file ID.
fileId :: String -> FileId
fileId = FileId

-- | Unwrap file ID.
unwrapFileId :: FileId -> String
unwrapFileId (FileId id) = id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Upload progress clamped to [0.0, 1.0].
-- |
-- | 0.0 = not started, 1.0 = complete.
newtype Progress = Progress Number

derive instance eqProgress :: Eq Progress
derive instance ordProgress :: Ord Progress

instance showProgress :: Show Progress where
  show (Progress p) = "(Progress " <> show p <> ")"

-- | Create a Progress, clamping to [0.0, 1.0].
progress :: Number -> Progress
progress p
  | p < 0.0 = Progress 0.0
  | p > 1.0 = Progress 1.0
  | otherwise = Progress p

-- | Unwrap progress value.
unwrapProgress :: Progress -> Number
unwrapProgress (Progress p) = p

-- | Zero progress (not started).
progressZero :: Progress
progressZero = Progress 0.0

-- | Complete progress (100%).
progressComplete :: Progress
progressComplete = Progress 1.0

-- | Create from percentage (0-100).
progressFromPercent :: Number -> Progress
progressFromPercent p = progress (p / 100.0)

-- | Convert to percentage (0-100).
progressToPercent :: Progress -> Number
progressToPercent (Progress p) = p * 100.0

-- | Progress bounds documentation.
progressBounds :: Bounded.NumberBounds
progressBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps "progress"
  "Upload progress (0.0 to 1.0)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // file size
-- ═════════════════════════════════════════════════════════════════════════════

-- | File size in bytes, non-negative.
newtype FileSize = FileSize Int

derive instance eqFileSize :: Eq FileSize
derive instance ordFileSize :: Ord FileSize

instance showFileSize :: Show FileSize where
  show fs = formatFileSize fs

-- | Create file size from bytes.
fileSize :: Int -> FileSize
fileSize bytes = FileSize (maxInt 0 bytes)

-- | Create from kilobytes.
fileSizeFromKB :: Int -> FileSize
fileSizeFromKB kb = FileSize (maxInt 0 (kb * 1024))

-- | Create from megabytes.
fileSizeFromMB :: Int -> FileSize
fileSizeFromMB mb = FileSize (maxInt 0 (mb * 1024 * 1024))

-- | Unwrap to bytes.
unwrapFileSize :: FileSize -> Int
unwrapFileSize (FileSize bytes) = bytes

-- | Convert to kilobytes.
toKilobytes :: FileSize -> Number
toKilobytes (FileSize bytes) = Int.toNumber bytes / 1024.0

-- | Convert to megabytes.
toMegabytes :: FileSize -> Number
toMegabytes (FileSize bytes) = Int.toNumber bytes / (1024.0 * 1024.0)

-- | Format file size for display.
formatFileSize :: FileSize -> String
formatFileSize (FileSize bytes)
  | bytes < 1024 = show bytes <> " B"
  | bytes < 1048576 = formatNum (Int.toNumber bytes / 1024.0) <> " KB"
  | bytes < 1073741824 = formatNum (Int.toNumber bytes / 1048576.0) <> " MB"
  | otherwise = formatNum (Int.toNumber bytes / 1073741824.0) <> " GB"

-- | Format number to 2 decimal places (simple implementation).
formatNum :: Number -> String
formatNum n = show (roundTo2 n)

-- | Round to 2 decimal places.
roundTo2 :: Number -> Number
roundTo2 n = 
  let scaled = n * 100.0
      rounded = Int.toNumber (floorNum scaled)
  in rounded / 100.0

-- | Floor a number (simple implementation).
floorNum :: Number -> Int
floorNum n = floorLoop n 0
  where
  floorLoop :: Number -> Int -> Int
  floorLoop x acc
    | x < 1.0 = if x < 0.0 then acc - 1 else acc
    | otherwise = floorLoop (x - 1.0) (acc + 1)

-- | File size bounds documentation.
fileSizeBounds :: Bounded.IntBounds
fileSizeBounds = Bounded.intBounds 0 2147483647 Bounded.Clamps "fileSize"
  "File size in bytes (non-negative)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // file entry
-- ═════════════════════════════════════════════════════════════════════════════

-- | A file entry representing a file selected for upload.
type FileEntry =
  { id :: FileId              -- ^ Unique identifier
  , name :: String            -- ^ File name
  , size :: FileSize          -- ^ File size
  , mimeType :: String        -- ^ MIME type
  , lastModified :: Number    -- ^ Last modified timestamp (ms since epoch)
  }

-- | Create a file entry.
fileEntry :: String -> String -> Int -> String -> FileEntry
fileEntry idStr name sizeBytes mimeType =
  { id: fileId idStr
  , name
  , size: fileSize sizeBytes
  , mimeType
  , lastModified: 0.0
  }

-- | Get file ID.
entryId :: FileEntry -> FileId
entryId f = f.id

-- | Get file name.
entryName :: FileEntry -> String
entryName f = f.name

-- | Get file size.
entrySize :: FileEntry -> FileSize
entrySize f = f.size

-- | Get MIME type.
entryType :: FileEntry -> String
entryType f = f.mimeType

-- | Get last modified timestamp.
entryLastModified :: FileEntry -> Number
entryLastModified f = f.lastModified

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // upload status
-- ═════════════════════════════════════════════════════════════════════════════

-- | Upload status for a single file.
data UploadStatus
  = Pending            -- ^ Waiting to start
  | Uploading          -- ^ Currently uploading
  | Processing         -- ^ Upload complete, server processing
  | Complete           -- ^ Successfully completed
  | Failed String      -- ^ Failed with error message
  | Cancelled          -- ^ Upload was cancelled

derive instance eqUploadStatus :: Eq UploadStatus

instance showUploadStatus :: Show UploadStatus where
  show Pending = "Pending"
  show Uploading = "Uploading"
  show Processing = "Processing"
  show Complete = "Complete"
  show (Failed msg) = "(Failed " <> msg <> ")"
  show Cancelled = "Cancelled"

-- | Check if uploading.
isUploading :: UploadStatus -> Boolean
isUploading Uploading = true
isUploading _ = false

-- | Check if complete.
isComplete :: UploadStatus -> Boolean
isComplete Complete = true
isComplete _ = false

-- | Check if failed.
isFailed :: UploadStatus -> Boolean
isFailed (Failed _) = true
isFailed _ = false

-- | Check if pending.
isPending :: UploadStatus -> Boolean
isPending Pending = true
isPending _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // upload progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Detailed upload progress for a file.
type UploadProgress =
  { loaded :: FileSize         -- ^ Bytes uploaded
  , total :: FileSize          -- ^ Total bytes
  , startTime :: Number        -- ^ Upload start timestamp
  , lastUpdate :: Number       -- ^ Last progress update timestamp
  }

-- | Create upload progress.
uploadProgress :: Int -> Int -> Number -> UploadProgress
uploadProgress loaded total startTime =
  { loaded: fileSize loaded
  , total: fileSize total
  , startTime
  , lastUpdate: startTime
  }

-- | Get loaded bytes.
progressLoaded :: UploadProgress -> FileSize
progressLoaded p = p.loaded

-- | Get total bytes.
progressTotal :: UploadProgress -> FileSize
progressTotal p = p.total

-- | Calculate progress percentage.
progressPercent :: UploadProgress -> Progress
progressPercent p =
  let loaded = Int.toNumber (unwrapFileSize p.loaded)
      total = Int.toNumber (unwrapFileSize p.total)
  in if total <= 0.0
     then progressZero
     else progress (loaded / total)

-- | Calculate bytes per second.
progressBytesPerSecond :: Number -> UploadProgress -> Number
progressBytesPerSecond currentTime p =
  let elapsed = currentTime - p.startTime
      loaded = Int.toNumber (unwrapFileSize p.loaded)
  in if elapsed <= 0.0
     then 0.0
     else loaded / (elapsed / 1000.0)

-- | Estimate remaining time in seconds.
estimatedTimeRemaining :: Number -> UploadProgress -> Number
estimatedTimeRemaining currentTime p =
  let bps = progressBytesPerSecond currentTime p
      remaining = Int.toNumber (unwrapFileSize p.total - unwrapFileSize p.loaded)
  in if bps <= 0.0
     then 0.0
     else remaining / bps

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // upload state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Per-file upload tracking.
type FileUploadState =
  { file :: FileEntry
  , status :: UploadStatus
  , progress :: UploadProgress
  }

-- | Complete upload state for multiple files.
type UploadState =
  { files :: Array FileUploadState
  , maxConcurrent :: Int       -- ^ Max concurrent uploads
  }

-- | Initialize upload state.
initialUploadState :: UploadState
initialUploadState =
  { files: []
  , maxConcurrent: 3
  }

-- | Add a file to upload queue.
addFile :: FileEntry -> UploadState -> UploadState
addFile entry state =
  let newFileState =
        { file: entry
        , status: Pending
        , progress: uploadProgress 0 (unwrapFileSize entry.size) 0.0
        }
  in state { files = Array.snoc state.files newFileState }

-- | Remove a file by ID.
removeFile :: FileId -> UploadState -> UploadState
removeFile fid state =
  state { files = Array.filter (\fs -> fs.file.id /= fid) state.files }

-- | Clear all files.
clearFiles :: UploadState -> UploadState
clearFiles state = state { files = [] }

-- | Update file progress.
updateFileProgress :: FileId -> Int -> Number -> UploadState -> UploadState
updateFileProgress fid loadedBytes currentTime state =
  state { files = updateMatchingFile fid updateFn state.files }
  where
  updateFn fs =
    fs { progress = fs.progress { loaded = fileSize loadedBytes, lastUpdate = currentTime }
       , status = Uploading
       }

-- | Update file status.
updateFileStatus :: FileId -> UploadStatus -> UploadState -> UploadState
updateFileStatus fid newStatus state =
  state { files = updateMatchingFile fid (\fs -> fs { status = newStatus }) state.files }

-- | Update matching file in array.
updateMatchingFile :: FileId -> (FileUploadState -> FileUploadState) -> Array FileUploadState -> Array FileUploadState
updateMatchingFile fid fn files = mapArray updateOne files
  where
  updateOne fs = if fs.file.id == fid then fn fs else fs

-- | Calculate total progress across all files.
totalProgress :: UploadState -> Progress
totalProgress state =
  let sumLoaded = Array.foldl (\acc fs -> acc + unwrapFileSize fs.progress.loaded) 0 state.files
      sumTotal = Array.foldl (\acc fs -> acc + unwrapFileSize fs.progress.total) 0 state.files
  in if sumTotal <= 0
     then progressZero
     else progress (Int.toNumber sumLoaded / Int.toNumber sumTotal)

-- | Count pending files.
pendingCount :: UploadState -> Int
pendingCount state = countMatching isPending state.files

-- | Count uploading files.
uploadingCount :: UploadState -> Int
uploadingCount state = countMatching isUploading state.files

-- | Count completed files.
completedCount :: UploadState -> Int
completedCount state = countMatching isComplete state.files

-- | Count failed files.
failedCount :: UploadState -> Int
failedCount state = countMatching isFailed state.files

-- | Count files matching predicate.
countMatching :: (UploadStatus -> Boolean) -> Array FileUploadState -> Int
countMatching pred files = Array.foldl (\acc fs -> if pred fs.status then acc + 1 else acc) 0 files

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // upload command
-- ═════════════════════════════════════════════════════════════════════════════

-- | Commands for upload management.
data UploadCommand
  = StartUpload FileId         -- ^ Start uploading a file
  | CancelUpload FileId        -- ^ Cancel an upload
  | RetryUpload FileId         -- ^ Retry a failed upload
  | PauseUpload FileId         -- ^ Pause upload (if supported)
  | ResumeUpload FileId        -- ^ Resume paused upload
  | RemoveUpload FileId        -- ^ Remove file from queue
  | ClearCompleted             -- ^ Clear all completed uploads
  | ClearFailed                -- ^ Clear all failed uploads

derive instance eqUploadCommand :: Eq UploadCommand

instance showUploadCommand :: Show UploadCommand where
  show (StartUpload fid) = "(StartUpload " <> show fid <> ")"
  show (CancelUpload fid) = "(CancelUpload " <> show fid <> ")"
  show (RetryUpload fid) = "(RetryUpload " <> show fid <> ")"
  show (PauseUpload fid) = "(PauseUpload " <> show fid <> ")"
  show (ResumeUpload fid) = "(ResumeUpload " <> show fid <> ")"
  show (RemoveUpload fid) = "(RemoveUpload " <> show fid <> ")"
  show ClearCompleted = "ClearCompleted"
  show ClearFailed = "ClearFailed"

-- | Apply upload command to state.
applyUploadCommand :: UploadCommand -> UploadState -> UploadState
applyUploadCommand cmd state = case cmd of
  StartUpload fid -> updateFileStatus fid Uploading state
  CancelUpload fid -> updateFileStatus fid Cancelled state
  RetryUpload fid -> updateFileStatus fid Pending state
  PauseUpload _ -> state  -- Pause not represented in pure state
  ResumeUpload fid -> updateFileStatus fid Uploading state
  RemoveUpload fid -> removeFile fid state
  ClearCompleted -> state { files = Array.filter (\fs -> not (isComplete fs.status)) state.files }
  ClearFailed -> state { files = Array.filter (\fs -> not (isFailed fs.status)) state.files }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // upload config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Upload configuration/constraints.
type UploadConfig =
  { maxFileSize :: FileSize           -- ^ Maximum file size
  , allowedTypes :: Array String      -- ^ Allowed MIME types (empty = all)
  , maxFiles :: Int                   -- ^ Maximum number of files
  , allowMultiple :: Boolean          -- ^ Allow multiple file selection
  }

-- | Default upload configuration.
defaultUploadConfig :: UploadConfig
defaultUploadConfig =
  { maxFileSize: fileSizeFromMB 100   -- 100 MB default
  , allowedTypes: []                  -- All types allowed
  , maxFiles: 10
  , allowMultiple: true
  }

-- | Get max file size.
configMaxFileSize :: UploadConfig -> FileSize
configMaxFileSize c = c.maxFileSize

-- | Get allowed types.
configAllowedTypes :: UploadConfig -> Array String
configAllowedTypes c = c.allowedTypes

-- | Get max files.
configMaxFiles :: UploadConfig -> Int
configMaxFiles c = c.maxFiles

-- | Validate a file against config.
validateFile :: UploadConfig -> FileEntry -> Boolean
validateFile config entry =
  let sizeOk = unwrapFileSize entry.size <= unwrapFileSize config.maxFileSize
      typeOk = Array.length config.allowedTypes == 0 
               || Array.any (\t -> t == entry.mimeType) config.allowedTypes
  in sizeOk && typeOk

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validation errors for file upload.
data ValidationError
  = FileTooLarge FileSize FileSize    -- ^ Actual, Maximum
  | InvalidFileType String            -- ^ Invalid MIME type
  | TooManyFiles Int Int              -- ^ Current, Maximum

derive instance eqValidationError :: Eq ValidationError

instance showValidationError :: Show ValidationError where
  show (FileTooLarge actual maxSize) = 
    "File too large: " <> formatFileSize actual <> " (max: " <> formatFileSize maxSize <> ")"
  show (InvalidFileType mimeType) = 
    "Invalid file type: " <> mimeType
  show (TooManyFiles current maxNum) = 
    "Too many files: " <> show current <> " (max: " <> show maxNum <> ")"

-- | Validate a file entry against config.
validateFileEntry :: UploadConfig -> FileEntry -> Maybe ValidationError
validateFileEntry config entry
  | unwrapFileSize entry.size > unwrapFileSize config.maxFileSize =
      Just (FileTooLarge entry.size config.maxFileSize)
  | Array.length config.allowedTypes > 0 && not (Array.any (\t -> t == entry.mimeType) config.allowedTypes) =
      Just (InvalidFileType entry.mimeType)
  | otherwise = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum of two integers.
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Map over array (pure implementation).
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f arr = mapLoop f arr 0 []
  where
  mapLoop :: (a -> b) -> Array a -> Int -> Array b -> Array b
  mapLoop fn source idx acc =
    case Array.index source idx of
      Nothing -> acc
      Just x -> mapLoop fn source (idx + 1) (Array.snoc acc (fn x))
