━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                // 24 // storage
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Storage Pillar

Browser storage APIs represented as pure ADT operations.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Storage/`
- **Files**: 4 modules
- **Key features**: Clipboard, LocalStorage, SessionStorage, IndexedDB

## Purpose

Storage operations are represented as pure data structures describing intent.
The runtime interprets these against actual browser APIs. This enables:
- Testability without browser dependencies
- Serialization of storage intents
- Operation batching and conflict detection
- Deterministic operation sequencing

────────────────────────────────────────────────────────────────────────────────
                                                                 // clipboard
────────────────────────────────────────────────────────────────────────────────

## Clipboard

Type-safe representation of browser Clipboard API operations.

### MimeType Enum

| Constructor | String Value | Category |
|-------------|--------------|----------|
| `TextPlain` | `"text/plain"` | text |
| `TextHtml` | `"text/html"` | text |
| `TextRtf` | `"text/rtf"` | text |
| `ImagePng` | `"image/png"` | image |
| `ImageJpeg` | `"image/jpeg"` | image |
| `ImageGif` | `"image/gif"` | image |
| `ImageSvg` | `"image/svg+xml"` | image |
| `ImageWebp` | `"image/webp"` | image |
| `ApplicationJson` | `"application/json"` | application |
| `CustomMimeType String` | custom | custom |

**Predicates:** `isTextMimeType`, `isImageMimeType`

### ClipboardItem

| Constructor | Description |
|-------------|-------------|
| `TextItem String` | Plain text content |
| `HtmlItem String` | HTML markup |
| `ImageItem Int` | Image (size in bytes) |
| `BinaryItem MimeType Int` | Binary data with MIME type |

### ClipboardContents

```purescript
type ClipboardContents = { items :: Array ClipboardItem }
```

**Operations:**
- `emptyClipboard` — Empty clipboard
- `hasTextContent`, `hasImageContent` — Content checks
- `firstTextItem`, `firstImageItem` — Content access

### ClipboardOp

| Constructor | Description |
|-------------|-------------|
| `ReadClipboard` | Read all contents |
| `WriteClipboard ClipboardContents` | Write contents |
| `WriteTextOp String` | Write plain text (shorthand) |
| `ReadTextOp` | Read plain text (shorthand) |

**All operations require permission.**

### ClipboardError

| Constructor | Description |
|-------------|-------------|
| `ClipboardNotSupported` | API not available |
| `PermissionDenied` | User denied access |
| `ReadFailed String` | Read operation failed |
| `WriteFailed String` | Write operation failed |
| `InvalidData String` | Invalid data format |
| `FocusRequired` | Window must be focused |

### ClipboardPermission

| Constructor | String Value | Description |
|-------------|--------------|-------------|
| `PermissionGranted` | `"granted"` | Access allowed |
| `PermissionDeniedState` | `"denied"` | Explicitly denied |
| `PermissionPrompt` | `"prompt"` | Not yet requested |

────────────────────────────────────────────────────────────────────────────────
                                                            // local storage
────────────────────────────────────────────────────────────────────────────────

## Local Storage

ADT operations for browser localStorage API.

### StorageKey

```purescript
newtype StorageKey = StorageKey String  -- Non-empty
```

**Convention:** Use namespaced keys: `"hydrogen:user:preferences"`

**Operations:**
- `storageKey :: String -> Maybe StorageKey` — Validates non-empty
- `storageKeyNamespace` — Extract namespace before first `:`

### StorageValue

```purescript
newtype StorageValue = StorageValue String
```

localStorage only stores strings. JSON serialization happens at higher layer.

### LocalStorageOp

| Constructor | Description | Returns |
|-------------|-------------|---------|
| `GetItem StorageKey` | Read value | `Maybe StorageValue` |
| `SetItem StorageKey StorageValue` | Write value | `Unit` |
| `RemoveItem StorageKey` | Delete key | `Unit` |
| `Clear` | Delete all | `Unit` |
| `HasItem StorageKey` | Check existence | `Boolean` |
| `GetAllKeys` | List keys | `Array StorageKey` |

**Introspection:**
- `opIsRead` — GetItem, HasItem, GetAllKeys
- `opIsWrite` — SetItem, RemoveItem, Clear
- `opIsDestructive` — RemoveItem, Clear
- `opKey` — Get key involved in operation

### LocalStorageError

| Constructor | Description |
|-------------|-------------|
| `StorageNotAvailable` | localStorage not supported |
| `QuotaExceeded` | Storage quota exceeded |
| `SecurityError` | Access denied (private browsing) |
| `SerializationError String` | Serialize/deserialize failed |
| `KeyNotFound StorageKey` | Key doesn't exist |

### StorageResult

```purescript
type StorageResult a = Either LocalStorageError a
```

────────────────────────────────────────────────────────────────────────────────
                                                          // session storage
────────────────────────────────────────────────────────────────────────────────

## Session Storage

Same API as Local Storage, but data persists only for the session.

Differences from localStorage:
- Cleared when tab/window closes
- Not shared between tabs
- Same storage limit (~5MB)

────────────────────────────────────────────────────────────────────────────────
                                                               // indexed db
────────────────────────────────────────────────────────────────────────────────

## IndexedDB

ADT operations for browser IndexedDB API (structured storage).

IndexedDB provides:
- Object store with indexes
- Transactional operations
- Larger storage limits
- Async operations

*(Module defines types for database operations, stores, indexes, and cursors)*

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

## Source Files

```
src/Hydrogen/Schema/Storage/
├── Clipboard.purs    # Clipboard API types and operations
├── IndexedDB.purs    # IndexedDB types and operations
├── Local.purs        # localStorage types and operations
└── Session.purs      # sessionStorage types and operations
```

4 files, ~1,000 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Storage as ADT

**The Problem:**

Browser storage APIs are effectful:
- They have side effects (write to disk/memory)
- They can fail (quota, permissions, availability)
- They're async (especially IndexedDB)

**The Solution:**

Represent operations as pure data:

```purescript
-- Intent (pure data)
let op = SetItem (storageKey "theme") (storageValue "dark")

-- Execution (effectful, handled by runtime)
result <- executeStorageOp op
```

**Benefits at billion-agent scale:**

1. **Composability** — Agents can build operation sequences algebraically
2. **Testability** — Test storage logic without browser
3. **Batching** — Runtime can optimize multiple operations
4. **Logging** — All intents are serializable, auditable
5. **Error handling** — Errors are typed, explicit, matchable

**No FFI in UI components.** Storage operations are data.
The runtime interprets them against reality.

────────────────────────────────────────────────────────────────────────────────
