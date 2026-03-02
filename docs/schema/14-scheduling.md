━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             // 14 // scheduling
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Scheduling Pillar

Calendar events, recurrence rules, invitations, RSVP responses, and contacts.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Scheduling/`
- **Files**: 8 modules
- **Lines**: 2,244 total
- **Key features**: RFC 5545 (iCalendar) semantics, cryptographic attestation,
  Google Calendar/Zoom-level granularity

## Purpose

Scheduling provides bounded, deterministic primitives for:
- Calendar events with full metadata (title, description, location, attendees)
- Recurrence rules (daily, weekly, monthly, yearly with RFC 5545 RRULE export)
- Invitations linking contacts to events with role-based access
- RSVP responses (Pending, Accepted, Declined, Tentative, Delegated)
- Contacts (Person, Room, Resource, Group)
- Cryptographically attested scheduling actions for x402 compatibility

## RFC 5545 Compliance

All types follow iCalendar (RFC 5545) semantics for interoperability:
- Events map to VEVENT components
- Recurrence exports as RRULE strings
- RSVP uses PARTSTAT values (NEEDS-ACTION, ACCEPTED, etc.)
- Attendee roles use ROLE parameter (REQ-PARTICIPANT, OPT-PARTICIPANT, etc.)
- Visibility maps to CLASS (PUBLIC, PRIVATE, CONFIDENTIAL)
- Event status maps to STATUS (CONFIRMED, TENTATIVE, CANCELLED)

────────────────────────────────────────────────────────────────────────────────
                                                              // event // atoms
────────────────────────────────────────────────────────────────────────────────

## Event Atoms

Core identity and timing primitives.

### EventId

| Name | Type | Format | Notes |
|------|------|--------|-------|
| EventId | newtype String | UUID5 | Deterministic identifier |

**Key insight:** UUID5 enables deterministic generation from content. Same event
data = same ID, reproducible across agents.

### DateTime

| Field | Type | Min | Max | Notes |
|-------|------|-----|-----|-------|
| year | Int | — | — | Full year (e.g., 2026) |
| month | Int | 1 | 12 | Calendar month |
| day | Int | 1 | 31 | Day of month |
| time | TimeOfDay | — | — | From Temporal pillar |

```purescript
type DateTime =
  { year :: Int
  , month :: Int
  , day :: Int
  , time :: TimeOfDay
  }
```

**Constructor:**
```purescript
makeDateTime :: Int -> Int -> Int -> TimeOfDay -> DateTime
makeDateTime y m d t = { year: y, month: m, day: d, time: t }
```

### Reminder

| Field | Type | Min | Max | Notes |
|-------|------|-----|-----|-------|
| minutesBefore | Int | 0 | ∞ | Minutes before event start |
| method | ReminderMethod | — | — | How to deliver |

```purescript
type Reminder =
  { minutesBefore :: Int
  , method :: ReminderMethod
  }
```

**Common Values:**
- 5 minutes — Last-minute reminder
- 15 minutes — Standard meeting reminder
- 30 minutes — Buffer for travel/prep
- 60 minutes — 1 hour heads-up
- 1440 minutes — Day-before reminder

────────────────────────────────────────────────────────────────────────────────
                                                              // event // enums
────────────────────────────────────────────────────────────────────────────────

## Event Enums

### EventStatus

Event confirmation state.

| Constructor | iCal Value | Description |
|-------------|------------|-------------|
| `Confirmed` | `CONFIRMED` | Event is confirmed and will occur |
| `Tentative` | `TENTATIVE` | Event is provisionally scheduled |
| `Cancelled` | `CANCELLED` | Event has been cancelled |

**State Machine:**
```
Tentative → Confirmed → (completed)
    ↓           ↓
Cancelled   Cancelled
```

### Visibility

Event privacy/access level.

| Constructor | iCal CLASS | Description |
|-------------|------------|-------------|
| `Public` | `PUBLIC` | Visible to everyone with calendar access |
| `Private` | `PRIVATE` | Only visible to invited attendees |
| `Confidential` | `CONFIDENTIAL` | Time shown as busy, details hidden |

**Use Cases:**
- `Public` — Company-wide meetings, public events
- `Private` — 1:1s, personal appointments
- `Confidential` — Sensitive meetings (HR, legal, medical)

### ReminderMethod

How reminders are delivered.

| Constructor | Description |
|-------------|-------------|
| `Email` | Send email notification |
| `Popup` | Display in-app notification |
| `SMS` | Send SMS text message |

### Location

Event location type (sum type, not enum).

| Constructor | Fields | Description |
|-------------|--------|-------------|
| `Physical` | address, room?, instructions? | In-person venue |
| `Virtual` | url, provider?, meetingId?, passcode? | Online meeting |
| `Hybrid` | physical, virtual | Both in-person and online |

```purescript
data Location
  = Physical 
      { address :: String
      , room :: Maybe String
      , instructions :: Maybe String
      }
  | Virtual
      { url :: String
      , provider :: Maybe String  -- "Google Meet", "Zoom", etc.
      , meetingId :: Maybe String
      , passcode :: Maybe String
      }
  | Hybrid
      { physical :: { address :: String, room :: Maybe String }
      , virtual :: { url :: String, provider :: Maybe String }
      }
```

────────────────────────────────────────────────────────────────────────────────
                                                          // event // molecules
────────────────────────────────────────────────────────────────────────────────

## Event Molecule

Full-featured scheduling entity.

```purescript
newtype Event = Event
  { id :: EventId
  , title :: String
  , description :: Maybe String
  , location :: Maybe Location
  , startDateTime :: DateTime
  , endDateTime :: DateTime
  , timezone :: TimezoneId
  , allDay :: Boolean
  , organizerId :: ContactId
  , attendeeIds :: Array ContactId
  , recurrence :: Maybe Recurrence
  , reminders :: Array Reminder
  , status :: EventStatus
  , visibility :: Visibility
  , conferenceLink :: Maybe String
  , createdAt :: DateTime
  , updatedAt :: DateTime
  }
```

### Constructors

| Function | Parameters | Notes |
|----------|------------|-------|
| `event` | id, title, desc?, start, end, tz, organizer, createdAt | Full control |
| `eventAllDay` | id, title, date range, tz, organizer, createdAt | All-day event |
| `eventSimple` | id, title, start (Y/M/D/H/M), end (Y/M/D/H/M), tz, organizer | Most common |

**eventSimple Example:**
```purescript
eventSimple "evt-123" "Team Standup"
  2026 3 1 9 0    -- Start: March 1, 2026 at 9:00
  2026 3 1 9 30   -- End: March 1, 2026 at 9:30
  utc organizer
```

### Accessors

| Function | Return Type | Notes |
|----------|-------------|-------|
| `getId` | EventId | Unique identifier |
| `getTitle` | String | Event title |
| `getDescription` | Maybe String | Optional description |
| `getLocation` | Maybe Location | Physical/Virtual/Hybrid |
| `getStartDateTime` | DateTime | Start time |
| `getEndDateTime` | DateTime | End time |
| `getTimezone` | TimezoneId | Event timezone |
| `isAllDay` | Boolean | All-day flag |
| `getOrganizerId` | ContactId | Creator/owner |
| `getAttendeeIds` | Array ContactId | Invited contacts |
| `getRecurrence` | Maybe Recurrence | Repeat rule |
| `getReminders` | Array Reminder | Reminder list |
| `getStatus` | EventStatus | Confirmed/Tentative/Cancelled |
| `getVisibility` | Visibility | Public/Private/Confidential |
| `getConferenceLink` | Maybe String | Video meeting URL |
| `getCreatedAt` | DateTime | Creation timestamp |
| `getUpdatedAt` | DateTime | Last modification |

────────────────────────────────────────────────────────────────────────────────
                                                           // event // queries
────────────────────────────────────────────────────────────────────────────────

## Event Queries (EventQuery module)

Boolean predicates and computed properties.

### Boolean Predicates

| Function | Description |
|----------|-------------|
| `hasRecurrence` | Event has a recurrence rule |
| `hasConference` | Event has a video conference link |
| `hasAttendees` | Event has attendees (besides organizer) |
| `isMultiDay` | Event spans multiple calendar days |
| `isCancelled` | Event status is Cancelled |
| `isPrivate` | Visibility is Private or Confidential |
| `isSameDay` | Start and end on same calendar day |
| `needsLocation` | No location and no conference link |

### Computed Properties

| Function | Return Type | Formula |
|----------|-------------|---------|
| `getDurationMinutes` | Int | endMinutes - startMinutes |
| `getAttendeeCount` | Int | length(attendeeIds) |
| `getReminderMinutes` | Array Int | map minutesBefore reminders |

**Duration Calculation:**
```purescript
dateTimeToMinutes :: DateTime -> Int
dateTimeToMinutes dt =
  yearMins + monthMins + dayMins + timeMins
  where
    yearMins = dt.year * 525600
    monthMins = dt.month * 43200
    dayMins = dt.day * 1440
    timeMins = TimeOfDay.toMillisOfDay dt.time / 60000
```

────────────────────────────────────────────────────────────────────────────────
                                                         // event // modifiers
────────────────────────────────────────────────────────────────────────────────

## Event Modifiers (EventMod module)

Pure transformation functions.

| Function | Parameters | Notes |
|----------|------------|-------|
| `setLocation` | Event, Location | Set event location |
| `setDescription` | Event, String | Set description |
| `setConferenceLink` | Event, String | Set video meeting URL |
| `addAttendee` | Event, ContactId | Add attendee to list |
| `addReminder` | Event, Reminder | Add reminder to list |
| `setRecurrence` | Event, Recurrence | Set repeat rule |
| `cancel` | Event | Set status to Cancelled |

### Offset Operations

| Function | Return Type | Notes |
|----------|-------------|-------|
| `getStartOffsetMinutes` | Int | Start time as UTC offset |
| `getEndOffsetMinutes` | Int | End time as UTC offset |
| `getTimezoneOffset` | UtcOffset | Event's timezone offset |

### iCalendar Export

```purescript
toICalString :: Event -> String
```

**Example Output:**
```
BEGIN:VEVENT
UID:evt-123
SUMMARY:Team Standup
DTSTART:20260301T090000
DTEND:20260301T093000
STATUS:CONFIRMED
CLASS:PUBLIC
END:VEVENT
```

────────────────────────────────────────────────────────────────────────────────
                                                         // recurrence // atoms
────────────────────────────────────────────────────────────────────────────────

## Recurrence Atoms

Parameters for repeating events.

### Interval

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| interval | Int | 1 | 999 | clamps | Every N periods |

**Common Values:**
- 1 — Every (day/week/month/year)
- 2 — Every other
- 4 — Quarterly (with Monthly frequency)
- 12 — Annually (with Monthly frequency)

### MonthDay

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| monthDay | Int | 1 | 31 | clamps | Day of month for monthly recurrence |

**Edge Cases:**
- Day 31 on months with fewer days: Most systems use last day of month
- Day 29-31 in February: Falls back to Feb 28 (or 29 in leap years)

────────────────────────────────────────────────────────────────────────────────
                                                         // recurrence // enums
────────────────────────────────────────────────────────────────────────────────

## Recurrence Enums

### Frequency

How often the event repeats.

| Constructor | iCal FREQ | Description |
|-------------|-----------|-------------|
| `Daily` | `DAILY` | Every N days |
| `Weekly` | `WEEKLY` | Every N weeks |
| `Monthly` | `MONTHLY` | Every N months |
| `Yearly` | `YEARLY` | Every N years |

### Weekday

Day of week for filtering.

| Constructor | iCal BYDAY | Full Name |
|-------------|------------|-----------|
| `Mon` | `MO` | Monday |
| `Tue` | `TU` | Tuesday |
| `Wed` | `WE` | Wednesday |
| `Thu` | `TH` | Thursday |
| `Fri` | `FR` | Friday |
| `Sat` | `SA` | Saturday |
| `Sun` | `SU` | Sunday |

### EndCondition

When the recurrence stops.

| Constructor | iCal | Description |
|-------------|------|-------------|
| `Never` | — | Repeats indefinitely |
| `Until { year, month, day }` | `UNTIL=YYYYMMDD` | Repeats until date |
| `Count Int` | `COUNT=N` | Repeats N times total |

────────────────────────────────────────────────────────────────────────────────
                                                     // recurrence // molecules
────────────────────────────────────────────────────────────────────────────────

## Recurrence Molecule

Complete recurrence rule.

```purescript
newtype Recurrence = Recurrence
  { frequency :: Frequency
  , interval :: Int
  , weekdays :: Array Weekday
  , monthDay :: Maybe Int
  , endCondition :: EndCondition
  }
```

### Preset Constructors

| Function | Frequency | Interval | Description |
|----------|-----------|----------|-------------|
| `daily` | Daily | 1 | Every day |
| `weekly` | Weekly | 1 | Every week (same weekday) |
| `weeklyOn days` | Weekly | 1 | Every week on specific days |
| `biweekly` | Weekly | 2 | Every two weeks |
| `monthly` | Monthly | 1 | Every month (same day) |
| `monthlyOnDay d` | Monthly | 1 | Every month on day d |
| `yearly` | Yearly | 1 | Every year (same date) |

**Custom Constructor:**
```purescript
custom 
  :: Frequency 
  -> Int           -- interval
  -> Array Weekday -- weekdays filter
  -> Maybe Int     -- monthDay
  -> EndCondition 
  -> Recurrence
```

### Accessors

| Function | Return Type |
|----------|-------------|
| `getFrequency` | Frequency |
| `getInterval` | Int |
| `getWeekdays` | Array Weekday |
| `getMonthDay` | Maybe Int |
| `getEndCondition` | EndCondition |

### Queries

| Function | Return Type | Description |
|----------|-------------|-------------|
| `isInfinite` | Boolean | EndCondition is Never |
| `hasWeekdayFilter` | Boolean | Weekdays array is non-empty |

### Display

| Function | Return Type | Example |
|----------|-------------|---------|
| `toDisplayString` | String | "Weekly on Mon, Wed, Fri" |
| `toRRuleString` | String | "RRULE:FREQ=WEEKLY;BYDAY=MO,WE,FR" |

**RRULE Format:**
```
RRULE:FREQ=WEEKLY;INTERVAL=2;BYDAY=MO,WE,FR;UNTIL=20261231
```

────────────────────────────────────────────────────────────────────────────────
                                                                       // rsvp
────────────────────────────────────────────────────────────────────────────────

## RSVP

Attendee response status.

### RSVP Enum

| Constructor | iCal PARTSTAT | Description |
|-------------|---------------|-------------|
| `Pending` | `NEEDS-ACTION` | No response yet (default) |
| `Accepted` | `ACCEPTED` | Attendee confirmed attendance |
| `Declined` | `DECLINED` | Attendee declined invitation |
| `Tentative` | `TENTATIVE` | Attendee might attend |
| `Delegated` | `DELEGATED` | Attendee delegated to another |

### Queries

| Function | Return Type | True When |
|----------|-------------|-----------|
| `isConfirmed` | Boolean | Accepted or Tentative |
| `isDeclined` | Boolean | Declined |
| `isPending` | Boolean | Pending |
| `needsResponse` | Boolean | Pending (alias) |

### Display

| Function | Return Type | Example |
|----------|-------------|---------|
| `toDisplayString` | String | "Accepted" |
| `toICalString` | String | "ACCEPTED" |

**State Transitions:**
```
Pending → Accepted
       → Declined
       → Tentative
       → Delegated

Tentative → Accepted
         → Declined

(Any state can transition to any other via re-response)
```

────────────────────────────────────────────────────────────────────────────────
                                                                    // contact
────────────────────────────────────────────────────────────────────────────────

## Contact

Person or resource that can attend events.

### ContactId

| Name | Type | Format | Notes |
|------|------|--------|-------|
| ContactId | newtype String | UUID5 or external ID | Deterministic identifier |

### ContactType Enum

| Constructor | Description |
|-------------|-------------|
| `Person` | Individual human attendee |
| `Room` | Physical meeting room |
| `Resource` | Equipment (projector, car, etc.) |
| `Group` | Distribution list or team |

### Contact Molecule

```purescript
newtype Contact = Contact
  { id :: ContactId
  , name :: String
  , email :: Maybe String
  , avatarUrl :: Maybe String
  , contactType :: ContactType
  , timezone :: Maybe TimezoneId
  }
```

### Constructors

| Function | Parameters | Notes |
|----------|------------|-------|
| `contact` | id, name, email?, avatar?, type, tz? | Full control |
| `contactWithId` | idString, name, email?, avatar?, type, tz? | String ID |
| `person` | id, name, email | Most common case |
| `room` | id, name | Meeting room |
| `resource` | id, name | Equipment |
| `group` | id, name, email | Distribution list |

### Accessors

| Function | Return Type |
|----------|-------------|
| `getId` | ContactId |
| `getName` | String |
| `getEmail` | Maybe String |
| `getAvatarUrl` | Maybe String |
| `getContactType` | ContactType |
| `getTimezone` | Maybe TimezoneId |

### Queries

| Function | Return Type | Description |
|----------|-------------|-------------|
| `isPerson` | Boolean | ContactType is Person |
| `isResource` | Boolean | Room, Resource, or Group |
| `hasEmail` | Boolean | Email is Just |
| `hasAvatar` | Boolean | AvatarUrl is Just |

### Display

| Function | Return Type | Example |
|----------|-------------|---------|
| `toDisplayName` | String | "Alice Smith" |
| `toEmailString` | String | "Alice Smith <alice@example.com>" |

────────────────────────────────────────────────────────────────────────────────
                                                                     // invite
────────────────────────────────────────────────────────────────────────────────

## Invite

Links a Contact to an Event with role and RSVP state.

### InviteId

| Name | Type | Format | Notes |
|------|------|--------|-------|
| InviteId | newtype String | UUID5 | Deterministic identifier |

### AttendeeRole Enum

| Constructor | iCal ROLE | Description |
|-------------|-----------|-------------|
| `Organizer` | `ORGANIZER` | Event creator/owner |
| `Required` | `REQ-PARTICIPANT` | Must attend |
| `Optional` | `OPT-PARTICIPANT` | May attend |
| `Chair` | `CHAIR` | Presides over event |
| `NonParticipant` | `NON-PARTICIPANT` | For information only |

### Invite Molecule

```purescript
newtype Invite = Invite
  { id :: InviteId
  , eventId :: String
  , contactId :: ContactId       -- Relational reference
  , contact :: Contact           -- Denormalized snapshot
  , role :: AttendeeRole
  , rsvp :: RSVP
  , sentAt :: Maybe DateTime
  , respondedAt :: Maybe DateTime
  , comment :: Maybe String      -- Response message
  }
```

**Why both contactId and contact?**
- `contactId` is the source of truth for relational queries
- `contact` is a snapshot for display without additional lookups
- Enables efficient rendering while maintaining referential integrity

### Constructors

| Function | Parameters | Notes |
|----------|------------|-------|
| `invite` | id, eventId, contact, role, rsvp, sentAt? | Full control |
| `inviteRequired` | id, eventId, contact | Required attendee, Pending |
| `inviteOptional` | id, eventId, contact | Optional attendee, Pending |
| `inviteOrganizer` | id, eventId, contact | Organizer, auto-Accepted |

### Accessors

| Function | Return Type |
|----------|-------------|
| `getId` | InviteId |
| `getEventId` | String |
| `getContactId` | ContactId |
| `getContact` | Contact |
| `getRole` | AttendeeRole |
| `getRsvp` | RSVP |
| `getSentAt` | Maybe DateTime |
| `getRespondedAt` | Maybe DateTime |
| `getComment` | Maybe String |

### Modifiers

| Function | Parameters | Notes |
|----------|------------|-------|
| `respond` | Invite, RSVP, DateTime | Record response |
| `respondWithComment` | Invite, RSVP, DateTime, String | Response with message |
| `updateRole` | Invite, AttendeeRole | Change attendee role |

### Queries

| Function | Return Type | True When |
|----------|-------------|-----------|
| `isOrganizer` | Boolean | Role is Organizer |
| `isRequired` | Boolean | Role is Required or Chair |
| `isOptional` | Boolean | Role is Optional or NonParticipant |
| `hasResponded` | Boolean | RespondedAt is Just |
| `isAttending` | Boolean | RSVP is Accepted or Tentative |

### Display

```purescript
toDisplayString :: Invite -> String
-- "Alice Smith (Required) - Accepted"
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // attested
────────────────────────────────────────────────────────────────────────────────

## Attested Scheduling

Cryptographically verified scheduling actions for non-repudiation.

### Why Attested Scheduling?

At billion-agent scale, scheduling requires:
1. **Non-repudiation** — Proof that an action occurred
2. **Tamper detection** — Verify content hasn't been modified
3. **Deterministic identity** — Same content = same hash
4. **x402 compatibility** — Foundation for on-chain verification

### Attested Types

| Type | Wraps | Proves |
|------|-------|--------|
| `AttestedEvent` | Event | When created, exact content |
| `AttestedInvite` | Invite | When sent, who sent it |
| `AttestedRSVP` | RSVPResponse | When responded, who responded |

**RSVPResponse Record:**
```purescript
type RSVPResponse =
  { inviteId :: String
  , contactId :: String
  , response :: RSVP
  , comment :: Maybe String
  }
```

### Event Attestation

| Function | Description |
|----------|-------------|
| `attestEvent` | Create attested event with timestamp |
| `verifyEvent` | Check if event hasn't been tampered |
| `getEventAttestation` | Get attestation proof |
| `getEventContent` | Get event content |
| `getEventId` | Get deterministic UUID5 |
| `getEventContentHash` | Get content hash |
| `getEventTimestamp` | Get attestation timestamp |
| `getEventContentHashHex` | Get hash as hex string |

### Invite Attestation

| Function | Description |
|----------|-------------|
| `attestInvite` | Create attested invite |
| `verifyInvite` | Verify invite integrity |
| `getInviteAttestation` | Get attestation proof |
| `getInviteContent` | Get invite content |
| `getInviteId` | Get deterministic UUID5 |
| `getInviteContentHash` | Get content hash |
| `getInviteTimestamp` | Get attestation timestamp |

### RSVP Attestation

| Function | Description |
|----------|-------------|
| `attestRSVP` | Create attested RSVP response |
| `verifyRSVP` | Verify RSVP integrity |
| `getRSVPAttestation` | Get attestation proof |
| `getRSVPContent` | Get response content |
| `getRSVPId` | Get deterministic UUID5 |
| `getRSVPContentHash` | Get content hash |
| `getRSVPTimestamp` | Get attestation timestamp |

### Serialization Formats

**Event Serialization:**
```
id|title|startDateTime|endDateTime|organizerId
```

**Invite Serialization:**
```
id|eventId|contactId|contactEmail|contactName|role
```

**RSVP Serialization:**
```
inviteId|contactId|response|comment
```

**Example Usage:**
```purescript
-- Create an attested event
attestedEvent <- attestEvent myEvent currentTimestamp

-- Verify integrity
isValid = verifyEvent attestedEvent  -- true if untampered

-- Get proof for external verification
proof = getEventAttestation attestedEvent
hash = getEventContentHashHex attestedEvent  -- "a1b2c3..."
```

────────────────────────────────────────────────────────────────────────────────
                                                             // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Scheduling/
├── Attested.purs      # Cryptographic attestation (422 lines)
├── Contact.purs       # Person/Room/Resource/Group (257 lines)
├── Event.purs         # Core event type (405 lines)
├── EventMod.purs      # Event modifiers (203 lines)
├── EventQuery.purs    # Event queries (150 lines)
├── Invite.purs        # Event invitations (307 lines)
├── Recurrence.purs    # Recurrence rules (399 lines)
└── RSVP.purs          # Response status (101 lines)
```

8 files, 2,244 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why These Primitives Matter

Scheduling is fundamental infrastructure for coordination. At billion-agent
scale, calendar coordination must be:

**Deterministic:**
Same event data = same EventId = same behavior everywhere. Agents can reason
about scheduling without ambiguity.

**RFC 5545 Compliant:**
iCalendar is the universal calendar interchange format. Full compliance means
seamless integration with Google Calendar, Outlook, Apple Calendar, and every
standards-compliant system.

**Cryptographically Verifiable:**
Attested scheduling actions provide proof of:
- When meetings were scheduled
- Who was invited
- What responses were given
- That nothing was tampered with

This enables x402-compatible on-chain verification for legally binding
scheduling (contracts, depositions, regulatory compliance).

**Role-Based Access:**
The AttendeeRole enum captures real-world meeting dynamics:
- Organizers own the event
- Required attendees must attend
- Optional attendees may skip
- Chairs preside
- Non-participants receive FYI

**Hybrid Locations:**
Modern meetings are often hybrid. The Location sum type captures this reality
with Physical, Virtual, and Hybrid variants — each with appropriate metadata.

## Integration Points

### Temporal Pillar
- `TimezoneId` — Event timezone
- `TimeOfDay` — Time component of DateTime
- `UtcOffset` — Timezone offset calculation

### Attestation Pillar
- `Attestation` — Cryptographic proof
- `ContentHash` — Content verification
- `UUID5` — Deterministic identifiers
- `Timestamp` — Attestation timing

### Brand Pillar (Future)
- Event styling (colors, typography)
- Calendar visual themes
- Invitation templates

────────────────────────────────────────────────────────────────────────────────
                                                          // usage // examples
────────────────────────────────────────────────────────────────────────────────

## Common Patterns

### Creating a Simple Meeting
```purescript
import Hydrogen.Schema.Scheduling.Event as E
import Hydrogen.Schema.Scheduling.Contact as C

organizer = C.person "user-123" "Alice" "alice@example.com"

meeting = E.eventSimple "evt-456" "Sprint Planning"
  2026 3 1 10 0   -- March 1, 2026 at 10:00
  2026 3 1 11 0   -- March 1, 2026 at 11:00
  utc (C.getId organizer)
```

### Setting Up Recurrence
```purescript
import Hydrogen.Schema.Scheduling.Recurrence as R

-- Every Monday, Wednesday, Friday until end of quarter
standup = R.custom R.Weekly 1 
  [R.Mon, R.Wed, R.Fri] 
  Nothing 
  (R.Until { year: 2026, month: 6, day: 30 })

meetingWithRecurrence = EM.setRecurrence meeting standup
```

### Inviting Attendees
```purescript
import Hydrogen.Schema.Scheduling.Invite as I

bob = C.person "user-789" "Bob" "bob@example.com"
invite = I.inviteRequired "inv-001" "evt-456" bob

-- Bob responds
accepted = I.respond invite RSVP.Accepted now
```

### Verifying Scheduling Actions
```purescript
import Hydrogen.Schema.Scheduling.Attested as A

-- Attest the event
attested = A.attestEvent meeting timestamp

-- Later, verify integrity
if A.verifyEvent attested
  then -- Event is authentic
  else -- Event was tampered with
```

────────────────────────────────────────────────────────────────────────────────
