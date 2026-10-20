# ISO-8601 UTC timestamp convention

Every anvil command that writes a `_progress.json` (or `_meta.json`, or
any other timestamped field) MUST use a single canonical timestamp format.
Drift across commands makes diffs noisier and breaks straightforward
chronological sorts.

## Format

**ISO-8601 with UTC `Z` suffix, second precision.**

```
2026-05-28T14:12:00Z
```

Examples:

- `2026-01-23T10:00:00Z` — January 23, 2026 at 10:00:00 UTC.
- `2026-05-28T14:12:00Z` — May 28, 2026 at 14:12:00 UTC.
- `2026-12-31T23:59:59Z` — last second of 2026 UTC.

## Rules

1. **UTC only.** Never write local-time offsets (`+02:00`, `-05:00`). The
   `Z` suffix makes the timezone explicit and avoids interpretation
   ambiguity across collaborators in different timezones.
2. **Second precision.** No sub-second component (no `.123` after seconds).
   Anvil phases run on a human timescale; millisecond precision adds
   noise without informational value.
3. **`T` separator, not space.** `2026-05-28T14:12:00Z`, not
   `2026-05-28 14:12:00 UTC`.
4. **Zero-padded.** `2026-01-09T05:07:03Z`, not `2026-1-9T5:7:3Z`.

## Generating the timestamp

Shell-side (consumer environments without Python):

```sh
date -u +%Y-%m-%dT%H:%M:%SZ
```

Python-side (when a non-LLM consumer eventually needs to write progress
files):

```python
from datetime import datetime, timezone
datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
```

LLM-side (when an agent writes JSON directly): substitute the current
UTC time formatted exactly as above. Do not invent timezones; if the
current time is not knowable, use the most recent timestamp the agent
has seen in the conversation and note the substitution.

## Where this is used

- `_progress.json` `phases.<phase>.started` and `phases.<phase>.completed`.
- `_meta.json` `started` and `finished` fields.
- `.promote/receipt.md` acknowledgment timestamps.
- Any future audit log entry or session marker.

## What this is NOT

- **Not** a date format for human-facing rendering. Verdict markdown,
  comments, and reports can use whatever locale-friendly date format
  fits the audience (e.g., "May 28, 2026"). The ISO-8601 UTC rule
  applies only to machine-readable timestamp fields.
- **Not** a logging timestamp format. Loggers can use whatever their
  framework defaults to; the rule applies to artifact metadata.
