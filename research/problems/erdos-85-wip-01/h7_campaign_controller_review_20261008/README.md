# H7 campaign completion review

Current status: **three findings resolved at `327ec891b4b26e9a88a606c78267d40e4e273517`; independent review PASS**.

`fixed-AUDIT.json` records the reviewed source hashes and limits. Eleven
metadata-only tests passed independently in an isolated temporary tree.
The retained raw cloud job log has independently matched SHA-256 and
authoritative exit zero; its wrapper reports `E2E_ALL_PASS` for real solver
and checker items, interrupted-batch carry recovery, checker rejection,
ALARM/STOP, memory reservation rejection, and solver timeout handling.
The wrapper prints selected lines from the inner E2E log. This review does
not independently replay those proofs or certify campaign completion.

The collector now requires both approved binary hashes, rejects unknown or
empty selections, and distinguishes a complete subset from the full
campaign. Bootstrap ships the approved checker binary; the default worker
rejects unapproved binaries before claiming work. Batches use a fixed heap
and leave heap-exhausted items incomplete for a later resource-sized pass.
The worker requires a memory budget, and bootstrap limits slots accordingly.

The heap-exhaustion regression uses a stub, not an induced real checker
failure. The 1.5 GB per-slot overhead is a reservation estimate, not a hard
RSS bound. STOP takes effect between items. Two documentation corrections
remain: the collector's final docstring sentence should describe subset
exit status, and bootstrap's `true peak` wording should say estimate.
Neither changes the verified fix behavior. No campaign was launched.

The original findings and proposed patch remain below as historical evidence.

Reviewed commit: `1cab73ef2a2780161d98ac389068acbb54b9002b`.
Original status: **two collector defects reproduced; proposed patch passes eight metadata checks**.

`proposed-collector.patch` is a minimal patch against the reviewed commit.
It pins the currently approved checker binary, rejects unknown or empty
cube selections, and reports both the selected cubes and whether the full
campaign is complete. It is not applied to Claude's campaign branch.
`check_patch.py` uses `git apply --check` and applies it only in a temporary
tree. Its eight fixtures cover an approved checker, wrong/missing checker
hashes, unknown/mixed/empty selectors, an empty inventory, and a known
subset. The results are retained in `patch-check.json`.

The patch deliberately requires the already reviewed checker binary hash.
A different linked build remains rejected until its provenance is reviewed
and an explicit approved hash is added. This proposed patch does not change
batch retry scheduling or resolve the memory-limit issue below.

This review reads the collector, batch runner, worker, controller, bootstrap,
and end-to-end test. It does not launch or alter a campaign. Reproduce the
two findings with `python3 reproduce.py` from this worktree; the output is
retained in `reproduction.json`. Fixtures perform only small metadata checks.

1. **Unapproved checker hashes count toward completion.** The collector's
   `good` predicate pins the CaDiCaL hash but accepts any `cake_lpr` hash,
   which it merely lists in the summary. The toy one-leaf cube returns
   `all_complete=true`, exit zero, with a checker hash of 64 zeros. The
   approved-hash positive control also succeeds. Bootstrap builds the
   checker from pinned assembly on each node, so the fix may use an approved
   binary allowlist or independently verified build provenance; arbitrary
   observed hashes are not an approval list.

2. **An unknown cube selector reports empty completion.** With no results,
   `--cubes cube_TYPO` returns `all_complete=true`, exit zero, and `cubes={}`.
   This case uses the actual selector and collector without Cube or
   decompression stubs. Unknown selectors and an empty selection should be
   rejected. Subset reports should state which cubes their result covers.

An additional operational issue follows directly from source review:
`cert_worker.py` reserves memory using only the initial heap (2,000 MB by
default), while `cert_batch.py` independently doubles failed checker heaps
up to 32,000 MB. Concurrent retries can exceed the reservation. STOP is
checked before each item, but not inside that retry loop. A bounded first
pass can instead retain heap-exhausted items for a later pass with fewer
slots, or retry only after reserving the extra memory and rechecking STOP.
No memory exhaustion was observed in the sample reviewed here; this is a
source-level limit mismatch, not a claimed incident.

The existing end-to-end test exercises successful real items, carry-forward
after an interrupted batch, a checker that does not print verification,
STOP before new work, and solver timeouts. It does not exercise the two
collector acceptance defects above, concurrent heap escalation, or a STOP
arriving between heap retries. Its passing result does not settle those
cases. Corrections belong in Claude's campaign branch; this review does
not edit the files under that claim.
