# Interim H7 sample receipt review

Status: **receipt consistency PASS; sample unfinished**.

The immutable snapshot ends at 2026-10-08 05:44:56 UTC. The original sampler
process, PID 210262, was independently observed live at 05:45:32 UTC on the
existing cloud builder. Its command specifies six slots, 50 sampled leaves
per cube, seed 20261008, and a 3,600-second per-item cap. The campaign source
is the reviewed commit `50a06c7c033ac8b63a7f9695e7dc7cfd15b38a28`.

`audit.py` checks the pinned snapshot and input-manifest hashes, unique item
identities, the fixed-seed selections and sample indices, binary hashes,
solver UNSAT and checker verified-line fields, proof-stream metadata,
timestamp order, leaf unit shapes, and all cover hashes against the pinned
manifest. Run `python3 audit.py` to reproduce `AUDIT.json`. This is a small
metadata audit; it runs no solver or Lean calculation.

The snapshot contains 331 successful receipts: all 28 covers and 303 leaves,
with 10 or 11 completed leaves in each of the 28 cubes. No heap retries are
recorded. The planned sample has 1,400 leaves; the full campaign has 377,776.

This review checks receipt consistency. It does not independently replay
discarded proofs or reconstruct the leaf CNFs. The proof streams are absent
by the campaign's check-then-discard design. Unfinished jobs are absent from
this snapshot, so completed-case timing is censored and is not extrapolated
to a campaign cost. No completeness or H7 exclusion claim follows.
