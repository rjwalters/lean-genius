# H7 capped-leaf follow-up review, 2026-10-08

**Receipt/source audit PASS for both follow-up attempts.** Producer job
`20261008T081402-commit-4c8bab43fccd-328154` terminated with exit 0 at source
`4c8bab43fccd5b3f0250cf96d8ee2568f1818fdd`. These are external cake_lpr
certificate checks, not Lean proof imports or full-campaign completion.

| Leaf | Solver CPU seconds | Checker CPU seconds | Streamed LRAT bytes |
|---|---:|---:|---:|
| `cube_F7_t6:119` | 3474.334389 | 252.980214 | 3,109,017,461 |
| `cube_F7_t0:2061` | 3807.894359 | 364.467792 | 5,193,710,663 |

Both receipts report solver exit 20 and UNSAT, checker exit 0 and VERIFIED
UNSAT, no checker failure, and no early proof-stream close. They used a
7200-second cap and 4000 MB checker heap. The streamed proof bytes were
hashed and discarded by the producer; this review cannot independently
replay them. Successful-attempt stdout was also discarded by the producer,
so acceptance here relies on the retained structured receipts and reviewed
producer source, not a new inspection of checker stdout.

`audit_cloud.py` ran read-only on the existing builder. It checks the exact
producer Git/source identity (including the H1 streaming dependency), terminal
job exit and log, current approved binary bytes, pinned input manifest and
component bytes, and both receipt outcomes. It independently reconstructs
each DIMACS byte sequence from the canonical body, cube units, hsb clauses,
and positive units from the selected cover line, then checks its hash and
length against the receipt. It does not invoke a solver, Lean, or the emitter.
Run it with `python3 -B audit_cloud.py` on that builder while the pinned source
worktree and inputs still exist; stdout is a JSON bundle of the report and
base64 raw evidence. `AUDIT.json` records its source hash and artifact hashes.

The local comparison additionally selected these exact two lines from the
previous audit's immutable `raw-primary.jsonl` (full-file SHA-256
`b93066071de9969416f0d3267082b1a97ca52fc97d5a173b26afe228716ce97d`).
Both original rows are `SOLVER_TIMEOUT` at a 3600-second cap. Their CNF
hashes, byte lengths, units, and binary pins match the follow-up rows.
`evidence/original-censored-rows.jsonl` retains the original lines verbatim;
the selection hash is in `AUDIT.json`. The original cost sample remains
unchanged. A revised cost estimate must identify these as separate follow-up
observations, not retroactively label the original one-hour attempts as
successful. This review does not reproduce a revised cost estimate or its
bootstrap interval.

`evidence/` retains the raw two-row follow-up, original selected rows,
job log/spec/exit, and the producer source files checked against Git. These
are historical bytes; whitespace in raw logs/source snapshots is preserved.
