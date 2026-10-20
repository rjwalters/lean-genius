# H1 certified census — receipts (board goal #48)

Completed 2026-10-06 06:36Z. Every H1 residual root is now certificate-checked:

| Set | Rows | Result | Checker |
|---|---|---|---|
| Census roots (this run) | 1,160 | 1,160 CERTIFIED | cake_lpr |
| Historical certificates | 96 | 96 accepted | all 96 cake_lpr (2026-10-07; 50 were first accepted by Std `LRAT.check`) |
| Pilot root `h1_81494a6ef36d3ec9` (cube tree) | 36 leaves | 36 VERIFIED | cake_lpr (30 also Std `LRAT.check`) + Lean composition lemma |

No proof was rejected and no solver returned SAT anywhere (1,196 census ledgers).

## Method (per census row) — check-then-discard

1. Regenerate the row's CNF from its banked `table.json` with the pinned emitter
   (`v2cnf` sha256 `4bd9604c…bf6`, image `sha256:a5ca6c4e…6dff6`), run `v2cnf check`, and require
   sha256 = the census `cnf_sha256` (manifest sha256 `9d04a66c…31c2`).
2. Solve with CaDiCaL 3.0.1, `--lrat=true --binary=true`. The binary LRAT proof is streamed
   through a FIFO and a hashing relay into **cake_lpr** (CakeML-verified LRAT/LPR checker,
   github.com/tanyongkiam/cake_lpr @ `a36874a8`, `cake_lpr_arm8.S` sha256 `95b64883…f00c`).
3. A row is CERTIFIED only if CaDiCaL exits 20 with `s UNSATISFIABLE` **and** cake_lpr prints
   `s VERIFIED UNSAT`. Proofs are not stored; the receipt keeps the proof sha256 and byte count.

Totals: 5.64 TB of binary LRAT checked; 3,435 solver CPU-h; 207 checker CPU-h (checking ran
concurrently with solving). Largest proof 36.2 GB. Hosts: AWS Graviton r6g/r7g/r8g (1,157 rows)
and a local Apple-silicon Mac (3 rows).

## Files

- `h1_cert_census_receipts.tsv` — one line per row: CNF sha256, host, heap, proof sha256/bytes,
  solver/checker CPU seconds, census CaDiCaL seconds, number of certified copies, evidence key
  (S3 `s3://2am-erdos85-certs/sat49/cert-20261001/results/…` archive, mirrored on Stripe under
  `artifacts/erdos85-sat49/h1-cert-full-20261001/`).
- `h1_cert_census_summary.json` — totals, pinned tool identities, ledger status counts.
- `historical96_receipts.jsonl` — 98 lines: 96 rows plus 2 superseded first attempts relabelled
  `LRAT_CHECK_OOM` (container memory kill, not a rejection; both re-checked by cake_lpr).
- `pilot_h1_81494a_leaf_*.jsonl` — pilot leaf solves and both checkers' receipts.

## Reproducing a check (third party)

On an arm64 Linux host (e.g. AWS Graviton), with the pinned emitter + image and the **exact**
published CaDiCaL binary (Linux arm64 sha256 `fd601b82…72a2`; proofs are byte-reproducible only
with the identical binary — a macOS build of the same release gives a different, equally valid
proof): regenerate the CNF, run CaDiCaL with the flags above into a FIFO read by cake_lpr, and
compare the proof sha256 with the TSV. Two gotchas:

- **cake_lpr exits 0 even when a check fails.** The only success signal is the stdout line
  `s VERIFIED UNSAT`.
- cake_lpr's heap (`--CML_HEAP_SIZE=<MB>`) must be large enough for the live clause set:
  4 GB sufficed for most rows; the longest rows needed 16 GB. Exhaustion fails cleanly
  ("CakeML heap space exhausted") and is not a rejection.

Determinism: three rows were certified twice on different instance types with the same binary;
all three pairs produced byte-identical proofs (`h1_b2c8ff1df5172f4d`, `h1_975cd491c88d79b8`,
`h1_3e48ec9850423249`, 27–28.6 GB each).

## Incidents (none affect any CERTIFIED receipt)

30 ERROR and 3 SOLVER_NOT_UNSAT ledgers, all infrastructure, all rows rerun to CERTIFIED:
a watchdog `Popen.poll()` race (ECHILD), CaDiCaL's 24 h `-t` cap on the longest row, and a
duplicate claim that reused (and deleted) a live attempt's work directory. Seven spot reclaims
cost rerun time only. Fixes: `cert_row.py` (waitid WNOWAIT), `cert_worker.py` (claim owner = IID,
unique work dir per attempt), `cert_controller.py` (owner re-read each pass; completion requires
CERTIFIED). Cloud spend ≈ $204 (controller estimate incl. 10% margin).

2026-10-07: all 96 historical certificates were re-checked by cake_lpr (`historical96_cake_lpr_receipts.jsonl`), so every H1 orbit in this repository's receipts is cake_lpr-checked.

cake_lpr builds: the AWS rows used a Linux arm64 build of commit `a36874a8` (`cake_lpr_arm8.S` sha256 `95b64883…`); the 96 historical orbits and the 36 pilot leaves were checked locally by a macOS arm64 build of the same commit and the same `cake_lpr_arm8.S` (binary sha256 `d23c413b1852eafd…`, recorded as `checker_sha256` in those receipts).

## Pilot leaf cube hashes (added 2026-10-20, review jhpvtq)

Five rows of `pilot_h1_81494a_leaf_solves.jsonl` (nodes 54, 61, 64, 65, 70) carry `cube_sha256`
and `command` but no `cube_sha_ok` field. They are the five leaves solved live by
`h1_cert_pilot_20261001/solve_leaves.py` after the 2026-10-01 host crash; that driver regenerates
the cube CNF, compares its sha256 with the banked tree's `cube_sha256`, and emits a
`CUBE_SHA_MISMATCH` row (and does not solve) on disagreement, so the check was made but not
recorded as a field. The other 31 rows were rebuilt by `backfill_leaf_receipts.py`, which does
record `cube_sha_ok`. The jsonl rows are historical and are left unchanged.

`pilot_h1_81494a_leaf_expected_sha256.tsv` records the check explicitly for all 36 leaves. It
was produced by `h1_cert_pilot_20261001/recompute_leaf_cube_sha256.py`, which:

1. loads the base CNF (`h1-cube-pass4-20260926/h1_81494a6ef36d3ec9/run-adaptive/base.cnf`) and
   requires its sha256 = the tree's `base_sha256` `860d8af2…177d` (the census `cnf_sha256` for
   this orbit; the materializer receipt shows the pinned v2cnf emitter reproduces it);
2. for every leaf of the banked tree
   (`phase_b_h1_census_20260927/cube-h1_81494a6ef36d3ec9/results.json`, identical to the run
   copy), rebuilds the cube CNF with `cube_verdict.cube_bytes` (base + the leaf's unit literals
   inserted after the header — the same function used by `solve_leaves.py` and
   `h1_checker_kit/cube_check.py`) and hashes it;
3. compares that with the tree's `cube_sha256`, the receipt's `cube_sha256`, and the sha256 of
   the `cube.cnf` still on disk from the pilot run.

Result: 36/36 MATCH on all four values, including the five rows above. Columns: `node`,
`literals`, `expected_cube_sha256` (banked tree), `receipt_cube_sha256`,
`recomputed_cube_sha256`, `ondisk_cube_sha256`, `receipt_had_cube_sha_ok`, `match`.
TSV sha256: `3e1cc9accc4c6c12762c3471560145c191c8821d6c05c4dcdfa10c4ca6183e89`.

## Census manifest (added 2026-10-20, review jhpvtq)

`h1_cert_full_manifest.jsonl` is the manifest cited in step 1 above (sha256
`9d04a66c36497329ae594c5b0f2924c7055a8355651b223bef3c4d8a4fb231c2`, 1,160 lines, 345,305 bytes;
also `manifest_sha256` in `h1_cert_census_summary.json`). It was written by
`../build_manifest.py` (originally at `artifacts/erdos85-sat49/h1-cert-full-freight/manifest.jsonl`
on the project volume) and gives, per census root, `id`, `profile`, `cnf_sha256`,
`table_sha256` and the census solver times. Its 1,160 ids and `cnf_sha256` values agree
one-for-one with `h1_cert_census_receipts.tsv`.

This manifest covers the 1,160 census roots only. The expected CNF hashes for the 96 historical
orbits (`cnf_sha256_expected` in `historical96_*receipts.jsonl`, checked against the archived
sweep CNFs) come from the tracked files `phase_b_historical_overlay/historical-95.json`
(sha256 `80fd7a26…8d98`) and `phase_b_historical_overlay_96/historical-96.json`
(`extra_case`; sha256 `f60a6590…495d`), as read by `h1_cert_pilot_20261001/replay_historical96.py`.
All 96 tags in both historical receipt files match those values.
