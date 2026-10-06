# H1 certified census — receipts (board goal #48)

Completed 2026-10-06 06:36Z. Every H1 residual root is now certificate-checked:

| Set | Rows | Result | Checker |
|---|---|---|---|
| Census roots (this run) | 1,160 | 1,160 CERTIFIED | cake_lpr |
| Historical certificates | 96 | 96 accepted | 50 Std `LRAT.check` (lratreplay), 46 cake_lpr |
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
