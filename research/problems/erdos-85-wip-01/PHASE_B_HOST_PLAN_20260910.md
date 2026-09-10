# Phase B host verdict plan

Prepared under board goal 38 (operator goal 48) and editor message 46111. This is a run plan and harness, not a solver result. No Phase B instance has been launched by this work.

The exact surviving instance census and generator revisions belong in `PHASE_B_SURVIVORS_20260910.md` and its machine-readable inventory. Sol1 owns H1/H3; sol3 owns H5/H7. Approximate older counts must not be substituted for that inventory. In particular, the fresh H1 audit differs from the earlier “about 1290” estimate. H3 is already excluded by reviewed Python computation and paper reductions; independent SAT verdicts are a cross-check of that result. The formal H3 remainder (full 261, deficient 1554) counts Lean obligations, not Phase B SAT instances.

## Start conditions and host budget

Bank the master Phase A table and the exact Phase B inventory first. The standing Phase A end is approximately 2026-09-11 07:00 UTC; encode the agreed start as the inventory's timezone-qualified `not_before`. The harness refuses execution before that timestamp and requires the inventory bytes to match an exact ancestor of both HEAD and the locally recorded `origin/erdos85/integration` ref. Refresh that tracking ref before dispatch. Dry-run is the default. There is no automatic launch when the time arrives.

Read-only host probe on September 10: 28 physical/logical CPUs, 96 GiB RAM, approximately 13.1 GiB free on the boot data volume. Use the existing checkout and existing CNFs in place. No new worktrees, proof files, certificate generation, LRAT replay, or CNF copies are part of this plan. Nothing is deleted by the harness.

Start the first three hard cases at **P=1**: the two canonical H3 bases and the first exact H5 inventory root, once their IDs are frozen. Use **1800 seconds per solver** for this pilot. Kissat runs first; only its UNSAT results trigger a CaDiCaL run on the identical CNF bytes. Compare elapsed times with the retained proof-producing records before scheduling the rest: an UNKNOWN pilot establishes that verdict solving is still expensive at this cap, not that proof output was the only obstacle. Report all three outcomes before expanding the queue.

After the pilot is assessed, use **P=4 total solver processes**, including cross-checks. Each worker runs its primary and secondary sequentially; cross-checks do not create four extra processes. Keep P=4 while other agents use the host. At the previously observed H1 rate of about eight primary orbits per hour, roughly 1250 cases require about 156 host hours for the primary pass alone; this is a historical estimate, not a measured Phase B rate. Measure the first actual block before forecasting the tail.

| Sector | Initial primary wall cap | CaDiCaL wall cap after primary UNSAT | Treatment at cap |
| --- | ---: | ---: | --- |
| H1 remaining orbit rows | 3600 s | 3600 s for every inventory-marked hard case | UNKNOWN; retain ID and elapsed time |
| H3 cross-check bases | 1800 s | 1800 s | UNKNOWN; do not replace the independent cross-check with the earlier Python result |
| H5 hard roots | 1800 s | 1800 s | UNKNOWN |
| H7 exact surviving leaves/classes | 1800 s | 1800 s | UNKNOWN |

These are first-pass caps, not a promise of closure. Put any longer tail caps in a new, banked inventory revision after reporting the measured UNKNOWN count and throughput. Do not silently restart a timed-out process or queue the same row twice. Spot capacity remains a separate operator/editor decision; this plan spends nothing.

The harness reserves 8 GiB of output-volume headroom and stops scheduling when free space drops below that reserve. It bounds each solver log to 4 MiB, so each case produces at most two 4 MiB logs plus small JSON receipts. A log-limit stop is UNKNOWN, even if an UNSAT line appeared earlier. This protects against single large artifacts; it is not a disk cleanup policy. Observe host memory during the three-case pilot and lower concurrency if swapping or pressure appears; the harness does not claim to enforce a memory ceiling.

## Inventory and invocation

`sat49/run_verdict_only.py` accepts this schema. Paths are resolved relative to the inventory file; absolute paths are permitted for existing host CNFs. Every ID is unique across the inventory. H3/H5/H7 require `crosscheck: true`; H1's hard rows must also be marked true by the inventory owner.

```json
{
  "schema": "erdos85-verdict-v1",
  "not_before": "2026-09-11T07:00:00Z",
  "cases": [{
    "id": "H3-example-id",
    "sector": "H3",
    "cnf": "/existing/path/to/input.cnf",
    "cnf_sha256": "<64 lowercase hex characters>",
    "generator_commit": "<40 lowercase hex characters>",
    "crosscheck": true,
    "primary_cap_seconds": 1800,
    "crosscheck_cap_seconds": 1800
  }]
}
```

This example is a schema illustration, not an executable inventory or a new case claim. The generator revision and CNF hash identify the encoding being tested; the inventory review must independently establish that its cases cover the claimed sector. Merely passing manifest validation does not prove coverage or Lean-exactness.

```sh
# Metadata and availability only: no solver invocation.
python3 sat49/run_verdict_only.py --inventory /path/to/banked-inventory.json

# At Phase B start, select the three explicitly named pilot IDs.
python3 sat49/run_verdict_only.py --inventory /path/to/banked-inventory.json \
  --inventory-commit <exact-commit> --execute --workers 1 \
  --case-id <H3-base-0> --case-id <H3-base-1> --case-id <first-H5-root> \
  --output-dir /existing-volume/new-pilot-directory
```

Use a fresh output directory for every invocation. Existing result directories are rejected. Explicit pilot selection records `selected_cases` and the full inventory size; a successful subset never sets `inventory_all_unsat` for the complete inventory. Retain and merge previous receipts by exact instance ID and CNF hash when constructing the eventual whole-split verdict table. This runner does not silently resume or merge campaigns.

## Evidence and failure semantics

Installed solver versions observed locally: Kissat 4.0.4 and CaDiCaL 3.0.1. Both CLI help texts document proof output as a second positional filename. The runner passes one input filename and a native time-limit option (`--time=N` for Kissat, `-t N` for CaDiCaL), with no proof filename or certificate flags. It strips solver-option environment variables and records binary hashes, versions, commands, CNF hashes, generator revisions, logs and elapsed time. It checks the CNF hash before launch and after each solver. The solvers share lineage; agreement is useful cross-check evidence, not two mathematically independent proofs.

| Receipt status | Meaning |
| --- | --- |
| `UNSAT_PRIMARY` | Kissat printed only `s UNSATISFIABLE` and exited 20; inventory does not require a cross-check |
| `UNSAT_CROSSCHECKED` | Both solvers produced that matching UNSAT line/exit pair on the same unchanged CNF |
| `SAT_CANDIDATE` | Primary printed SAT and exited 10; retain its model log for independent CNF and graph validation before any witness claim |
| `DISAGREEMENT` | Kissat says UNSAT and CaDiCaL says SAT; stop scheduling and investigate |
| `UNKNOWN` | Solver returned UNKNOWN, hit a time/log/resource cap, or the required secondary check did not finish |
| `ERROR` | Hash mismatch/change, inconsistent exit/status, missing input, crash or other execution failure |

SAT candidates, disagreements and errors stop new scheduling; already running siblings drain under their existing caps. UNKNOWN rows remain explicitly unresolved while other rows run. SIGINT/SIGTERM request cancellation, terminate live process groups and record an aborted campaign. Uncatchable SIGKILL or host failure cannot write a terminal receipt; native solver time limits still bound surviving solver processes, and missing records remain unresolved. Inspect retained process handles before any retry. A complete queue with UNKNOWN rows is not a completed UNSAT case split. Even a complete cross-checked UNSAT table establishes solver-level evidence, not a Lean kernel theorem. The campaign records the OS cumulative child maximum RSS, explicitly not a per-instance or summed memory measurement.

The test suite uses fake executables only and covers exit/verdict mismatch, contradiction, timeout after an UNSAT line, bounded logs, input mutation, pre-launch hash rejection, committed-inventory mutation and dry-run behavior. Run it with `python3 -B -m unittest discover -s sat49 -p test_run_verdict_only.py -v` from this directory. Real solver calibration awaits the banked inventory and execution window.

Pilot comparison limit: the two canonical H3 bases and first H5 root do not match an emitted or solved input hash in the retained 406-root historical ledger audit. The three-case pilot measures current feasibility; it cannot establish a proof-logging speedup without a matched same-CNF, same-solver baseline. This statement covers the retained corpus only.
