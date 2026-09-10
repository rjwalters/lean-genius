# Phase B per-worker dispatcher (review draft)

`../sat49/dispatch_verdict_only.py` connects the reviewed H1 native input stage,
H5/H7 exact unit materializer and existing H3 bases to the verdict-only runner.
Each worker prepares one case, runs Kissat, then any required CaDiCaL check.
The worker count covers the entire preparation/solve pipeline. No queue-wide
CNF generation occurs. The default is a dry run and one worker.

The draft configuration pins all four tool sources, the 1,416-case combined
index and (transitively) its four sector manifests. Execution requires all
captured bytes to equal one exact committed ancestor of both local HEAD and
`origin/erdos85/integration`. One captured snapshot supplies parsing, bank
checks and receipt identity. Every index ID/source offset/hash must join
bijectively; the current fixed census is H1 1,257, H3 2, H5 129, H7 28.
Any revised survivor census requires a separately reviewed code/config change.

`config.draft.json` is preparation metadata, not an instruction to launch.
The planned window starts 2026-09-11 07:00 UTC after Phase A. No solver campaign
was run in preparing this package. The intended first pilot selects both H3
canonical bases and `h5_t0.cube-0-0` with one worker. This calibrates present
feasibility, not proof-logging speedup: a matched historical baseline is absent.

From the repository root, inspect that pilot without generating input:

```
python3 -B research/problems/erdos-85-wip-01/sat49/dispatch_verdict_only.py \
  --config research/problems/erdos-85-wip-01/phase_b_dispatch/config.draft.json \
  --case-id h3_t0_canonical --case-id h3_t1_canonical \
  --case-id h5_t0.cube-0-0
```

An eventual explicit execution additionally requires `--execute`, an exact
`--config-commit`, and a new `--output-dir`. The existing harness supplies
native solver caps, process-group cancellation and bounded logs. H1 generation
has its independent native/container caps. H5/H7 preparation is bounded by
strict 99 MB input/output checks. Eight GiB free headroom is checked before and
after preparation and after each completed batch. No memory limit is imposed
on native solvers; H1 generation retains its container memory limit.

Each `output/<id>/preparation.json` records the input identity and provenance;
`output/<id>/solve/<id>/result.json` is the unchanged solver receipt, while
`output/<id>/result.json` combines preparation and verdict status. Root
`results.json` identifies config/index hashes, config commit, selected IDs,
solver identities and explicit `not_started`. A selected pilot can never set
`inventory_all_unsat`. These are solver verdicts, not Lean certificates.
SAT_CANDIDATE is not a graph witness; separate graph-decoder verification is
required. ERROR, DISAGREEMENT or SAT_CANDIDATE stop further submissions only
after inspecting every already-completed result; active siblings drain.

After a successful UNSAT or UNKNOWN receipt, the dispatcher may remove only
the fresh generated CNF inside that invocation's exclusively created case
directory, after a final hash check. All preparation/solver receipts and logs
remain. SAT, errors, cancellation and pre-existing H3/base inputs are retained.
No historical artifact is removed. A failed preparation writes an ERROR case
receipt and never launches a solver. Existing case directories are untouched.
A killed harness can leave incomplete receipts and fresh inputs; these are
unresolved, never implicit UNSAT. There is no automatic resume or cleanup of
another invocation's outputs.

The twelve tests use fake solvers and verify scheduling, cancellation, retained
input protection, failure receipts, exact-index loading and mutation detection.
`preparation-pilots.json` records actual H1/H3/H5/H7 input preparation through
the dispatcher adapter, with independent output hash rereads and no solver
launch. H1 uses the existing historical producer binary; the generator commit
names the source provenance, not a fresh binary rebuild.

Review 2001 passed the initial implementation. Its N1–N3 follow-up independently
extracts the 1,066 known H1 hashes from the frozen source rows and enforces them
after materialization; each H1 preparation records `identity_basis` as
`historical` or `new` (191 rows). Optional config `crosscheck_ids` selects
individual H1 rows for CaDiCaL even when the sector default is false. Unknown,
duplicate and non-H1 override IDs are rejected. Aborted state is published at
the first observed cancellation. Native solver memory remains uncapped.

The real-index test requires the banked combined index and both sector
manifest directories beside `sat49`; run tests from the repository tree.
The four preparation pilots used the review-2001 source pins preserved here;
the final H1 follow-up pilot is recorded separately. No acceptance or solver
result is inferred from these preparation-only checks.
