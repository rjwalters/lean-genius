# Explicit historical H1 verdict overlay

The frozen reference remains 1,416 targets: H1 1,257, H3 2, H5 129, H7 28.
The optional historical configuration schedules 1,321 fresh cases by default:
H1 1,162 plus the same 159 H3/H5/H7 cases. It records the other 95 H1 cases as
historical evidence, not fresh solver outcomes. No historical row is removed
from the index and no old artifact is deleted.

Review 2005 independently checked 98 fresh canonical native generations
against archived CNFs. All 98 matched byte-for-byte; 95 have paired historical
UNSAT/drat:VERIFIED/MONO records with matching tables. Three lack paired
verdict records and remain in the fresh queue. The paired records inherit
historical proof checking; this package does not replay any proof payload or
claim a new Lean certificate. The graph-to-CNF and historical-report trust
boundaries remain those documented in the underlying evidence package.

`historical-95.json` pins the frozen H1 manifest, independent audit and full
native comparison snapshots. `historical_verdict_overlay.py` joins every row
across those exact files, checks the exact 95-case eligible set, native receipt
success/profile/hash, table-derived tag, strict historical UNSAT/MONO framing,
verdict bytes/hash and paired baseline path/hash/table. Missing, duplicate,
unpaired, changed, UNKNOWN, cube-mode or falsely proof-replayed entries fail.
The loader reads one raw snapshot per evidence file; the dispatcher retains
and bank-checks those exact bytes with its other dependencies. It does not
re-read historical proof payloads at launch.

Use the optional configuration explicitly to inspect the proposed queue:

```
python3 -B research/problems/erdos-85-wip-01/sat49/dispatch_verdict_only.py \
  --config research/problems/erdos-85-wip-01/phase_b_historical_overlay/config.draft.json
```

Without this configuration, the normal draft still schedules all 1,416 rows.
Both are dry runs unless execution is explicitly requested with an exact
committed configuration and new output directory after the launch window.
An explicit `--case-id` can select a historical row for re-solving. Any H1 row
marked in `crosscheck_ids` remains scheduled even if it has historical evidence.
No memory or solver-cap policy is changed.

The root receipt adds `historical_evidence` (all 95 validated rows) and
`historical_skipped` (the historical IDs not selected for this invocation).
Preparation and solver receipts remain unchanged. `selected_all_unsat` and
`inventory_all_unsat` retain their fresh-solve meanings: the normal 1,321-case
run cannot set the latter. Combining historical and fresh evidence requires
the separately reviewed reducer extension; an old reducer must not silently
accept overlay runs or infer full closure. A new SAT observation on a historic
case must remain an explicit conflict with its historical UNSAT evidence.

Validation: 11 historical/selection tests and the existing 12 dispatcher tests
pass. Dry-run receipts record 1,416 without the overlay, 1,321 with it and an
explicit one-case historical re-solve. No input generation or solver launch
occurred while preparing this revision. Historical proof checking and fresh
CaDiCaL cross-checking remain distinct claims.

The exact eligible cardinality of 95 is intentional. Adding any of the three
unpaired or 66 untested historical tags requires a new reviewed evidence and
code/configuration revision; they cannot enter through an unreviewed data edit.
