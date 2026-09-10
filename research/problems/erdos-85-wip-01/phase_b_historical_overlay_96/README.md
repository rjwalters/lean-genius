# Explicit 96-case historical overlay

This optional revision retains the exact reviewed 95-row overlay and adds
only H1 case `4ee646ca0ec3e2f0`, independently reviewed in squad review 2014.
The frozen 1,416-case index remains unchanged. This configuration schedules
1,320 fresh cases and records 96 historical cases separately. The ordinary
configuration still selects 1,416; the earlier historical configuration still
selects 1,321. Explicit re-solves and hard-row cross-check selection retain
the dispatcher's existing behavior.

The new row has a short verdict without a table suffix, so it must not pass
the old strict parser. The version-2 wrapper in `historical-96.json` references
the exact version-1 bytes (SHA80fd7a26...) and calls the original 95-row
validation path. Its extra row uses the explicit `manifest_joined_mono`
format. That format is restricted to this one reviewed tag and profile 1.
Adding any other row requires another reviewed revision.

The extra-case checks join the frozen table/tag/profile, successful native
emission and check receipt, canonical CNF hash/size, archived baseline,
separate local manifest row, short-format MONO/UNSAT verdict, and paired
historical drat-trim log. The latter must have exactly one `s VERIFIED` status
and the matching variables/clauses header. Every retained metadata string is
checked against its recorded hash. Missing/duplicate local rows, changed
tables, failed generation, altered headers/statuses or a proof-replay claim
are rejected. The local manifest and trim log supply the evidence missing
from the short verdict; the original 95-case parser is not weakened.

These are joins among reviewed snapshots. Review 2014 independently rehashed
the archived CNF and rechecked its strict framing and metadata. Launch does
not re-read the large historical proof artifacts, and no new proof replay,
Lean certificate or global exclusion is claimed. The existence of an old
compact LRAT file is not used as proof-validity evidence.

Inspect the optional queue from the repository root:

```
python3 -B research/problems/erdos-85-wip-01/sat49/dispatch_verdict_only.py \
  --config research/problems/erdos-85-wip-01/phase_b_historical_overlay_96/config.draft.json
```

Execution still requires explicit `--execute`, an exact committed
configuration, a new output directory and the existing launch window. The
wrapper, base overlay, old audit/comparison, and extra audit/comparison all
join the captured committed dependencies (17 files total with tools/index
and sector manifests). Root historical evidence and skipped IDs use the
existing receipt fields. Fresh-solve completion flags remain fresh-only.

The reducer's approved-snapshot list must be extended and reviewed separately
before it accepts this wrapper. Until then it correctly rejects 96-case
runs. SAT observations must continue to conflict with inherited UNSAT;
UNKNOWN/ERROR/INCOMPLETE must remain explicit.

Validation: 11 new manifest-joined tests, 11 earlier historical-overlay tests
and 12 dispatcher tests pass. The dry run records 1,320 selected fresh cases
and 96 historical cases. No solver or input generator was launched for this
revision; it consumes the already reviewed native-generation evidence.
