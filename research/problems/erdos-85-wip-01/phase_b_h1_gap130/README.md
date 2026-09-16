# The 130 capacity gaps outside the Phase B residual queue

`gap130.json` freezes the exact complement of the 1,161-root Phase B H1
verdict-only queue within the dated 1,288-gap capacity snapshot. It is a
metadata manifest, not a solve queue or a certificate acceptance record.

| Class | Count | Native input route |
|---|---:|---|
| Reviewed historical overlay, no listed object | 96 | Present in the frozen 1,257 Phase B source. The existing H1 materializer can regenerate each input and check the overlay's CNF hash. A separate reviewed dispatch must select these IDs despite their historical evidence. |
| Outside frozen Phase B source | 34 | Present in `capacity-inventory.compact`, with profile, ordinal and exact 24-value table frozen here. The Phase B materializer refuses these IDs by design; a reviewed capacity-table materializer and CNF identity receipt are needed. |

The remaining 1,158 gap tags are inside the 1,161-root queue. Its other
three tags already had listed objects in the snapshot. Thus
`1,158 + 96 + 34 = 1,288` gaps; a 1,161-root solver run cannot by itself
establish two-solver verdicts for every capacity gap.

For the 96 historical rows, `historical_cnf_sha256` is the reviewed overlay's
expected native CNF digest. The frozen Phase B candidate rows contain no
historical producer hash for those cases, so the overlay supplies the check.
For the 34 outside-frozen rows that field is null: the compact capacity
table fixes the mathematical input, while native emission/checking must
establish the generated CNF bytes before any solve. Seven of these 34 have
v3 claims without a terminal ledger in the dated join; the other 27 have
no recorded v3 claim. Neither state is a solver verdict.

`materialize_capacity_gap.py` is a candidate adapter for those 34 rows. It
checks the frozen manifest and source join, constructs a deterministic
one-row input for the unchanged reviewed H1 native materializer, and records
both the adapter input SHA-256 and the native emission/check receipt. It
rejects the other 96 rows and all unknown IDs. Dry-run selection and all 34
adapter inputs pass the native selector; three focused tests pass. A real
Docker emission/check canary and independent source review are still needed
before using its output as a solver input. This adapter never invokes a SAT
solver.

The manifest pins the source SHA-256 values, reconstructs every capacity
tag from its 24-value table, checks all profile ordinals and set identities,
and carries every table needed by a future materializer. Reproduce it with:

```sh
python3 research/problems/erdos-85-wip-01/phase_b_h1_gap130/freeze.py --check
```

The source snapshots were taken at different times and do not certify the
live bucket. Any final 1,288/1,288 coverage claim must rejoin all solver
receipts by exact tag and CNF identity, preserve UNKNOWN/SAT/ERROR rows,
and disclose which metadata snapshot it uses.
