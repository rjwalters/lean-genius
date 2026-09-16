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
the adapter/freeze source hashes, adapter input SHA-256, native emission/check
receipt, and an independent post-return CNF hash and byte-count readback. It
rejects the other 96 rows and all unknown IDs. Dry-run selection and all 34
adapter inputs pass the native selector; six focused tests pass. Independent
source review passed for commit `1a6f1c906c`. One real Docker emission/check
canary passed for `h1_0d27d1c53e67aa6c` on 2026-09-16: the checked CNF has
12,479,696 bytes and SHA-256
`8ddc9688635bec216d221f3c1b6e821c9f1b8061387c89ac943a56795d92d1b9`.
The output and both receipts are at
`/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-capacity-gap-canary-20260916-sol1-h1_0d27d1c53e67aa6c`.
The native receipt SHA-256 is
`09a041486fd2abd4f6f350df8399cd3d98f132ca2a9421728b4ce91eb6298473`;
the binding receipt pins the adapter source SHA-256
`b223db0913341b69d8be23c89c28e3ea8f966a1ed8099b8d9fe00363125cf2fa`,
freeze source SHA-256
`5beca242a3f0cd4b86fe8aa361be5b306b4ab46f300e4b86e3b7ffac6761dece`,
native materializer SHA-256
`00201aa9e23c2c55bce8cab3532d5eaf34df9fdb24d0134df01a974e0ff74dbd`,
and frozen manifest SHA-256
`e65684212b851d3fa3cb0e7598b6ead5662da7b3abcc97c64835945cccd7baf0`.
Independent readback found matching hashes, sizes, and receipt identity;
the native check returned zero, container cleanup completed, and no solver
launched. This is one input canary, not a verdict for any of the 34 rows.

`dispatch_capacity34.py` is a separate candidate verdict-only route for all
34 outside-frozen rows, which are absent from the 1,416-case Phase B index.
It uses the reviewed native adapter for each input and the unchanged
`run_verdict_only.run_case` for Kissat and CaDiCaL at the H1 14,400-second
caps. Execution requires banked config and wrapper commits, a new output
directory, and the frozen 34-ID digest. It accepts a row only after an
`UNSAT_CROSSCHECKED` result; primary-only UNSAT is an error. Its full dry run
selects 34; six focused wrapper tests pass. It has not launched a solver and still needs
independent source review and an execution decision.

`dispatch_historical96.py` is a separate candidate verdict-only wrapper for
the 96 historical-overlay gaps. It selects exactly the reviewed historical
IDs from the unchanged 1,416-case Phase B index, uses the existing H1
two-solver policy with 14,400-second caps, and checks each newly emitted CNF
against that row's reviewed overlay SHA-256 *before* either solver starts.
This extra guard is necessary because the frozen candidate rows have blank
historical CNF hash fields for all 96 cases. Its full dry run selects 96,
and four focused tests pass. Independent source review passed for commit
`54b7f7035b`; it has not launched a solver, and a separate execution decision
remains open.

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
