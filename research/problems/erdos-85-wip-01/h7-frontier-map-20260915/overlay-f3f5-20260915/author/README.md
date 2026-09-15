# H7 selected scope overlay after F3 and F5

The reviewed F3 and F5 graph exclusions add exactly `cube_F7_t3` (2667) and
`cube_F7_t5` (2665) to the accepted F2 overlay. Selected structural scopes now
cover **15 of 28 roots**, leaving **13 outside those scopes**: six a6 and seven
a7 roots. Earlier maps remain unchanged historical snapshots.

The complete F3 chain is 2116 → 2662 → 2664 → 2667, rejecting all 704,382 host
leaves. The F5 chain is 2116 → 2661 → 2663 → 2665, rejecting all 331,484 host
leaves. Both have exact source joins and independent negative endpoint checks.
The common upstream 2116 enumeration completeness rests on accepted code
audit, not an independent replay of that enumeration.

`provenance.json` pins the integration commit and exact source blobs copied
here. Run `python3 check.py` to reproduce the two-row overlay. The check
validates accepted review records, root masks and identity relabellings,
preserves every other row, and verifies the resulting counts. It does not
run a solver or proof replay.

These are paper/computation structural graph exclusions. They are not Lean
kernel theorems or arbitrary-CNF UNSAT proofs. H1, the remaining H7 roots,
formal certificate closure, and the full Erdős 85 problem remain open.
