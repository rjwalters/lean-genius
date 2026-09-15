# H7 selected scope overlay after F2 review 2659

The accepted F2 computational exclusion adds exactly `cube_F7_t2` to the
historical map reviewed as 2652. The selected structural scopes cover **13 of
28 roots**, leaving **15 outside those scopes**: six a6 roots and nine a7 roots.

`check.py` verifies the pinned historical map, accepted review, exact F2 root
mask and identity relabelling. It preserves every other historical row and
produces `results.json`. `provenance.json` identifies the integration commit and
the exact committed source blobs copied here. Run `python3 check.py` to reproduce
the overlay; no search, solver, or proof replay is involved.

The F2 chain is 2116 → 2655 → 2657 → 2658 → 2659. It covers all 785,408 host
leaves with checked negative endpoints. The upstream singleton enumeration's
completeness rests on its accepted code audit, not an independent enumeration
replay. This is a paper/computation graph exclusion; formal Lean closure remains
separate. The historical 12/28 map, frozen solver inventory, and original
UNKNOWN record are retained unchanged.
