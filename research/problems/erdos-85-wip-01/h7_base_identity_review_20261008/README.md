# Independent H7 base-formula identity review

Status: **PASS for all 28 base cube formulas**.

Cloud job `20261008T051026-erdos85__h7t0-formal-20261007-211746` ran
`check_base_identity.sh` at commit
`50a06c7c033ac8b63a7f9695e7dc7cfd15b38a28`. The authoritative job exit is
zero. The retrieved raw log's SHA-256 was separately matched on the cloud.

The reviewed Lean emitter evaluates
`orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf F i` and prints its
clauses in order, translating a zero-based SAT variable to DIMACS with
`v + 1` and preserving literal polarity. The shell wrapper uses `pipefail`;
the comparator requires exactly 28 segments, the expected variable and
clause counts, and the frozen hash for each cube in the fixed argument order.

Every formula has 720,825 clauses and 17,633 variables. All 28 unique root
identifiers, masks, and emitted hashes match both the frozen Python roots
and the pinned campaign input manifest. The inline per-cube results equal
the complete receipt. The three printed Lean source hashes match the
execution commit; the emitter, comparator, wrapper, and common definitions
were also checked against that commit. `AUDIT.json` records the hashes and
the checks; `raw.log` and `receipt.json` preserve the original evidence.

This verifies byte identity of the base formulas. Together with the separate
hsb/cover identity checks, it supports the campaign's connection to the Lean
formulas. It does not assert UNSAT, completion of the leaf campaign, or H7
exclusion. No additional solver or Lean computation was launched for this
review.
