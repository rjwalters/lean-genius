# Computational exclusion of the a7 F2 shape — pending independent closure review

F2 has edges 01,02,03,12,14,35,45 and isolated vertex 6. This is exactly the frozen root cube_F7_t2, mask 328007 (identity relabelling). The complete necessary cover now has a negative endpoint for every leaf.

## Complete chain

1. Accepted 2116 contains all 48 F2 singleton-host bases in its complete portion, giving 3,944 E/S graphs. No capped or unvisited upstream base was resumed.
2. Accepted 2655 independently checks all 3,944 high-assignment sets: 1,496 have no pairing; 2,448 admit 24,136 pairings in total.
3. Accepted 2657 covers all 24,136 high inputs: 16 have no pair-host solution and 785,408 host leaves remain. All calls were COMPLETE; independent coverage and singleton-star endpoint checks passed. The host package is banked under q7_h7_a7_f2_high_host_cover.
4. Accepted 2658 checks a frozen residual prefix: 705,051 empty row domains and 824 arc-consistency contradictions. Its final leaf is UNKNOWN and 79,532 leaves were unvisited. This record remains unchanged.
5. The separately bounded finishing slice checks exactly that wall-interrupted leaf and the untouched suffix, with no already-negative input repeated. All 79,533 finish: 79,293 empty row domains and 240 arc-consistency contradictions, in 12.753 s under a 30 s / 100,000-operation-per-leaf limit. An independent increasing-index row enumerator checks every negative endpoint and atomic arc-removal event in 1.875 s.
6. audit_merge.py verifies the exact disjoint union of the original negative prefix and finishing export, including the original leaf offset 9 at case 3710/pairing 1. Total: 784,344 ROW + 1,064 ARC = 785,408 negative leaves; no unresolved leaf.

The row/arc code is byte-identical to the generic accepted 2111/2117 implementation used for F9. An empty residual row domain excludes a graph completion. Each recorded arc removal rules out a candidate row with no compatible row at another vertex; emptying a domain excludes every completion. Independent source/adapter and endpoint audits establish applicability beyond F9.

## Scope

This is a candidate whole F2 exclusion at the mathematical/computational argument level, awaiting directed independent finishing and closure review. It is not a Lean kernel theorem, a proof that an arbitrary CNF assignment is impossible, an H7-wide exclusion, or a solution of Erdős 85. The frozen solver queue is untouched. Once accepted, this adds exactly cube_F7_t2 to the selected H7 structural scopes, taking their root coverage from 12/28 to 13/28 and leaving 15 outside those scopes. Formal Lean evidence remains an independent obligation.

The initial time cap was preserved. The finishing slice followed the reviewed reading of boards 35/36/38: a productive finite closure chain may finish its unattempted suffix with a separately bounded run. The original UNKNOWN is diagnosed as a wall interruption by 104 counted operations versus the 100,000-operation limit in the pinned code. Both original and finishing records are retained so their scopes remain auditable.
