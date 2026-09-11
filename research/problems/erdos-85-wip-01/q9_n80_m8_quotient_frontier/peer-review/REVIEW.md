# Review 2168 — PASS, retained-only scope

codex-sol-2, 2026-09-11. Nine pins verified, with pre-launch source/binary hashes equal to the pinned files. Compressed and raw streams agree byte-for-byte.

Inspected cover.cpp without executing it. Rows join through their assigned symmetric prefix; earlier completed rows remain fixed. Pairwise dot products check all cross entries of Q squared when the later row is assigned. The internal-degree-two BFS runs only on completed indices and enforces a necessary bipartite support condition. The completed-matrix triangle rejection uses the accepted free-orbit mixed-triangle parity argument. Bounds and normalization are necessary, not sufficient for a graph lift.

The tested-row counter is incremented once per candidate, checked before attempting candidate 100001, and reset only at the next distinct sorted first-row root. A cap exception emits UNKNOWN; time/artifact termination preserves unvisited roots. All actual receipts record node caps at 100000. No inference of nonexistence is made for capped roots, including those retaining zero matrices.

Independent audit derives the 13 sorted roots by multisets and the 7846 ordered row profiles by multinomial counts. It validates every retained matrix, source-root match, row/symmetry/bound constraints, square bounds, involution-pair rule, internal-degree-two colouring, and saturated-cross parity. All 24 matrices pass and are distinct. The 13 ordered receipts and summary match results.json exactly: zero COMPLETE, 13 UNKNOWN, zero unvisited roots. This audit did not rerun the capped traversal or modify submitted artifacts.

Scope is source/cap inspection and retained-candidate/status validation only. It is not an independently reproduced search frontier, complete quotient cover, N80/free-Z8 exclusion, graph witness, SAT result or Lean theorem.
