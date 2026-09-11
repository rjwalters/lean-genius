# Review 2192 — PASS

codex-sol-2, 2026-09-11. All frozen pins and five live source equalities verified. Independently topologically assembled all five supplied source bodies (including AttachedPrimeOrbit and OrderSevenFixedGraph), rather than importing those submitted theorems. Read-only Docker compilation exited0; all three final axiom lists contain only propext, Classical.choice and Quot.sound, with no sorryAx. External accepted imports and assembly order are recorded in assembly.json.

The three attached sets have cardinal seven, lie in the moved set and are pairwise disjoint. Independence forbids edges inside the first; adjacency of the corresponding fixed centres forbids edges from the first to either other set. A fixed vertex other than the first centre has no neighbour in the first attached set, by uniqueness of a moved vertex's fixed neighbour. Thus only that centre and the moved complement of the three attached sets can receive incidences from the first attached set.

The centre contributes at most seven and every other permitted vertex contributes at most one. The total incidence count is the degree sum on seven nine-regular vertices, namely63. With D=M minus the three sets, the bound63<=7+|D| and |D|+21=|M| force |M|>=77. This proof correctly works in the full graph, accounting for the centre explicitly.

The fixed-graph theorem supplies a fixed vertex with two distinct fixed neighbours and leaves only (N,F)=(78,8),(80,3),(80,10). The77 moved bound eliminates the first and third, leaving (80,3). Consequently at78 every period-seven adjacency-preserving map is the identity. The proof retains the finite/C4-free/minimum-degree-nine assumptions and does not claim that arbitrary graphs lack order-seven automorphisms.

Audit setup: image lean4-arm64:v4.31.0,4096MB memory/swap,two CPUs; read-only integration /workspace, shared build/packages /workspace/proofs/.lake/{build,packages}, this directory /audit; working directory /workspace/proofs; command timeout 120s lake env lean /audit/Audit.lean. Raw output is compile.json.

Scope: complete formal exclusion at78 and reduction to F3 at80. The final80/F3 contradiction remains a separate proof obligation; neither unrestricted graph order is excluded.
