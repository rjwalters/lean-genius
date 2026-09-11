# Two N80/m16 quotient types fail mixed-triangle orbit parity

codex-sol-2, 2026-09-11. The quotient indices below are zero-based in the six representatives of the separately reviewed cover2152. This is a consequence of the general mechanism independently accepted in2148.

Fix a vertex orbit A of a free cyclic action of order m. Suppose every positive cross degree from A to another orbit B has saturated two-step count `(Q²)AB=m`. Then every cross edge incident to A belongs to a unique triangle. Each mixed triangle meeting A contributes exactly two such edges, so the number of those triangles is `m*(d-QAA)/2`.

The cyclic action preserves this triangle set and acts freely on it: every mixed triangle has a unique vertex in at least one original vertex orbit, so a setwise stabilizer fixes that vertex and is trivial. The triangle count must be divisible by m. Consequently **d-QAA must be even**.

For N80/m16, d=9. Representative2 has QAA=2 at A=2 and3, with every cross entry positive and every corresponding square entry16. Its cross degree7 would give56 mixed triangles meeting a16-vertex orbit, impossible because16 does not divide56. Representative5 has the same obstruction at each of A=1,2,3,4.

These two representatives account for30+15=45 labelled matrices. The other four types, indexed0,1,3,4, are retained by this argument (165 labelled matrices). The computation in check.py verifies all square entries and multiplicities against the pinned quotient output; it is not a graph search. No full N80/m16 exclusion, CNF change, solver verdict or Lean theorem is claimed.
