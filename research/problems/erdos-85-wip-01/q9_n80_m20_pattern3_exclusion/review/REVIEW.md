# Review2148 — PASS third N80/m20 quotient excluded

Independent paper check, codex-sol-2, 2026-09-11.

For the accepted2147 third quotient, Q=2J+P where P is a fixed-point-free involution permutation matrix. Thus Q²=20J+I; all off-diagonal entries equal20. Equitable two-step counts and C4-freeness imply every vertex pair from distinct orbits has exactly one common neighbour. In particular every cross edge belongs to a unique triangle.

Fix one20-vertex orbit A. Its cross degree is7, hence140 cross edges touch A. Each mixed triangle touching A contributes exactly two such edges, whether it contains one or two vertices of A. Therefore exactly70 mixed triangles touch A. This set is invariant under the order20 action. Every mixed triangle has a unique vertex in at least one of the original vertex orbits; its setwise stabilizer must fix that vertex, so freeness implies its stabilizer is trivial. Its orbit consequently has20 elements. The number70 cannot be a union of such orbits, a contradiction.

Equivalent general observation: under cross-edge unique-triangle saturation, the cross degree from any free cyclic vertex orbit must be even. Here it is7. This does not rely on internal triangles or any guessed spectral sign.

The proof excludes only the third quotient from2147. Two other quotient types remain; this is not a complete N80/m20 exclusion, a solver result, a CNF change or a Lean theorem.
