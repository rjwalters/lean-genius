# Proposed exclusion of the N80/m20 internal2-cross223 quotient

Premise: accepted review2147 covers the possible N80/minimum-degree9/free-Z20 quotients. Consider its type with every internal degree2 and, in each row, cross degrees2,2,3; the degree3 pairs form a perfect matching among the four orbits.

For two different orbits, the number of length-two walks from a fixed source vertex into the target orbit is20. If their cross degree is3, this count is2*3+3*2+2*2+2*2=20. If it is2, the count is2*2+2*2+2*3+3*2=20. The target orbit has20 vertices, and C4-freeness allows at most one such path to any endpoint. Every cross-orbit pair therefore has exactly one common neighbour. In particular, every edge between different orbits belongs to exactly one triangle.

Fix one vertex orbit V. Every vertex in V has cross degree7, so140 edges connect V to other orbits. Their unique triangles are mixed: they meet two or three vertex orbits. Every mixed triangle involving V uses exactly two cross edges incident to V, whether it has one or two vertices in V. Therefore exactly70 mixed triangles involve V.

The Z20 action preserves the set of mixed triangles involving V and acts freely on it. Indeed, a triangle meeting three vertex orbits has a unique vertex in each; any setwise stabilizer must fix these vertices. A triangle meeting two vertex orbits has a unique vertex in one of them, which any setwise stabilizer must fix. The original action is free on vertices, so both stabilizers are trivial. Every orbit of mixed triangles has size20.

Consequently the number70 must be divisible by20, a contradiction. This excludes this particular quotient type and its three labelled versions. It leaves the other two accepted2147 quotient types open. No solver run, CNF modification, global N80 exclusion or Lean theorem is claimed.
