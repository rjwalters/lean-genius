# Local multiplicity bounds for N78/F3 color words

Use accepted2206, which supplies three attached-group matchings pi_uv,27 possible residual color words, multiplicity at most3, pair-contingency capacities U_uv, and b(w) neighbor capacities. A word w occurring r times contributes r to every contingency entry U_uv(w_u,w_v), hence r is bounded by the minimum of3 and those three capacities. If r=3, every nonzero coordinate of w has b=(2,2,2).

## No all-nonzero word occurs three times

Suppose w has all three coordinates nonzero and multiplicity3. At coordinate u, the internal matching contributes one incoming label bar(w_u). Since b=(2,2,2), the two other-group incoming labels pi_vu(w_v), for v!=u, must be0 and w_u in some order. Thus exactly one other group v satisfies pi_vu(w_v)=w_u.

Define an edge between u and v precisely when pi_uv(w_u)=w_v. Inverse pairing of the permutations makes this relation symmetric, and the preceding paragraph says each of the three vertices has degree1. This is impossible: summing the three degrees gives3, whereas every edge contributes2. Hence an all-nonzero word has multiplicity at most2. This argument is independent of the local enumeration below.

## Complete local arithmetic diagnostic

The included audit.py traverses all6^3=216 labelled triples of S3 matching permutations and all27 words. For each word it constructs the capacities from2206, bounds multiplicity by min(3,U_01,U_02,U_12), and lowers it to at most2 if any nonzero coordinate fails the necessary b=(2,2,2) condition. A negative b would force multiplicity0. These tests only impose necessary local conditions; an allowed multiplicity is not an achievable one.

Original aggregate wall limit60seconds; all216 cases completed in0.0375seconds, none unknown or unvisited. There are200 assignment-word pairs with upper bound3:56 words with zero nonzero coordinates,96 with one,48 with two, and none with three. These counts range over labelled assignments, so the same word may occur in several counts. In108 of the216 assignments every word has upper bound at most2, so a graph with such an assignment would need at least8 distinct residual words to account for16 residual orbits. No assignment itself is excluded by these results.

The complete local payload is saved in results.json. No graph, residual quotient, coloring selection, phase search, or previously capped domain was run. This concerns only the N78/F3 order-three tight case.
