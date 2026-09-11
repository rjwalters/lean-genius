# Necessary quotients for N80, minimum degree9, free cyclic action of order16

codex-sol-2, 2026-09-11. Integer quotient cover only; no graph or solver search and no existence/exclusion claim.

The accepted below-square regularity lemma2140 makes every such graph9regular. Five vertex orbits of size16 give a symmetric equitable matrix Q with row sums9. Internal circulant degree is0,1 or2: three or more shifts contain distinct noninverse u,v and the four vertices0,u,u+v,v form a C4. An internal degree1 orbit uses the unique involution8.

For distinct orbit indices i,j, (Q²)ij counts two-step walks from one source vertex into the16-vertex target orbit; C4-freeness bounds it by16. For the same orbit, nine walks return immediately to the source, leaving at most15 distinct other endpoints; hence (Q²)ii<=24. In particular any cross degree x satisfies x(x-1)<=15, so x<=4. Two internal degree1 orbits cannot have a cross edge, since the edge and its translate by8 form a C4 with the two internal edges.

The producer enumerates all first-row cross tuples in{0,...,4}^4. It forces the first diagonal by the row sum and rejects invalid first rows. For each remaining first row it enumerates all15625 six-cross-entry tuples among the other four orbits, then forces the four remaining diagonals. All necessary square and involution conditions are checked. The original launch had625 cases, at most15625 combinations per case, and a60-second aggregate cap; all625 completed in0.008seconds, with no unvisited case. There were210 retained labelled matrices.

The independent verifier instead constructs complete row templates, joins them by symmetry of previous entries, and checks the square conditions. It reconstructs exactly the same210 matrices in39031 states, maximum777 per first-row case,0.069seconds. Full permutation canonicalization gives **six classes**, with labelled multiplicities15,60,30,60,30,15 in the order of verification.json. Every retained quotient has exactly one internal degree1 orbit. The representatives and full labelled list are saved verbatim.

These matrices are necessary conditions only. They need not lift to C4-free graphs, and no prepared CNF was altered. Neither N80/m16 nor any broader class is excluded by a nonempty quotient list. Source and verification programs refuse to overwrite their original result receipts; no capped retry occurred.
