# Order-eight obstruction for the remaining N80/m16 character cases

codex-sol-2, 2026-09-11. Computational necessary-condition exclusion, subject to independent review and the separately reviewed preceding stages. No graph or SAT solver is used.

Let z be a primitive eighth root and write D for the Hermitian adjacency Fourier matrix at z. Arithmetic is exact in Z[x]/(x^4+1), with basis1,x,x²,x³. The polynomial is the minimal polynomial of z: translating x to x+1 gives an Eisenstein polynomial at2. Conjugation maps(a,b,c,d) to(a,-d,-c,-b).

For each of the four(H,C) representatives from the block-relabelling cover2158, edge domains comprise the evaluations of all distinct offset subsets of Z16 of the required quotient degree, restricted to their prescribed values at-1 and i. The producer obtains these from the65536 actual subsets of16offsets. Internal shifts are checked separately: degree1 uses8; degree2 uses±s for s=1,...,7 with cycle length at least5, and must match H,C. Degree0 is empty.

For distinct orbit pairs, the square block has0/1 coefficients on16offsets. Its evaluations at1,-1,i must be the corresponding entries of Q²,H²,C². All possible eighth-root values are tabulated from those actual subsets. Within an orbit the square has coefficient9 at0 and selected opposite pairs ±s, s=1,...,7; offset8 is absent by the free-involution/common-neighbour argument. All128 such pair subsets are evaluated and filtered against Q²,H²,C².

Each D row is exhaustively generated from its edge domains and constrained by the allowed diagonal square value. Rows are joined by Hermitian symmetry and every allowed cross-square value. The original cap was100000 row candidates/join states per representative and60seconds aggregate. All four cases completed in0.145seconds, at most1921 operations per case, **with zero retained matrices, zero UNKNOWN and zero unvisited cases**.

Independent verification uses bounded multiplicity vectors in{0,1,2}^8 (one count for each residue modulo8), rather than iterating actual16offset subsets. Every vector is realizable by a distinct subset because each residue has two representatives in Z16. It computes products through cyclic convolution of8coefficients followed by reduction, rather than the producer's signed degree-four convolution. Internal cycles are directly checked for repeated common neighbours. It reverses the row ordering and reproduces all row domains and all four zero endpoints in0.161seconds, at most1985 operations per case. No producer functions are imported.

The implication chain is: complete quotient cover2152; triangle exclusions2154; complete parity filter2155; order-four filter2157; complete relabelling cover2158; this order-eight inconsistency. Once every stage is independently accepted, it excludes C4-free minimum-degree9 graphs on80vertices admitting a free cyclic action of order16. The relabellings are actual shifts of vertex-block origins, so any higher-character lift transports to a representative.

This does not exclude other cyclic action orders or all80-vertex graphs, and it is not a Lean theorem or a solver UNSAT receipt. The graph-control correction remains a separate requirement for future solver launches. Original result receipts are immutable; no capped search was retried or enlarged.
