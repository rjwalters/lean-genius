# Universal H3 triple matching capacities: r is3 or4

The secondary eight-vertex graph C[R] in the H3 triple profile has **three or four edges**, independently of the residual spectrum. Each of the three five-vertex blocks Ui contains exactly two edges. Their three cross-edge counts are either(5,5,5), or a permutation of(4,5,5).

This strengthens the universal bound2<=r<=4 in `Q7_H3_TRIPLE_SECONDARY_LEDGER_20260910.md`. It makes the r=2 endpoint exclusion in the spectrum-specific defect-triangle note redundant, while leaving that local spectral bound valid. Neither remaining r case is excluded here.

## Capacities at each Ui

Use the reviewed partition E={u} disjoint-union U1,U2,U3,R, with |Ui|=5, |R|=8, N=N_E(u) of size6, and T=R minus N of size2. Every Ui vertex has degree4 in C[E], and there are no edges from Ui to u. The earlier C4 arguments give:

- C[Ui] is a matching, so ai=e(Ui)<=2.
- Between Ui,Uj there are at most5 edges: every vertex has at most one neighbor in the other block.
- Between Ui and N there are at most5 edges. Every Ui vertex has at most one neighbor in N, since two would be common neighbors with u.
- Between Ui and T there are at most2 edges. Each of the two T vertices has at most one neighbor in Ui, since two would be common neighbors with si.

Consequently Ui sends at most7 edges to R. Its20 degree incidences give

    20=2ai+bij+bik+e(Ui,R)<=2ai+5+5+7.

Thus ai>=2, hence ai=2 for all three blocks. The same equality gives

    bij+bik>=9,

while each bij<=5. Therefore every cross count is4 or5, and two cross counts cannot both be4 because they share a block and would sum to8 there. The only possibilities are(5,5,5) and permutations of(4,5,5).

## Consequences

The secondary degree ledger e(U)=17+r now gives

    r=3: e(U)=20, cross counts4,5,5;
    r=4: e(U)=21, cross counts5,5,5.

Each cross graph with five edges is a perfect matching between its two five-vertex blocks; the four-edge graph is a matching missing one vertex on each side. Each internal two-edge matching leaves exactly one vertex of its block unmatched.

For r=4, C[U] has twelve vertices of degree3 and three of degree2: every vertex has one neighbor in each other block, and four vertices per block have an internal neighbor. Accordingly each Ui has four vertices with one R-neighbor and one with two R-neighbors.

For r=3, the two endpoints omitted by the deficient cross matching each lose one degree from that pattern. They may or may not coincide with the internally unmatched vertices, so no single total degree sequence is asserted for this case.

The verifier `verify_q7_h3_triple_matching_capacity.py` exhaustively checks the tiny scalar capacity system and its exact four possible labeled solutions. This is an arithmetic check of the displayed consequences, not an enumeration of graphs or a Lean graph theorem. All C4-to-capacity arguments are given above.
