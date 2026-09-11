# Independent graph derivation audit: proposed N78/F10 contradiction

This audit starts from accepted 2225 and the proposed deficiency count. It does not replace the producer's frozen proof or its primary review.

Write H for the cubic fixed graph, B_v for its six-vertex attached groups, and R for the eight residual vertices. Let a be the number of type A groups and d_j the four residual quotient row degrees. The zero-codegree graph E=8I+J-M² is simple and five-regular. Among unordered R pairs, attached middle vertices contribute 2(10-a) common-neighbor pairs: each B/C group has exactly two vertices of R-degree two, while all other attached vertices have R-degree one. Residual middle vertices contribute sum_j d_j(d_j-1). C4-freeness ensures these contributions do not overlap. Hence

    e_E(R)=28-2(10-a)-sum_j d_j(d_j-1).

There are 2a E edges from R to fixed vertices, because each A group misses two residual vertices and each B/C group covers all eight. E-degree summation on R gives

    e_E(R,B)=40-2e_E(R)-2a=2 sum_j d_j(d_j-4),

using a=4+sum_j d_j. Each d_j is between zero and four. Nonnegativity forces every d_j to be zero or four. A row of degree four is all ones; symmetry then makes every row positive, hence all rows degree four. This contradicts a<=10 (it would give a=20), independently of the adjacent-loop prohibition. Thus Q=0, R is independent, a=4, and E(R,B) is empty. The four A groups miss different residual orbits since the accepted missing count is d_j+1=1.

Let F_A be the four type A fixed centers and F_D the other six. Let S be the 12 attached vertices of R-degree two, all in D groups, and T the 48 attached vertices of R-degree one. Split T into T_A (24 in A groups) and T_D (24 in D groups).

For a fixed center v, E restricted to fixed centers is 2I+J-H² and has row sum three. E(v,R) has size two for A centers and zero for D centers. Therefore A centers have no E-neighbor in attached groups; D centers have two such neighbors. More precisely, for type B these are its own unmatched internal pair, and for type C these are the missing cross-matching pair in its unique deficient partner group. In both cases these are an involution orbit in S, with two R-neighbors per vertex in distinct residual orbits. This uses the accepted fact that an antipodal pair cannot have a common neighbor.

M and E commute. At a fixed center v and residual vertex r, (ME)_(v,r) is the number of H-neighbors of v among the A centers missing r's residual orbit. The other sum, (EM)_(v,r), counts adjacency from v's two attached E-neighbors to r (zero if v is A). Thus F_A is independent, and every D center has exactly two A neighbors and one D neighbor. In particular H[F_D] is a matching.

Every R/attached pair has exactly one common G-neighbor because E(R,B) is empty. For an attached vertex x of R-degree k (one or two), its attached degree is 8-k. Sum its codegrees with all eight R vertices. Only attached middle vertices contribute: each contributes one, plus one more if it lies in S. The sum is eight, so x has exactly k neighbors in S. Hence S vertices have two S neighbors and T vertices have one.

Each r in R has one fixed E-neighbor, no attached E-neighbors, and therefore four E-neighbors in R. Exactly three of the other seven R vertices share a G-neighbor with r. Such common neighbors are precisely its S neighbors, each accounting for one other residual vertex and none repeated by C4-freeness. Thus r has three S neighbors. It has one neighbor in each of the three A groups that do not miss it, giving three T_A neighbors and then three T_D neighbors.

An S vertex belongs to a D group. Exactly two A centers are nonadjacent to that D center in H, and both corresponding cross-matchings are full (A groups are never deficient). Therefore it has two T_A neighbors, and then two T_D neighbors. A T_A vertex has one internal matching neighbor in its own A group and one neighbor in each of the other three A groups, giving four T_A neighbors. Its remaining attached neighbors are one S and two T_D. A T_D vertex has two T_A neighbors for the same allowed-cross-group reason; with one S neighbor, its remaining four attached neighbors lie in T_D.

Consequently the six cells (F_A,F_D,R,S,T_A,T_D), of sizes (4,6,8,12,24,24), have exact G quotient

    0 3 0 0 6 0
    2 1 0 2 0 4
    0 0 0 3 3 3
    0 1 2 2 2 2
    1 0 1 1 4 2
    0 1 1 1 2 4.

For any T_D vertex, the number of length-two walks ending in S is 2+3+2+2+4=13. The 12 endpoints are all distinct from the starting vertex, so C4-freeness permits at most 12 such walks. Contradiction.

Every step above is a local graph count or accepted 2225 property; no quotient search, full graph solver, or cycle classification is used. If independently accepted, this excludes N78/F10 only. It does not exclude smaller involution fixed counts, N80/F10, or solve Erdős 85.

The subsequently frozen producer PROOF.md was read in full and matches this independent derivation. All producer payload pins were verified; exact manifest and proof hashes are saved in input-pins.json. The primary review remains review 2236 directed to sol1.
