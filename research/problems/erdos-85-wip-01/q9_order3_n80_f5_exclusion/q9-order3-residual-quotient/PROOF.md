# Ten-orbit necessary system for the N80/F5 order-three residual case

Use accepted2176/2179. A hypothetical N80 witness with an order-three automorphism fixing five vertices has a residual C4-free4regular graph R on30 vertices. Its action on R is free, giving ten3vertex orbits P_1,...,P_10. Each fixed vertex u has a nine-vertex attached group B_u, comprising three3orbits labelled0,1,2: orbit0 consists of the three isolated vertices in G[B_u], while orbits1and2 are joined by a perfect matching.

Let Q be the symmetric ten-by-ten residual quotient. Then Q has row sum4, diagonal entries0or2, and cross entries0,1or2. A diagonal2 means an internal triangle; a cross3 block would contain a K3,3 and hence C4, so is forbidden.

For each fixed u and residual orbit P, every vertex in P has exactly one neighbour in B_u. Equivariance puts all these edges between P and a single attached3orbit, as a perfect matching. Write c_u(P) in{0,1,2} for this orbit. The ten orbit indices have colour multiplicities4,3,3: each vertex of attached orbit0 has four R neighbours, and each vertex of attached orbits1and2 has three. Thus there are five partitions of ten indices into cells of sizes4,3,3.

For P!=T set a(P,T)=#{u:c_u(P)=c_u(T)}. Fix a vertex in P. Through attached groups it has exactly a(P,T) length-two walks into T, one for each colour agreement. Through R it has (Q²)_PT such walks. All endpoints must be distinct, so

`(Q²)_PT + a(P,T) <= 3`.

Within P, the five attached groups contribute only five return walks, while Q² counts all residual walks. The full graph has nine return walks and at most two other endpoints in P, so

`(Q²)_PP <= 6`.

Since the row sum is4, each entry2 contributes two units to squared norm above row sum. Therefore each row has at most one entry2, counting the diagonal. The double cross edges form a matching disjoint from the internal-triangle indices. Two internal-triangle indices cannot have a positive cross entry, because translating a cross edge around their common internal shift gives a C4. The only sorted degree profiles are consequently: four cross singles; one cross double and two singles; or one diagonal2 and two cross singles.

## Coupling to the attached-group matchings

The perfect matching between B_u and B_v is equivariant and induces a permutation pi_uv of their three orbit labels, with pi_vu=pi_uv^{-1}. For fixed residual P and group u, define n_a=sum_{T:c_u(T)=a} Q_PT. Define e(P,u)=0 if c_u(P)=0 and1 otherwise; if e=1, let bar(c_u(P)) be the other label in{1,2}.

For each a in{0,1,2}, the total number of length-two walks from a vertex of P into attached orbit (u,a) is

`n_a + 1[e=1 and a=bar(c_u(P))] + sum_{v!=u} 1[a=pi_vu(c_v(P))]`.

The first term counts middle vertices in R, the second those in B_u, and the last those in other attached groups. Fixed vertices contribute none, because R has no fixed neighbours. Each displayed count is at most3. Their sum over a is8+e. Thus if c_u(P) is1or2, all three counts equal3; if it is0, the three counts are2,3,3 in some order.

Every hypothetical graph in this fixed-count case supplies Q, the five colourings and the ten inverse-paired permutations satisfying all these constraints. The system deliberately omits matching phases modulo3 and additional constraints, so a satisfying integer system would not prove graph existence. This is a necessary finite formulation only; no enumeration, graph solver, full case exclusion or Lean claim is made here.
