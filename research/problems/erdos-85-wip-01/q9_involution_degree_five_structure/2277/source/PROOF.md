# Symmetric deficit coupling and filtering the saved t=0 matrices

Assume the degree-five branch and accepted 2274, so attached residual degrees are one or two, never three. At an attached vertex u in B_p, the fixed center p and its three H-neighbors account for the usual fixed-center common-neighbor slots as follows. The three centers adjacent to p each have p as their unique common neighbor with u. For p itself the internal B_p neighbor is the only possible common neighbor. For each of the other six centers q, a cross neighbor in B_q is the only possible common neighbor. These seven internal/cross slots are each at most one. Their occupied total is the W-degree 8-k_R(u). Hence precisely k_R(u)-1 fixed centers have zero common neighbors with u.

Thus every k=1 attached vertex has no fixed E-neighbor, and every k=2 vertex has exactly one. The involution makes this target constant across each k=2 attached orbit. It is either its own center (an absent internal matching neighbor) or a nonadjacent center of H (an absent allowed cross neighbor). It cannot be an adjacent center.

Let Z_pq count the k=2 orbits in B_p targeting q. If p differs from q, the missing vertices in the B_p--B_q matching number 2Z_pq on one side and 2Z_qp on the other. The groups have equal size six, so Z_pq=Z_qp. The diagonal represents internally unmatched orbits. Each group has delta_p k=2 orbits, where delta_p=2-|Y_p|, giving row sum delta_p. Symmetry gives the same column sums.

At t=0, accepted 2274 says that each of the four P groups has one central k=2 orbit, supported on residual orbit zero and one leaf orbit. Those four leaf labels form a permutation of 1,2,3,4. There are six k=2 orbits altogether, by sum delta=6, leaving exactly two noncentral k=2 orbits. Each is supported on two distinct covered leaf orbits. Supports in the same attached group are disjoint because each residual vertex meets that group at most once. These orbit supports omit all residual orientation information; retaining them is a relaxation, sufficient for rejecting a saved incidence matrix but not for constructing G.

For every fixed center f and residual orbit j, define T_fj as the number of k=2 orbits targeting f whose support contains j. This is exactly (E_FW A_WR)_fr for a vertex r of that residual orbit: equivariance and disjointness give one adjacent member of the attached orbit. Commutation forces

    (HY)_fj <= (YQ)_fj + T_fj.

For t=0, (YQ)_f0=|Y_f| and (YQ)_fj=Y_f0 for j>0. At the central column there are no E-edges to W, so the required target counts are exactly

    T_f0=1+delta_f-deg_P(f).

The checker takes only the ten saved t=0 incidence matrices not already rejected by accepted 2274. It enumerates the six orbit targets with exact column capacities delta, forbidden H-adjacencies, symmetric Z, and the exact central target counts. It then enumerates every central leaf permutation and every two-element support for the remaining two orbits, imposing coverage and within-group disjointness. No orientation or other graph constraint is assumed. Every such possibility violates at least one commutation inequality, in all ten saved matrices.

The target assignments number four for each of seven matrices and fourteen for each of three matrices. The respective support/target combinations tested number 792 and 4,032, totaling 17,640. The complete filter finished in under one second with a 30-second cap. Together with 2274's rejection of the other fourteen, this rejects all 24 saved t=0 witnesses of the older relaxed model. It does not exclude their roots: alternative matrices may exist. The earlier capped search is neither replayed nor extended, and its UNKNOWN/UNVISITED statuses remain intact.

This is a necessary coupling lemma and finite saved-certificate filter only. It is not a full-graph solver, a t=0 exclusion, a Lean formalization, or a solution to Erdős 85.
