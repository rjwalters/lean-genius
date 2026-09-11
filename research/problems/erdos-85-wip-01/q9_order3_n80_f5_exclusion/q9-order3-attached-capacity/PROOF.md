# Attached-orbit capacity constraints for N80/F5

Assume the accepted order-three tight normal form (2179) and ten-orbit notation (2184). These are necessary conditions only; no graph existence, exclusion, solver, or Lean claim is made.

There are five attached groups B_u with labels 0,1,2 on their three free orbits. Label 0 is unmatched internally; labels 1 and 2 match each other. Let E be the three-by-three matrix with E_12=E_21=1 and all other entries zero. Write P_uv for the permutation matrix of the matching from group u to group v: its (a,b) entry is 1 exactly when pi_uv(a)=b. Thus P_vu=P_uv^T. For u != v define T_uv(a,b) as the number of the ten residual orbits with c_u=a and c_v=b. It has row and column sums (4,3,3).

## Pairwise attached walk bound

For every distinct u,v, entrywise,

    T_uv + E P_uv + P_uv E + sum_{w != u,v} P_uw P_wv <= 3 J_3.

Indeed fix a vertex x in attached orbit (u,a), and count length-two walks ending in the three vertices of attached orbit (v,b). Middle vertices in R give exactly T_uv(a,b), because each relevant residual orbit supplies one matching path. Middle vertices in B_u and B_v give E P_uv and P_uv E. Each other attached group B_w gives P_uw P_wv. A fixed middle vertex supplies none: the sole fixed neighbour of x is u, and u has no neighbours in B_v. These exhaust the vertex partition. Endpoints are distinct from x, and C4-freeness permits at most one common neighbour per endpoint, proving the bound.

This is a constraint on the color contingency tables and the ten inverse-paired permutations, independent of Q. The sum of all nine entries on its left is 10+2+2+9=23, so its total slack is exactly four.

## Capacity of walks into the residual graph

For x in attached orbit (u,a), let e(a) be 0 at label 0 and 1 otherwise. Let h_u(a) count the other groups v for which pi_uv(a)=0. This is independent of the chosen vertex x, by equivariance. Then

    h_u(0) <= 2,     h_u(1) <= 3,     h_u(2) <= 3.

To prove it, count length-two walks from x into R, which has 30 vertices. Through the 4-e(a) residual neighbours of x there are 4(4-e(a)) walks. Through the four other attached groups there are 12+h_u(a) walks, because a matched attached vertex has three residual neighbours and an unmatched one has four. If e(a)=1, the internal partner of x is matched and contributes three more walks. The fixed neighbour u contributes none. The total is therefore

    28 - e(a) + h_u(a) <= 30.

All these endpoints are distinct from x, so the inequality follows again from C4-freeness. This gives the stated bounds. Also h_u(0)+h_u(1)+h_u(2)=4, since each of the four permutations has exactly one preimage of label 0.

In particular, put an edge uv on the five group indices exactly when pi_uv(0)=0. This is an undirected simple graph, since the reverse permutation is inverse. Its degree at u is h_u(0), hence its maximum degree is at most two. Its components must therefore be isolated vertices, paths, or cycles. This gives a small structural restriction on the unmatched-to-unmatched matching pattern before choosing any matching phases modulo three.

Both arguments count actual two-step walks, so omitted matching phases cannot invalidate their necessity. Satisfaction does not guarantee distinct endpoints, a compatible lift, or a graph witness.
