# Odd-degree involutions cannot have a tight fixed star

Let d>=3 be odd and let F be even with 2<=F<=d-1. There is no simple d-regular C4-free graph on

    N=d(d-1)+F

vertices admitting an involution whose fixed set has size F and induces K1,F-1.

This is a paper theorem generalizing the N78/F6 and N80/F8 star arguments. Regularity is an explicit hypothesis; no unproved regularity theorem for arbitrary parameters is used.

## Boundary partition

A moved vertex cannot have two fixed neighbors: together with its distinct involution image, those neighbors would form a four-cycle. Thus the sets B_v of moved neighbors of fixed vertices are disjoint. Let R be the moved vertices without a fixed neighbor. If c is the fixed star center, write

    m=d+1-F=|B_c|.

Every fixed leaf has d-1 moved neighbors. Since the fixed degree sum is 2(F-1),

    |R| = N-(d+1)F+2(F-1)
         = d(d-1)-(d-2)F-2
         = (d-2)(d+1-F)
         = (d-2)m.

Here m>=2, and d-2 is positive and odd.

## Central saturation

A vertex x in B_c has only c as a fixed neighbor, hence d-1 moved neighbors. It has no neighbor in any leaf attached set: such an edge would form a C4 through the corresponding adjacent fixed centers. It has at most one neighbor in B_c, because two would give x and c two common neighbors. Therefore x has at least d-2 neighbors in R.

Every residual vertex has at most one B_c-neighbor by the common-neighbor bound with c. Summing the m lower bounds gives m(d-2)=|R|, so equality holds everywhere. In particular B_c induces a perfect matching, each x in B_c has exactly d-2 residual neighbors, and the sets

    R_x=N(x) intersect R

partition R into m classes of odd size d-2.

## Residual saturation and parity

Fix r in R_x. It has at most one neighbor in each class R_y, including its own, since two would give r and y two common neighbors. If x' is the matching partner of x inside B_c, there are no edges between R_x and R_x': any such edge closes a C4 through xx'. Thus r has at most m-1 residual neighbors.

On the other hand r has no fixed neighbors and at most one neighbor in each of the F attached sets. Its total degree is d, so its residual degree is at least d-F=m-1. Equality follows. Every allowed class must supply exactly one neighbor; in particular r has exactly one neighbor in R_x.

Every induced graph on R_x is therefore one-regular on the odd number d-2 of vertices. This is impossible, because the handshake identity would make its vertex count equal to twice its edge count.

The contradiction proves the theorem. At d=9 it includes (N,F)=(74,2),(76,4),(78,6),(80,8), subject to the stated regularity and fixed-star hypotheses. The last two recover the independently studied q9 cases. No assertion about arbitrary involution fixed graphs, other orders, or the full Erdős 85 problem follows by itself. No computation or graph solver is used, and the general theorem is not yet formalized in Lean.
