# Necessary attached pattern when residual orbit degrees are1,2,2,3,3

Assume the N80/F10 cubic-fixed branch of2251 and the displayed residual degrees. Let k(u) be an attached vertex's residual degree. The exact two-step inequality, derived by counting distinct endpoints in R, is

    sum_{r~u in R}(d_R(r)-1)+sum_{v~u in W}(k(v)-1)<=2.

All terms are nonnegative. An attached degree-three vertex cannot meet a cubic residual vertex: that term uses the entire budget, so its other two residual neighbors would both have to be leaves in distinct involution orbits, while only one leaf orbit exists. Thus a type311 group's high orbit covers precisely the leaf orbit and the two degree-two orbits. Its two low orbits cover the two cubic residual orbits.

The identity from2251 gives e_E(R,W)=4n_311-4, so n_311>=1. Two type311 groups are impossible. Each high orbit partitions the same six noncubic residual vertices into two triples. For two such partitions, their four intersections have total size six, so some intersection has size at least two. The corresponding two attached vertices would have two common residual neighbors, a C4. Hence n_311=1 and E(R,W) is empty.

The total deficit is four. Apart from the unique311 center h, the remaining exceptional types are either one221 or two211.

## The high orbit in B_h has no internal neighbor

Any attached vertex meeting a cubic residual vertex has only degree-one W-neighbors, by the exact inequality. In B_h all four low vertices meet cubic residual vertices. They cannot therefore be W-neighbors of either high vertex. The two high vertices cannot be internally adjacent either: they already share the fixed center h as a common neighbor with any other B_h vertex, so the induced graph on B_h is a matching; an internal high-pair edge would still be possible from this fact alone, but its high endpoint's exact inequality rules it out. Indeed its residual degrees1,2,2 use the entire budget, forcing every W-neighbor to have k=1. Thus both high vertices are internally unmatched.

Each high vertex has exactly two fixed E-targets, corresponding to its missing internal/cross slots. One is h because the internal slot is absent, and the other is a distinct exceptional center p not H-adjacent to h. Missing cross-slot counts are reciprocal, so one high orbit in B_p targets h.

## One221 is impossible

If p is the only other exceptional center, it has type221. The fixed center h receives its own high orbit of degree three and one B_p high orbit of degree two. Their total contribution to T over residual orbits is five. But Y_h is empty and all three H-neighbors of h are ordinary, since p is not adjacent to h. Their missed sets have total size six. Commutation would require six<=five, contradiction.

## Two211 centers and their fixed adjacencies

Thus the remaining exceptional centers are p,q of type211. The degree-three orbit in B_h targets{h,p}; the high B_p orbit targets h by reciprocity, and the high B_q orbit targets q by the remaining target capacity. All other groups are ordinary111.

Because E(W,R) is empty, commutation is equality HY=YQ+T at every fixed/residual entry. Summing at h gives6-sum_{g~h}delta_g=5. Since p is not adjacent to h, this forces h adjacent to q. The edge pq is not determined here.

Let epsilon=1 if p and q are H-adjacent and zero otherwise. At p the received high orbit has degree three, so the degree of its unique missed residual orbit is3-epsilon. At q the received high orbit has degree two, so its missed orbit has degree2-epsilon. These follow by summing the same equality, using delta_h=2 and delta_p=delta_q=1.

This restricts the1,2,2,3,3 residual pattern to one311 and two211 groups with the stated deficit targets and fixed adjacency. It is not an exclusion or a full graph construction. It uses no finite enumeration, capped-search outcome, or Lean formalization.
