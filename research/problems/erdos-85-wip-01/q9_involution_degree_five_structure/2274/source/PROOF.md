# No residual-degree-three attached vertex in the degree-five branch

Assume the N80/F10 cubic-fixed setting of accepted review 2259, with central residual edge xx', four same-side leaves L,L', and a matching of size t on each side, where t is zero, one, or two. The involution swaps the two sides. Attached groups have six vertices and their orbit residual-degree patterns were previously restricted to 111,211,221,311.

Let u be any attached vertex and S its residual neighborhood. It cannot contain two vertices of L, since those already have x as a common neighbor and u would give a second. Similarly S contains at most one vertex of L'. It cannot contain both x and x': the distinct attached vertex tau(u) would also neighbor both, producing a C4. Finally if x belongs to S, no vertex of L' can belong to S, since x and every vertex of L' already share x'. The symmetric statement holds for x'.

If S contains no central vertex it has size at most two, one per side. If it contains a central vertex, it contains at most one further vertex, on that same side. Hence every attached residual degree is at most two. Type 311 is impossible throughout the entire residual-degree-five branch, for all t.

## Exact central attachments

Accepted review 2259 gives sum k(u)=8-2t over the four attached neighbors of x, and each k is positive. Since now k<=2, exactly 4-2t of these four vertices have k=2, and the others have k=1.

If u neighbors x and has a second residual neighbor a, that neighbor lies in L by the preceding proof. Moreover a must be unmatched in the matching on L: if a had matching partner b, then x and a would already share b and would also share u, a C4. Two such u cannot choose the same a, because they would be two common neighbors of x and a. There are exactly 4-2t unmatched vertices of L, so the resulting map is a bijection from the central attached vertices of residual degree two onto the unmatched leaves. The involution gives the corresponding bijection on the other side.

Thus for t=0 all four groups meeting the central orbit have a degree-two orbit there; in particular all four are exceptional (211 or 221). For t=1 exactly two of the four central attached neighbors have degree two. For t=2 none do, recovering the earlier special restriction.

The count identity now simplifies to n_211+2 n_221=6-2t. At t=0 the possibility n_221=3,n_211=0 is impossible because only three exceptional groups would be available for the four centers meeting the central orbit. The other count possibilities are not asserted realizable or excluded here.

## Finite local check

For each of the three explicit residual graphs, check all 1,024 subsets S of R. A possible attached residual neighborhood must be disjoint from tau(S), and no two members of S may already have a common residual neighbor. The first requirement follows because u and tau(u) cannot share a residual neighbor: otherwise that neighbor and the fixed center of B_u would have two common attached neighbors. These are necessary conditions only. The checker confirms that the maximum subset size is two, and that the allowed pairs containing x are exactly its unmatched same-side leaves, numbering four, two, zero for t=0,1,2.

This proof is a restriction on attached neighborhoods, not a full exclusion of t=0 or t=1 or a graph construction. It uses no full-graph solver and is not formalized in Lean.
