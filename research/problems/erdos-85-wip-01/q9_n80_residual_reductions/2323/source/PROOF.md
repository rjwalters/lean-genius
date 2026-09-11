# No degree-three attached vertices for residual pattern (0,2,2,3,3)

Assume the N80/F10 cubic-fixed branch and residual orbit degrees (0,2,2,3,3). Let I be the unique isolated residual orbit, consisting of two vertices. Every other residual vertex has degree at least two. Every attached vertex u has residual degree k(u)>=1 and8-k(u) neighbors in W.

Counting distinct two-step endpoints in R gives the exact budget

 sum over r in N(u) intersect R of (d_R(r)-1)
 + sum over w in N(u) intersect W of (k(w)-1) <=2.

This identity is the same as in2251/2297, but here the residual terms may be negative at isolated vertices. We do not assume they are nonnegative globally.

Suppose v is attached with k(v)=3. It has five W-neighbors. For any such neighbor u, the second sum includes k(v)-1=2 and its other terms are nonnegative. If u had no residual neighbor in I, every term in its first sum would be at least one, and there is at least one such term because k(u)>=1. The left side would be at least three, a contradiction. Thus all five W-neighbors of v meet I.

The residual neighborhoods of different W-neighbors of v are disjoint: a shared residual vertex r would give v and r two common W-neighbors, hence a C4. Five disjoint nonempty intersections with the two-element set I are impossible. This excludes k(v)=3 and therefore

 n_311=0.

## Consequences for the remaining attachment domain

The accepted2251 identities now give

 n_211+2n_221=5,
 e_E(R,W)=2.

Thus there are exactly five high attached involution orbits, all of residual degree two. Their possible center-type counts are (n_211,n_221)=(5,0),(3,1),(1,2).

A degree-two attached vertex not meeting I can only meet the two degree-two residual orbits: its first budget sum is at most two, and both positive support degrees are at least two. Those supports are in distinct involution orbits by C4-freeness. A degree-two attached vertex meeting I has its other residual neighbor in a degree-two or cubic orbit. Consequently the high-orbit support types are exactly constrained to (0,2),(0,3),(2,2). This is a necessary list; no realizability is asserted.

The no311 argument uses only the residual degree pattern and the exact endpoint budget, not the pending three-type residual classification2321 or any pending no-isolation proof. It gives a structural restriction, not an exclusion of02233. No finite search, full graph solver or Lean formalization is used.
