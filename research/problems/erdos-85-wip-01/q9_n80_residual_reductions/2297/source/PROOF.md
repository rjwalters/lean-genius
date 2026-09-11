# At most two cubic residual orbits when there is no isolation

Assume the N80/F10 cubic-fixed branch of2251 and no isolated residual vertex. Use the maximum-degree bound submitted as2295, so residual degrees lie in{1,2,3}. The involution has five residual orbits of size two. Let a,b,c be the counts of residual orbits of degrees1,2,3 respectively.

For an attached vertex u of residual degree k(u), count all nonreturn two-step walks ending in R. Its8-k(u) attached neighbors v contribute k(v) each, and its residual neighbors r contribute d_R(r) each. Its fixed neighbor contributes none. C4-freeness makes all endpoints distinct among the ten residual vertices. Keeping the full terms, rather than just their lower bounds, gives

    sum_{r in N(u) intersect R}(d_R(r)-1)
      +sum_{v in N(u) intersect W}(k(v)-1) <=2.       (1)

Both sums have nonnegative terms, because there is no isolation and every attached vertex has residual degree at least one.

If u meets a residual vertex of degree three, its contribution alone is two. Every attached neighbor of u must therefore have residual degree one. In contrapositive form: an attached vertex v with residual degree at least two has no W-neighbor that meets any cubic residual vertex.

There is at least one such high attached vertex v. If all attached degrees were one, the deficit sum in2251 would be zero, hence the sum D of the five residual orbit degrees would be15. With maximum degree three all five would be cubic, contrary to2251's exclusion of residual degrees entirely in{2,3}.

The high vertex v has8-k(v)>=5 neighbors in W, since k(v)<=3. Each of them has at least one residual neighbor, and all of those residual neighbors are noncubic by the preceding contrapositive. The residual neighborhoods of different W-neighbors of v are disjoint: an intersection would give v and that residual vertex two common W-neighbors. Thus at least five noncubic residual vertices exist. Their number is even under the free involution, so at least six exist. Consequently

    c <=2.

Also a>=1, since2251 excludes all degrees in{2,3}. Therefore this branch has at least one leaf orbit and at most two cubic orbits.

## Deficit constraint on degree-two orbits

The exact identity of2251 is

    e_E(R,W)=30+2 sum_j d_j(d_j-4)+4 n_311.

For degrees1,2,3, and a+b+c=5, it simplifies to

    e_E(R,W)=4 n_311-2b.

Hence n_311>=ceil(b/2). The incidence deficit equation is

    n_211+2n_221+2n_311 = 5+a-c.

These are necessary restrictions on the no-isolation branch. They do not exclude residual leaves, specify a full graph, or settle Erdős85. The proof is paper counting without finite enumeration, capped-search dependence, or Lean formalization. The maximum-degree premise2295 needs independent acceptance before this consequence is accepted unconditionally.
