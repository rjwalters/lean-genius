# Nonidentity involutions have at most ten fixed vertices at78 or80

Let G be C4-free on N in{78,80} vertices with minimum degree at least9, and let tau be a nonidentity automorphism with tau²=id. Accepted below-square regularity makes G9regular. Let H be its induced fixed graph, F its order, r_v its degrees, and S=sum_v r_v.

Period-two pairing on the nine neighbors of a fixed vertex gives r_v odd, hence r_v in{1,3,5,7,9}. The moved set is nonempty, and the accepted moved-degree and tight-cardinality bounds give at least58 moved vertices. Also F is even. Thus F<=20 at78 and F<=22 at80.

## Boundary and residual capacity

A moved vertex has at most one fixed neighbor. Put B_v=N(v) outside the fixed set; these sets are disjoint and have sizes9-r_v. Let R be the vertices with no fixed neighbor. Then

    |R|=N-10F+S >=0.

The fixed graph is C4-free, so its cherry count gives sum r_v(r_v-1)<=F(F-1). Cauchy therefore yields S²-F*S<=F²(F-1). Writing L=10F-N, we have S>=L. For each even F>=14 in the above ranges, L>=F and

    L²-F*L-F²(F-1)>0,

as checked by the short exact arithmetic table. Monotonicity of S²-F*S for S>=L contradicts the cherry bound. Thus F<=12.

There is an additional capacity inequality for every fixed vertex v:

    (9-r_v)(8-F+r_v) <= |R|.

To see this, each x in B_v has exactly eight moved neighbors. It has at most one inside B_v, and at most one in any other B_u, since two would give two common neighbors with the fixed centre u. If u and v are adjacent, there are no B_u--B_v edges: such an edge closes the four-cycle x-v-u-y-x. Thus at most1+(F-1-r_v)=F-r_v moved neighbors of x lie in the union of attached sets. It has at least8-F+r_v neighbors in R. Summing over B_v gives the displayed lower bound. Each R vertex meets B_v at most once, giving the upper bound |R|. Negative lower bounds cause no problem; when B_v is empty the inequality is trivial.

## Excluding F=12

Enumerate the five counts of degrees1,3,5,7,9, with sum12. Impose S>=120-N, the cherry bound<=132, and the displayed residual capacity for every occurring degree. check.py uses exact integer arithmetic over all such counts. AtN78 no profile survives. AtN80 exactly two survive:

* eight degree3 vertices and four degree5 vertices (S44, |R|4);
* one degree1 vertex, ten degree3 vertices and one degree9 vertex (S40, |R|0).

Both contradict C4-freeness of H. For any vertex v of H, the nonreturn two-step count sum_{w in N_H(v)}(r_w-1) is at most11. In the second profile the degree9 vertex has at least eight degree3 neighbors, giving at least16, impossible.

In the first profile a degree5 vertex cannot neighbor another degree5 vertex: all its neighbors have degree at least3, giving at least10 nonreturn paths, and one degree5 neighbor raises this to12>11. Thus the four degree5 vertices form an independent set and send20 edges into the other eight vertices. Let h_i count their neighbors at each of those eight vertices. Then sum h_i=20. Since pairs of high-degree vertices have at most one common neighbor, sum h_i(h_i-1)<=4*3=12, hence sum h_i²<=32. Cauchy gives400=(sum h_i)²<=8*32=256, a contradiction.

Therefore F<=10. Since F is even, the only counts not excluded by this argument are0,2,4,6,8,10. No surviving count is asserted realizable. This restricts nonidentity involutions only; it does not exclude the underlying graphs or solve Erdős85. It is a paper argument with a small exact degree-profile check, not a new graph search or Lean theorem.
