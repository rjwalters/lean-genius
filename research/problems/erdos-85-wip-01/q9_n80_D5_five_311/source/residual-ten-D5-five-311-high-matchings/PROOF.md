# High-vertex matchings for residual-matching D5/s5 packings

Start from the3024 exact-rational-survivor roots of2464, all residual matching actions. Every high vertex has support size3, so its endpoint budget B=3+2-3=2. Each high neighbor costs2. Thus the high-high graph is a tau-invariant matching on ten vertices. Each low vertex has budget2 and can be adjacent to at most one high vertex.

Write rho for the residual matching involution and S_v for each high support. An edge v-w is allowed only when rho(S_v) and S_w are disjoint. This is exactly the additional C4 condition for such an edge: a residual/high pair could acquire both a residual and a high common neighbor precisely at an intersection of those sets. Symmetry gives the reverse condition. In a matching, no pair of high vertices can acquire a common high neighbor. Other common-neighbor counts are unchanged from the accepted support packing. Thus these pairwise edge conditions suffice for C4-freeness of this partial graph, without asserting any completion.

The recursion chooses the least remaining high tau orbit. It leaves that orbit unmatched, joins its two vertices if allowed, or matches it to another remaining orbit using either bijection when allowed. It then removes all affected orbits. This uniquely enumerates every invariant matching. There are at most312 on ten vertices: f(0)=1,f(1)=2,f(n)=2f(n-1)+2(n-1)f(n-2).

For an unmatched high vertex, residual-middle endpoints occupy rho(S_v), and exactly five remaining W neighbors are low. Their singleton supports are distinct. The defect row Q_v is therefore any two-element subset of the other seven residual endpoints, avoiding zero-q columns. For a matched vertex, middle endpoints occupy the disjoint six-set rho(S_v) union S_w and four low neighbors cover its complement, leaving Q_v empty. All low counts are positive and each low endpoint has budget2, so these complete conditional domains require no other support restriction.

Reject a matching if a domain is empty, if entries forced by all choices exceed q in a column, or if low demands forced by every Q choice exceed the number of low vertices supported at an endpoint. The latter holds because a low vertex has at most one high neighbor. Remaining domains are necessary only.

The original30-second stage completes in2.300115 seconds on all3024 roots. It enumerates37408 allowed matchings;30256 survive the conditional-domain filters. Every root has a survivor. No joint-row feasibility or graph realization is claimed. No capped domain is retried, and no global or Lean conclusion follows.
