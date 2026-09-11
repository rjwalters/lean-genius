# Low-neighbor parity excludes the empty-high D5/s5 subcase

Start from every one of the59 joint defect assignments in the upstream exact enumeration. Every low vertex has exactly one high neighbor. The low vertices are uniquely labeled by(v,r), high neighbor v and singleton residual support r: a repeated label would give v and r two common neighbors. There is one such low precisely when r lies outside rho(S_v) and Q_v. All50 labels are reconstructed.

A low vertex(v,r) has residual degree1, one high neighbor, and hence six low neighbors (its total degree9 also includes its unique fixed neighbor). The residual endpoints reached in two steps through its residual and high neighbors are rho(r) and the three elements of S_v. These four endpoints are distinct. Its residual defect row is empty. Therefore its six low neighbors have pairwise distinct singleton supports, exactly the other six residual endpoints.

Let M[r,e] be the number of low vertices supported at r that require a low neighbor supported at e. Necessarily M[r,e]=M[e,r] when r!=e, by counting the same undirected edges. For e=r, the low vertices requiring an internal neighbor each require exactly one. Thus their induced internal edges form a matching covering them, and M[r,r] must be even.

The checker reconstructs every low label and target-support set. All59 assignments satisfy off-diagonal balance but each has at least one odd diagonal count. An explicit support index and odd count are saved for every assignment. The original30-second stage completes in0.011358 seconds, with59 negative certificates and zero survivors. Its24 root entries exactly match the upstream cases, and every upstream assignment index occurs once.

Together with the five empty upstream joint domains, all24 remaining empty-high cases are excluded. The complete highmatching domain and symmetry cover, and2469's exclusions if any, cover every other original case. Thus in D5/s5 the high-high matching must be nonempty, conditional on independent acceptance of the upstream and current packets. This does not exclude nonempty high matchings, D5, N80 globally, or Erdős85. No Lean theorem or capped-domain retry is claimed.
