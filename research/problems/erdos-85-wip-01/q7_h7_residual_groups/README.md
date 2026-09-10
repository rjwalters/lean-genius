# H7 residual host-group defect constraints

Assume a complete high0 host assignment as in reviewed2064 and the pair-host reduction2066. Write H=N(high0), with two weight1 singleton hosts and six weight2 pair hosts. The perfect matching on H gives mate(h). The34 outside-low vertices partition into groups G_h of sizes n_h=6-w_h. All their high incidences and their unique H neighbour are fixed; remaining edges are only among these34 vertices. A vertex u of weight w_u still needs6-w_u such edges.

For u in G_h, the group G_mate(h) is forbidden: an edge u-v into it would form the cycle h-u-v-mate(h)-h. For every nonzero high colour j in u's support, G_P0j is forbidden too: u and host P0j already share highj, and an edge from u to one of that host's guests would give them a second common neighbour. These1+w_u forbidden groups are distinct, because the host h's matching partner and its guests have disjoint high supports. There are therefore7-w_u remaining groups.

Vertex u has at most one neighbour in any one group: two would give u and that group's host two common neighbours. Since its residual degree is6-w_u, u has a neighbour in every available group except EXACTLY ONE. Call the omitted group its defect group. This statement concerns any full completion, not the current partial graph.

For any two hosts h,k which are not matching partners, let a_hk count the vertices of G_h allowed to meet G_k under these rules. If k is a singleton host, every vertex in G_h is allowed, so a_hk=n_h. If k=P0j, exactly one guest in G_h contains j: the matching partner of h is not k, so j is an as-yet-required high colour at h, and the host assignment covers it exactly once. Thus a_hk=n_h-1. Both cases give

    a_hk = 7 - w_h - w_k.

For matching partners a_hk=0. In particular the8x8 matrix A is symmetric, independent of the particular pair-host assignment, and has diagonal5 on singleton groups and3 on pair groups.

Let d_hk count vertices of G_h whose unique defect group is G_k. For h!=k the actual residual edge count between the two groups is a_hk-d_hk. Symmetry of this count and of A forces d_hk=d_kh. Also sum_k d_hk=n_h, since each vertex in G_h has exactly one defect. Therefore column sums are n_k too: exactly n_k outside vertices omit group G_k.

For h=k, the number a_hh-d_hh is twice the number of edges inside G_h, hence is even. Since a_hh is odd, d_hh is odd and at least1. Every host group consequently has at least one vertex which omits its own group. Bounds are d_hh in{1,3,5} for a singleton group and{1,3} for a pair group. Matching partners have d_h,mate(h)=0. All entries satisfy0<=d_hk<=a_hk.

These are universal necessary constraints on any full H7 completion of a high0 host assignment. They do not by themselves imply the existence of a completion or exclude a host assignment or empty-graph class. They may support future degree/host-group matching filters; none is run here. Historical capped host and empty-class searches remain unchanged.

The finite audit checks the algebra directly on the two independently constructed sample host assignments from the bounded raw census: exact guest colour coverage, forbidden-group counts, available-row counts, symmetry/formula for A and the column deficit identity. It uses no hypothetical completed graph and does not claim to verify a defect matrix instance. Independent proof review is requested; no Lean theorem is asserted.
