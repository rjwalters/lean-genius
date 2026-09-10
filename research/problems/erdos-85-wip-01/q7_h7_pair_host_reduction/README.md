# H7 host assignments reduce to15 pair placements

Use the two N(H0) matching forms submitted as2064. The eight hosts are S0a,S0b,P01,...,P06; their remaining outside-low capacities are5,5,4,4,4,4,4,4. Their34 guests are the fifteen Pij with i,j>0, two singletons of each colour1,...,6, and seven empties.

For a host h let m(h) be its already fixed matching partner in N(H0). Let R_h be the high colours1,...,6 not contained in the support of m(h). High colour0 is already covered by m(h). The outside guests of h must partition R_h by their supports, since BC=J demands exactly one high-colour common neighbour. Consequently the pair guests assigned to h form a matching of the complete graph on R_h.

Equivalently assign each of the15 edges ij of K6 to one of the eight hosts, with no two edges at a host sharing an endpoint, and with both endpoints in R_h. This is a proper edge colouring by named hosts with forbidden colours at each edge. These requirements are necessary. Direct graph checks may impose further constraints; no sufficient full-completion claim is made.

For any fixed nonzero colour i, exactly one matching partner m(h) contains i: P0i is the only vertex of N(H0) carrying that colour. Hence precisely seven hosts initially have an i slot. The five assigned pair vertices Pij consume five distinct such slots. Exactly two remain. These name the two colour-i singletons uniquely up to swapping their original labels. Thus there is no separate singleton-host assignment search after the pair placements.

Let p_h be the number of pair guests and K_h the remaining host capacity. Singleton count is |R_h|-2p_h, so the empty count is

    e_h = K_h - p_h - (|R_h|-2p_h)
        = p_h - (|R_h|-K_h).

Put delta_h=|R_h|-K_h. The exact allowed pair range is delta_h<=p_h<=floor(|R_h|/2). In the twin-adjacent seed all eight deltas are1. In the other seed they are0,0 for the two singleton hosts,2,2 for the two pair hosts matched to singletons, and1 for each remaining pair host. In both seeds sum(delta)=8; as sum(p)=15, exactly seven empty positions remain automatically. Each pair host has at most one empty position and each singleton host at most two, agreeing with the established H7 incidence bounds.

Empty vertices can be named consecutively within these host groups, applying the naming to their entire as-yet unknown graph. This replaces a raw34-guest assignment by fifteen constrained pair placements. Any subsequent use of an empty-graph isomorphism census must allow the relative relabellings; it cannot simultaneously fix arbitrary host-group and empty-census labels.

The checker finds just one example for each seed (17 recursion nodes each), assigns the singleton positions and empty groups, and directly verifies all49-vertex common-neighbour bounds, BC=J in high0, and degree7 at all eight hosts. Other vertices remain incomplete. No full colouring census, H7 class exclusion, solver run or old capped retry is claimed. The mathematical parametrization and its finite sanity checks await independent review.
