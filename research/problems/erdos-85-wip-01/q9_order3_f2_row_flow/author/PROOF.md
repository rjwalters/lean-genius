# Local residual-row capacity screen for F2 tables

Input is all672 tables of accepted2221, using2219. Represent each of the20 residual3-orbits by a word(a,b), with a,b in{0,1,2,3}, where3 denotes a missing attached neighbour. Table entries give multiplicities of fully attached words. In the full crossmatching case add either one(3,3) word or the two distinct missing words(i,3),(3,j), as prescribed by2221.

Fix an origin orbit with word(a,b). Its residual degree is d=9-[a<3]-[b<3]. Its quotient row has at most one entry2 and no diagonal1, by2219. Counting two-step walks into each A label x gives the upper bound

 sum_target q_target*[target_A=x] <= 3 - [a is nonzero/present and x=3-a] - [b present and P(x)=b].

The analogous B bound is3 minus the internal matching term at b and the A--B matching term from a. These are capacities on three A and three B margins. Targets missing the corresponding attached neighbour have no bound from that group; the implementation uses d as a harmless upper bound.

For a row with no2, remove the origin copy (diagonal1 forbidden). Select d other orbit copies with at most the available multiplicity of each word and within both sets of margin bounds. This is integral bipartite capacity flow on four left and four right labels, where an edge's capacity is the remaining multiplicity of that word. Source/sink capacities are the marginal bounds. An integral flow of value d is exactly such a selection.

For a row with one2, choose the double target's word, and whether that target is the origin when allowed. Subtract2 from its two margin capacities and from the required row sum. Remove that target from the available ordinary copies; remove the origin as before unless it is itself the double target. If the double target has both attached labels, forbid all ordinary copies of that same word: otherwise two distinct targets share two attached groups and get at least2 common-middle paths through the origin, contradicting Q²+h<=3. A double target missing a label does not cause this restriction. The residual capacity-flow test selects the remaining d-2 ordinary targets.

These options include every necessary row profile. A table would be excluded if one of its nonempty word types had no supported row, even after trying every double-target option. An integral local row does not establish compatibility with other rows, symmetry of Q, all codegrees, or phases.

Original60s aggregate cap, no retry. All672 tables COMPLETE in about0.081s,6838 flow calls. Every table has a supported row for every type: zero exclusions. The receipts record the tested options and achieved flow values. The result establishes that this local screen alone cannot advance the elimination; it supplies no graph witness. No earlier capped search was repeated.
