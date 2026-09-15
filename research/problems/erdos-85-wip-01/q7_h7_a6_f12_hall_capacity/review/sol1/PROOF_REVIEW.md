# Independent Hall necessity review

Use the exact high-support coverage established in review2706. A pair vertex with current degree d has only high or empty neighbours, whose high supports are empty. If its missing neighbours include a singletons and b pairs, then a+b=7-d and a+2b=7. Therefore a=7-2d. The saved cases have d in {2,3}, giving demand3 or1. A singleton has at most 7 minus its current degree available incidences. The checker verifies all these type, support, high-independence and empty-degree hypotheses directly on each certified saved graph.

An actual added pair–singleton incidence must pass the fixed-neighbourhood four-cycle test. When the pair demand is three, the singleton must belong to an eligible triangle with an admissible two-edge matching of remaining high supports; this is necessary by review2706. The resulting eligibility relation is an overestimate of actual allowable incidences.

For any subset U of pair vertices, the demanded incidences total the sum of their exact singleton demands. Each singleton can receive at most its residual capacity, and at most one incidence from each eligible member of U by simplicity. Thus its contribution is bounded by the minimum of these quantities. A strict violation of the summed bound excludes the branch. Verification does not trust the flow algorithm used to discover U.

The independent checker rebuilds eligibility with sets, verifies every subset and both integer sums, and checks that the100negative plus29unclassified cases partition the previous129. This is a new global necessary cut; it does not regenerate row domains or run ARC and does not imply feasibility for survivors.
