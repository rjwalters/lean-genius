# Every N78 candidate has at least six automorphism orbits

Let G be a simple C4-free nine-regular graph on78 vertices. Accepted2329 establishes at least five vertex orbits under A=Aut(G). We assemble the independently accepted exclusion of exactly five orbits.

Accepted2335 gives the complete necessary five-orbit quotient cover, using accepted2332 to eliminate the mixed order-three cases. It leaves only order24 with sizes3,3,24,24,24, or order24/order48 with sizes6,12,12,24,24. Every remaining quotient is included in the saved lists; no unrealized quotient is assumed to exist.

Accepted2339 excludes all order48 cases. Its former conditional2335 premise is accepted. For order24 and sizes6,12,12,24,24, the twelve quotients split into eight single-attachment and four double-attachment types.

## The split-center case3,3,24,24,24

Accepted2334 supplies the complete structural and group/action cover. In particular both local regularity hypotheses needed for2269 are independently established in that action. Accepted2336 verifies all41 subgroup/action contexts and the complete set of22848 necessary partial graphs. Accepted2338 independently excludes necessary regular residual incidence for every one of those partial graphs. Its saved-domain condition is discharged by2336; no remaining graph action falls outside the cover. Thus the split-center case is impossible.

## The double-attachment case6,12,12,24,24

Accepted2340 gives the complete faithful action classification for the four double-attachment quotients, leaving the two signed S4 actions on the six matching centers and their nonmatching pairs. Accepted2342 excludes both by a forced internal matching edge on the twelve-vertex pair orbit, which creates a C4 with a center matching edge. No group/action alternative remains in this quotient type.

## The single-attachment case6,12,12,24,24

Accepted2343 supplies the complete group/action parameters for the remaining eight quotients. Its group exclusions use central-involution fixed-point bounds rather than incorrectly assuming a regular cubic residual orbit.

Accepted2345 independently covers all211 center actions and all four internal degrees, leaving exactly12928 partial graphs. Accepted2347 independently tests every such graph for the required first12-orbit incidence, leaving exactly896 normalized neighborhoods across448 partial graphs. Accepted2348 independently excludes the second12-orbit incidence for every one of those896 first-orbit configurations.

The older conditional wording in2347 and2348 is discharged:2345 is now resolved PASS with exact complete input coverage, and2347 supplies all possible first residual orbits to2348. The second normalization is justified by the invariance of the entire first-orbit translate family. The last obstruction already occurs before residual internal edges are added, so those edges cannot repair it. Therefore every single-attachment candidate is excluded.

## Conclusion and scope

All five-orbit order/size and quotient alternatives are excluded. Combined with accepted2329, every simple C4-free nine-regular graph on78 vertices has at least six automorphism orbits. All thirteen component review states listed in premise-states.json are freshly PASS; their source manifests are pinned in input-pins.json.

This assembly does not exclude graphs with six or more orbits, asymmetric graphs, N80, or Erdős85 globally. It combines paper arguments and independently verified finite necessary-model exclusions. It is not Lean formalization, launches no new graph search, and does not treat any capped UNKNOWN receipt as infeasibility.
