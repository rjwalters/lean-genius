# H5/T1 bounded singleton-layer pilot

Select the first 30 of 211 joint-host survivors sorted by Cartesian per-colour host-domain size, preserving input order for ties. Enumerate ALL allowed host partitions, including every matching size, with cross-colour pair reuse forbidden. Singleton vertices of a colour are interchangeable before singleton edges are added, so bins use consecutive host labels and unused hosts follow.

For each host assignment, a singleton requires one low neighbour containing each high colour absent from its heavy neighbours, by BC=J. Remaining nonempty-support neighbours are singletons; therefore a missing colour c must be supplied by an edge to a singleton of colour c, with the reciprocal missing-colour requirement also satisfied. Empty-support neighbours supply no colour. Search chooses a missing incidence with the fewest legal partners. Every added edge obeys the total low-vertex degree upper bound 7 and introduces no C4 (no existing length-three walk between endpoints). All choices are exhausted before REJECT; caps produce UNKNOWN.

Result: 30 processed, 28 REJECT, 2 PASS, no capped cases, about 5.44 seconds. PASS saves a 49-vertex partial graph checked directly for C4-freeness, degree upper bounds, and BC=J on every nonempty-support low vertex. Empty-support vertices and remaining degree completion are not assigned. No full H5/T1 exclusion or Phase B queue change.

These are author results pending independent review. Reproduce `python3 singleton.py` beside results.json and joint-results.json. Prior frozen core and joint files remain unchanged. A REJECT concerns all host assignments for that core, not merely the first saved joint witness.
