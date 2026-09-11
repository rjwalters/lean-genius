# Exact cover by ten necessary fixed-center groups

From each center-domain case, choose one option for each of the five labeled311 groups, with disjoint low-orbit sets. The remaining15 low orbits must be partitioned into five permitted111 triples. Enumerate high options by the currently most constrained group, and cover remaining orbits by permitted triples, always selecting a remaining orbit with the fewest eligible triples. Memoization changes only repeated work. Every actual fixed-center partition supplies such a cover.

The original30-second aggregate stage completes all41 cases in0.030768 seconds. Two have no cover (already empty high domains);39 have explicit cover witnesses. Each witness uses all25 low orbits exactly once, with five labeled pairs and five triples. The41 root identifiers exactly match the complete domain input and the41 positive edge-relaxation models from2486.

These witnesses are necessary local group placements, not complete center assignments or graph realizations. The fixed graph on centers, cross-group restrictions, simultaneous internal-edge choices and the rest of the low graph remain unresolved. Later work must permit all valid covers rather than exclude a case by failing only its saved example. No cap retry, global Erdős85 result, or Lean theorem is claimed.
