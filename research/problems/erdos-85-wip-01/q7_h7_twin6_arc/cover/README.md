# Independent complete twin6 host-census verification

For the complete twin6 profile (pair counts2,1,2,2,2,2,2,2), an independent raw counting recurrence assigns host matchings in reverse order with no symmetry pruning. Memoization keys only the host position and already used K6 edge set. Every matching of the exact host size on its allowed colour set is included, and host choices must be disjoint. Counts sum to15, so a terminal union is all15K6edges. The recurrence gives125280 labelled assignments, evaluating5655 distinct states.

Separately, generate the full48element stabilizer preserving the high0 matching and this count profile. Expand all2640 published representatives under this action. Every representative and image satisfies the allowed matching domains and exact cover. The2640 image sets are pairwise disjoint and their union has125280 labelled members, equal to the independently computed complete raw domain. Hence the representatives cover every assignment exactly once up to symmetry.

Orbit sizes are6(two orbits),12(nine),24(forty-three),48(2586). Nontrivial stabilizers explain why2640*48 overcounts the raw domain. Each representative is also the lexicographic minimum of its own orbit. This verification does not use the author's prefix symmetry pruning or enumerate any capped profile. It finishes below100000state/60second limits, with no UNKNOWN or retries.

All six original census package pins are checked before and after. The result verifies the twin6 source census, not its graph exclusions; the61local and2579arc negatives are a separate review2074. Combining those exact2640negative assignments with this cover would exclude twin6. H7 and global/Lean conclusions require further joins.
