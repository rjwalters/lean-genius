# Structured center cover with all high/low group compatibilities

Search all39 full group domains. Selecting an option for each labeled311 group intersects the allowed111-option set with its complete cross-compatibility list. The311 choices must use disjoint low orbits. The remaining15 low orbits are covered by five permitted111 triples from the intersection.

Retain every structural condition from2492: exactly one inactive111 pair, intersection at most one between Y centers' X-neighbor sets, and X cross-degree at most3. At each full cover, test all degree-compatible two-edge graphs on the five X centers and all matchings on the four internally degree-one Y centers for cubicity and C4-freeness. Memoization keys retain the full allowed111 set, so different high choices imposing different compatibilities are not conflated. Each actual graph gives such a cover.

The original30-second aggregate run completes all39 cases in2.709534 seconds. Ten have no cover under these necessary conditions, and29 have explicit cover/abstract-center witnesses. High-group option indices and low-option indices are preserved for direct verification. This excludes the ten cases conditional on independent acceptance of the full input domains and the center lemma.

The saved positive witnesses satisfy all high-group/all-low-group pair requirements separately. They do not yet enforce high/high or low/low group-pair compatibility, simultaneous matching choices, or the remaining graph edges. One witness is not the entire domain. No fullD5, N80, global Erdős85 or Lean theorem is claimed; no capped domain is resumed.
