# Full automorphism order at most twelve for N78 candidates

Let G be a simple C4-free nine-regular graph on78 vertices and A=Aut(G). The accepted bound2408 leaves possible orders1,2,3,4,6,8,12,16. We exclude order16 by composing exhaustive accepted structural covers and the independently accepted branch exclusions listed below, including the final partial-incidence exclusion2485.

Suppose |A|=16. The matching normal form2419 gives an invariant S=3K2 of size6, a uniquely attached set W of size48, and residual set R of size24, with quotient[[1,8,0],[1,5,3],[0,6,3]]. Its S-orbits are either2+2+2 or2+4. The first is excluded by2447. The center-action cover2450 then gives kernel order2 or4 for the remaining2+4 action; it includes the faithful-action exclusion as an accepted premise. The residual profile is always8+16 or8+8+8.

If the kernel has order four, review2479 excludes residual8+16. Its input cover2474 exhausts the required normalized incidences, and its complete local-neighborhood check excludes all1152 inputs times three possible matching directions on S4. Review2482 independently excludes residual8+8+8 by its stabilizer-class, saturated cross-pair and six-vertex cubic-fiber argument. Thus the kernel-four case is impossible.

If the kernel has order two, review2477 reduces all possible center images and extension laws to four labeled actions. Two are dihedral law100 actions, both excluded by2481. The two remaining law111 actions have semidihedral abstract group and edge-axis involution images on S4. Review2484 excludes residual8+8+8 for both characters, with the hypotheses of2482's residual argument separately established. Review2485 excludes residual8+16 for both characters: all six possible residual Y connection sets, both S2 characters, all normalized W0 incidences and all105 possible W2 origin triples are covered; every branch already contains a C4 in the required partial graph. Thus no kernel-two action remains.

These cover all full order16 actions, so |A|=16 is impossible. Combining this with2408 yields

    |Aut(G)| in {1,2,3,4,6,8,12}, and hence |Aut(G)| <= 12.

This does not assert that the order divides twelve: order eight remains in the upper cover. No remaining order is claimed realizable or excluded here. In particular asymmetric candidates, N78 existence, N80 and Erdős85 globally remain open.

This composition uses only independently accepted paper proofs and complete finite domains. It does not resume or reinterpret any capped or UNKNOWN search, and it does not substitute a selected feasible witness for an exhaustive domain. The accompanying premise snapshot, source hashes and review states provide the exact dependency record. No new graph enumeration or Lean formalization occurs in this assembly.
