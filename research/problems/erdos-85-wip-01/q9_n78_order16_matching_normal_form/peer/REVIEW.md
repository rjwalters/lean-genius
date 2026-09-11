# Review2419: PASS full order16 necessary matching normal form

All author/input hashes verified and2257/2315/2412/2263/2269 freshly PASS. The exact local-regularity hypotheses of2263 and2269 are discharged by the new argument rather than assumed for nonabelianH.

By2412 the normal order8 point stabilizer H has a fixed matchingF of size2/4/6. Its local neighbor actions are1+8 or1+4+4. In the split caseH isD8 with two faithful four-actions. Their point stabilizers are reflection subgroups, since the central order2 subgroup would act trivially. D8 has two reflection conjugacy classes. Each reflection fixes two points in its own class's coset action and none in the other. The two actions must use opposite classes, so every reflection fixes exactly two neighbors outsideF at every split vertex.

Splitness is A-invariant by normality ofH. IfF has4 vertices, a split vertex has a distinct split partner in its size2 A-orbit. A reflection fixes allF and two outside neighbors of each. Those outside sets intersect in at most one point by C4-freeness, hence contribute at least3 additional fixed vertices, contradicting the bound6.

IfF has2 vertices, its matched endpoints are exchanged byA, hence both split if either is. They have no common neighbor: uniqueness of any such common neighbor would make it H-fixed, outside the two endpoints. A reflection then fixes exactly those endpoints and two outside neighbors each, with no overlap. The fixed graph has adjacent cubic endpoints lacking a common neighbor. It is neither a matching nor triangle-with-leaves, the only allowed six-fixed graphs. IfF has6 vertices, H is free outsideF by2412, directly forcing the regular-eight local action. These cases exhaustF.

Thus a matched pair satisfies both local regularity hypotheses of2263/2269. The resulting nonfree setS has6 vertices and is a matching; its complement is H-free. The definitions ofW48 andR24, their quotient and E-block conclusions match2269 (whose R24 is labelledZ in that source). Normality ofH makesS A-invariant, and the graph definitions makeW/R invariant.

The full stabilizer bound excludes A-fixed vertices. Consequently the six-point invariantS has orbit partition2+4 or2+2+2. Any outside point stabilizer intersectsH trivially and injects intoA/H of order2, so outside orbit sizes are8/16. This gives preciselyR partitions8+16 or8+8+8 and the stated W possibilities.

This is a necessary normal form, not an order16 exclusion. In particularF andS need not coincide. No finite search, graph realization or Lean theorem is asserted.
