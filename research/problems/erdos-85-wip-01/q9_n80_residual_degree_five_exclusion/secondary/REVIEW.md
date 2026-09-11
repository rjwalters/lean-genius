# Independent secondary audit of the paper degree-five exclusion

I independently derived the leaf-sum identity and the t=1 star contradiction while codex-sol-2 wrote the full proof. I then read the frozen full source. The argument is sound, including all t values; no finite negative receipt is needed.

For f in P, summing HY over leaves gives 3+deg_P(f)-sum_neighbor delta, and summing YQ gives a_f. Every degree-two attached orbit contributes twice to all five T columns. Removing its central contribution 1+delta_f-deg_P(f) yields the stated inequality delta_f+sum_neighbor delta+a_f>=4. This uses cardinalities of missed sets, not sums of their labels.

For matching P, the summed delta coefficients are two on P, two on the two M endpoints, and one on the other four M vertices. Thus the upper bounds used in all three t cases are valid. At t=1 equality would force delta_P=0, contrary to two distinct central degree-two attached orbits in P groups. The t=0 and t=2 numerical bounds are strict contradictions.

For star P, summing the three leaf rows counts every noncentral delta once and the central delta three times. At t=0 this is10 rather than the required12. At the center itself, its empty missed row and T_c0=0 force the leaf deltas to sum to at least two. This immediately excludes t=2 and at t=1 forces every M group to have delta zero.

The final attachment argument is valid: the star center's only allowed cross groups are precisely those six ordinary M groups, so every cross slot is full. Nine-regularity gives k_R=2-internal_degree for each attached vertex there. Every k2 vertex therefore misses its internal slot and has the center as its unique fixed E-target. A k2 neighbor of the central residual vertex would contradict T_c0=0. Thus the two central attached neighbors are exactly the two k1 vertices, which must be internally matched to one another, making the stated C4.

The full proof depends only on accepted2259,2272,2274,2277, each checked in the room as accepted. It has no dependence on the defective2281 producer, its counters, or its repaired independent finite audit. It excludes residual degree five only in the N80/F10 cubic-fixed branch. It neither solves Erdős85 nor claims Lean formalization. The primary review2285 remains with codex-sol-1; this secondary audit does not resolve that review.
