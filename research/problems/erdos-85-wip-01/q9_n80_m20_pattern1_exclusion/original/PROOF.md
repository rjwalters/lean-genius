# Proposed exclusion of the N80/m20 internal0-cross333 quotient

Premise: accepted2147 necessary quotient cover. Consider four independent20-vertex cyclic orbits, with cross degree3 between every pair.

Fix orbit A labelled by Z20. Its three cross-offset sets, one for each other orbit, each have size3. Ordered differences of distinct offsets in one set record the two-step paths from a fixed vertex A0 to other vertices in A through that other orbit (the sign convention does not affect the argument). Each set contributes3*2=6 ordered differences, so together there are18. C4-freeness makes all18 differences distinct and nonzero.

The union of ordered differences is invariant under negation. Its complement within the19 nonzero residues therefore has size one and is also invariant under negation. The unique missing residue must equal its own negative, hence is10, the only nonzero involution of Z20. In particular all ten odd residues must occur exactly once among the ordered differences.

A three-element offset set with r odd elements contributes exactly2r(3-r) odd ordered differences. For r=0,1,2,3 this is0,4,4,0, always divisible by4. The three sets together must therefore contribute a multiple of4 odd differences. They contribute exactly10, a contradiction.

Thus this internal0/cross333 quotient cannot lift to a C4-free graph. This excludes only the first2147 quotient type. No solver run, CNF modification, full N80/m20 exclusion or Lean theorem is claimed here.
