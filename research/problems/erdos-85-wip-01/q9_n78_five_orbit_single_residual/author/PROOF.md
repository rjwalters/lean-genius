# Necessary first12-orbit incidence on the saved single-attachment domain

Use accepted2343 for the action and normalization. The saved12928 partial graphs come from the coupling packet submitted as2345; completeness of that input domain remains conditional until independently accepted.

The required B12 orbit has two U and four V neighbors per vertex. Normalize a chosen U-neighbor to U1. For every possible order-two stabilizer L={1,l}, the U-neighbors are then exactly{U1,Ul}, and the V-neighbors are two left-L pairs. Every chosen neighbor must lie over a different fixed center.

The involution l must act freely on the six centers. Indeed B's six attached neighbors project bijectively to those centers. If l fixed a center, it would preserve the unique selected vertex over that center and hence fix an attached vertex. But both attached orbits are regular A-sets, so no nonidentity element fixes one. The checker therefore enumerates precisely all involutions with no fixed center and retains all such choices, without assuming they are conjugate.

For each l, exhaust every pair of left-L pairs in V whose four center labels complement the two U labels. Reject any two chosen vertices with an existing common neighbor in the partial graph. Finally require |X intersect gX|<=1 for all g outside L, using direct translated sets in the two separate regular copies. The condition inside L is not imposed, because those translates represent the same B vertex. This is the necessary model justified in2343.

The original aggregate30-second run completed in1.142 seconds. Every one of12928 roots is COMPLETE. Exactly448 roots admit neighborhoods, with896 saved normalized neighborhoods in total; all other roots are negative in this model. Positives occur only in three labelled D8 product models, at internal degree two or three. They are not full graph completions.

A separate direct verifier generated all twelve distinct translates of each saved neighborhood and appended their incidence vertices to the54-vertex partial graph. Every resulting66-vertex graph is C4-free: all1921920 unordered-pair codegrees were checked. The degree sequence is six centers of degree nine,24 U vertices of degree seven,24 V vertices of degree eight, and twelve B vertices of degree six. The verifier completed in0.199 seconds and pins the full adjacency stream. It supplies no edges within B or to the second residual orbit C.

This is a complete saved-domain necessary incidence filter with positive survivors, not an exclusion of the single-attachment five-orbit case. No C12 incidence, residual internal edges, full graph solver or Lean formalization is included. The input-coverage dependency on2345 is kept explicit.
