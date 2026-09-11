# Five-edge residual graphs with a free involution

Let R be simple, C4-free, on ten vertices, with exactly five edges, maximum degree at most three, and a fixed-point-free involution tau. This standalone classification does not assume the pending uniform D<=5 bound. In the N80 cubic-fixed branch, the maximum degree premise is accepted2295 and D=e(R).

R is a forest. Any cycle has at most five edges. A triangle or five-cycle cannot be invariant under a fixed-point-free involution, since it has an odd number of vertices. A distinct image of a triangle would require at least five edges; in the five-edge borderline case the triangles share an edge, and their four nonshared edges form a C4. A distinct image of a five-cycle requires more than five edges. Four-cycles are forbidden. These alternatives exclude every possible cycle. (Equivalently, two distinct triangles in a C4-free graph share at most one vertex and need six edges.)

The five sorted orbit degrees sum to five and lie in0..3: 00023,00113,00122,01112,11111. Pattern00023 is impossible: its four nonisolated vertices have degree sequence3,3,2,2, giving K4 minus an edge and a C4.

For00113, the cubic vertices must lie in the same component, since two components containing cubic vertices require at least eight nonisolated vertices, but only six exist. The forest component therefore uses all six nonisolated vertices and is the double star with adjacent cubic centers and two leaves at each. There are four isolated vertices. Tau exchanges the centers and bijects their two leaf sets; all such bijections are equivalent under leaf relabeling. The isolated vertices form two tau pairs. This gives one action type.

For00122, the forest has six nonisolated vertices, only two leaves, and maximum degree two. It is P6 plus four isolates. Tau reverses P6 and pairs the isolates, giving one action type.

For01112, the forest has eight nonisolated vertices, six leaves, and two degree-two vertices. If the degree-two pair lies in one component, that component is P4, reversed by tau; the two remaining K2 components are either individually invariant or exchanged. If the degree-two vertices lie in different components, those components are exchanged P3s, and the remaining K2 is invariant. One isolated tau pair remains in all cases. These give three action types.

For11111, R is five disjoint K2s. The number of individually invariant edges is1,3,or5; the others are exchanged in pairs. The swap on an invariant edge is forced by freeness, and endpoint choices between exchanged edges are equivalent by relabeling. These give three action types. Total: eight.

## Finite confirmation and exact action cover

Use tau(v)=v xor1. The complete possible edge orbits comprise five singleton edges within vertex pairs and twenty two-edge orbits between pairs. A five-edge invariant graph has respectively(1,2),(3,1),or(5,0) singleton/double-orbit counts, hence1151 choices before filtering. The checker filters maximum degree and common-neighbor counts, verifies the forest identity separately for every component, and records1041 survivors. Sorted-pattern counts are0,120,240,600,81 in the order above.

Component sizes/degrees and whether each component is invariant give the eight paper types. As an independent check that no inequivalent actions were hidden by this key, verify-actions.py applies all3840 permutations commuting with tau to each representative. Its full orbit equals precisely the saved labeled graph set of that type, and the eight orbits are disjoint and cover all1041 records. Orbit sizes are120,240,240,120,240,60,20,1.

Both original30-second stages completed: enumeration0.014831 seconds, action-cover verification0.048766 seconds. No attachments have yet been supplied, so these are residual graphs only, not order80 witnesses or exclusions of the eight cases. No global Erdős85 or Lean theorem is claimed.
