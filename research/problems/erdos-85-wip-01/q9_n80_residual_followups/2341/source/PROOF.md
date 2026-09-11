# Full single311-group local screen above11123 residual graphs

Inputs are the144 residual graphs and960 high support orbits submitted as2337. This packet keeps input completeness conditional on that review. Every retained high support determines the complete residual attachments of a311 group: its two high vertices use the displayed triple and its partner; the four low vertices cover the two remaining residual orbits singly. Choose their labels so each low pair attaches to the correspondingly ordered residual pair. Independent flips of these low labels are absorbed by the full internal-matching enumeration.

The six attached vertices share one fixed neighbor. Their induced graph has maximum degree one, since two edges with a shared endpoint would make a C4 through the fixed center. It is invariant under the involution. Every low attached vertex must have an internal neighbor, since its residual degree one saturates all seven possible W slots. The high vertices may have zero or one internal neighbor.

The checker enumerates every invariant internal matching by the nine edge orbits under the three paired involution orbits. It retains precisely the ten matchings giving each low vertex internal degree one. It then checks the endpoint budget at every group vertex using its full residual support plus internal neighbors; omitted cross-neighbor excesses are nonnegative because this branch has no isolation. Finally it reconstructs R, the six attached vertices and their fixed center, and checks every pair for a C4.

The original30-second run completes in0.080 seconds. All9600 high-support/matching combinations are tested, and2544 survive across all144 input residual graphs. There is no excluded residual graph, UNKNOWN or unvisited case. These results show that adding one complete311 group still leaves every residual type viable locally; they do not establish any full-graph realization.

A full continuation must couple multiple groups and their cross edges and fixed-center constraints. The current17-vertex graphs omit those features, the other nine fixed centers and all other attached groups. No full graph solver or Lean formalization is used, and11123 remains open.
