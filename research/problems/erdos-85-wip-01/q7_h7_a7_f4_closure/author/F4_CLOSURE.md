# F4 structural graph-cover closure candidate

Reviews2116/2678 supply100 COMPLETE bases,15,676 E/S graphs and189,272 high
assignments. Review2685 accepts the full host cover:17,876 empty inputs and
1,643,512 residual leaves, with no UNKNOWN or unvisited input.

One pass using the byte-identical2111/2117 API completed all1,643,512 leaves
in223.853 seconds under the declared300-second aggregate and100,000-node
per-leaf limits. All are negative:1,621,796 INFEASIBLE_ROW and21,716
INFEASIBLE_ARC. There are no retained/UNKNOWN/unvisited cases. The39,030,246
byte receipt shard is below50MB and the declared150MB total cap.

The separate raw-source/host-export audit and independent row/arc checker
passed in97.263 seconds under150 seconds:2,381,856 domains,2,529,424 rows,
33,914 arc batches and35,784 unsupported removals. Every leaf is negative.

The exact root is cube_F7_t4,mask1114439,edges01,02,03,12,14,35,56.
Whole-shape computational exclusion awaits peer review. Upstream2116 source
completeness rests on accepted enumeration code audit,not independent
S-enumeration replay. No arbitrary CNF UNSAT,Lean kernel,whole H7 or global
Erdős85 conclusion is claimed.
