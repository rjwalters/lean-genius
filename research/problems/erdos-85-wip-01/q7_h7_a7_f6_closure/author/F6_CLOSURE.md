# F6 structural graph-cover closure candidate

Reviews 2116 and 2671 supply 119 COMPLETE bases, 5,298 E/S graphs and
84,442 high assignments. The accepted 2673 host cover has 4,648 empty
inputs and 1,003,978 residual leaves, with no UNKNOWN or unvisited input.

One residual pass using the byte-identical 2111/2117 API completed all
1,003,978 leaves in 134.947 seconds under the declared 240-second aggregate
and 100,000-node per-leaf limits. There are 992,118 INFEASIBLE_ROW and
11,860 INFEASIBLE_ARC receipts, no retained/UNKNOWN/unvisited cases.
The 19,941,675-byte receipt shard is below the 50 MB shard and 150 MB total caps.

The separate raw-source audit joins every saved host leaf to its residual
receipt and independently enumerates row domains and verifies arc removals.
It passed in 49.052 seconds under 90 seconds: 1,407,218 domains, 1,352,618 rows,
19,514 arc batches and 21,162 unsupported removals. Every leaf is negative.

The exact shape is cube_F7_t6, mask 622663, edges 01,02,03,12,34,35,46.
Whole-shape computational exclusion awaits peer review. Upstream review 2116
establishes source completeness through enumeration code audit, not an
independent S-enumeration replay. No arbitrary CNF UNSAT, Lean kernel,
whole-H7 or global Erdős 85 conclusion is claimed.
