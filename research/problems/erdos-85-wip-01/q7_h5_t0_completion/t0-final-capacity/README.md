# Counting obstruction for the final capped T0 core

Under the reviewed H5/T0 support and BC=J premises, heavy core 5774048758818 cannot extend. This is a new counting argument; the earlier capped search remains recorded as UNKNOWN and is not rerun.

The ten heavy vertices carry the ten two-element subsets of five high colours in lexicographic order. The core edges are two cycles:

    (0,2,7,8,6,0) and (1,3,9,5,4,1).

Each heavy vertex has two heavy neighbors whose supports are disjoint, covering exactly four high colours. BC=J therefore forces exactly one singleton neighbor, of the remaining colour. With two high neighbors, two heavy neighbors and one singleton neighbor, its required degree seven leaves exactly two empty neighbors. Across ten heavy vertices this requires **20 heavy–empty incidences**.

There are fourteen empty vertices: 49 minus five highs, ten pair-support vertices and twenty singletons. At an empty vertex, BC=J partitions the five high colours among nonempty neighbors. Each heavy guest contributes two colours, so an empty vertex has at most two heavy guests.

Two heavy vertices hosted by the same empty must have disjoint supports and no common heavy neighbor; otherwise they already have a common neighbor and the empty creates a C4. Direct inspection of the fixed core gives only five eligible pairs:

    {0,9}, {1,6}, {2,4}, {3,7}, {5,8}.

A given pair may be hosted by at most one empty, again by C4-freeness. Thus at most five empties have two heavy guests, and every other empty has at most one. The total heavy–empty incidence is at most **14 + 5 = 19**, contradicting the required 20.

This bound depends only on the fixed heavy core, not a choice of singleton hosting or singleton completion. It therefore excludes all possible completions of this core. audit.py checks the exact core mask, all support unions, eligible pairs, and arithmetic against the frozen T0 census; it does not search completions. Run it from any directory. Inputs use ../t0-empty-completion/core-t0.json. PINS.json freezes the evidence.

This is a conditional mathematical exclusion with a small finite core audit, pending independent review. It is not a Lean theorem. Combining it with the other T0 computations would exclude T0 only after the normalization and remaining reduction chain are independently accepted (reviews 2022, 2025, 2031, 2033, 2034). No automatic Phase B queue change or full Erdős 85 solution is claimed.
