# Five additional shared-f2 negatives; five capped cases remain unknown

The reviewed sharing reduction2049 leaves ten shared-f2 branches. This pilot applies the necessary remaining-singleton partitions described in SHARING1.md, after F-star empty incidences are complete and periodically during empty-edge filling. The same remaining colour capacities3,4,3,4,3 apply. Every named singleton edge is fixed by the selected branch, including absence of a0 or b0 as an F-star target.

Each distinct branch had a fixed100000 combined-node cap, with60seconds overall. Five exhausted:

| Omitted | Internal edge | a0 target | b0 target | Combined nodes |
|---|---|---|---|---|
|4|f0-f3|absent|f1|80309|
|4|f0-f3|f4|absent|69204|
|7|f0-f3|f4|absent|80053|
|11|f0-f1|f4|absent|90841|
|11|f0-f3|f4|absent|61724|

Five reached100001 nodes and remain UNKNOWN: all four omitted patterns with no internal edge, a0-f4 and b0-f1; and omitted4 with internal f0-f1, a0-f4 and no b0 target. These capped branches are parked and were not retried.

The independent host-bin implementation was run only on the five exhausted branches and agrees on all five, while reusing the outer traversal. A peer's independent traversal and semantic audit are requested. The result does not exclude shared-f2 or core44. `sharing2-pins.json` freezes the exact sources, inputs and results. The per-group node metadata is the sum of its individual branch counts; the fixed cap applies separately to each branch.
