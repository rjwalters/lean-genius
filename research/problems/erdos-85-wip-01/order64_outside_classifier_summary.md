# Order-64 H16 outside-feasibility census

Date: 2026-08-17

The classifier `order64_outside_classifier.py` enumerates every simple
six-regular exterior-pair graph `R` satisfying the formally proved local
conditions for a fixed H16 cycle partition:

- `R H = H R`;
- no `R` edge joins an H-distance-two pair;
- on each H-cycle, either every H-edge belongs to `R` or none does.

For every such `R`, its 48 edges are used as the outside vertices and the
classifier asks for a symmetric simple graph `C` satisfying the formally
proved cross-block routing equation `H B + B C = J`.  It also requires that
`C` be C4-free.  Models are quotiented by all dihedral automorphisms of the
H-cycles and by permutations of equal cycles.

## Exhaustive result

| H cycle partition | labeled R models | R orbits | feasible C | unknown |
|---|---:|---:|---:|---:|
| `16` | 20 | 20 | 0 | 0 |
| `10,6` | 6 | 3 | 0 | 0 |
| `8,8` | 2328 | 75 | 0 | 0 |
| `5,5,3,3` | 360 | 3 | 0 | 0 |
| **total** | **2714** | **101** | **0** | **0** |

Thus all four partitions left by the formal quotient census are excluded by
the outside-block constraints encoded here.

## Independent CNF replay

The final run emitted:

- 101 outside-`C` CNFs, one for each automorphism orbit;
- four `R`-completeness CNFs, which encode the complete local `R` ledger and
  exclude every enumerated labeled model.

All 105 CNFs replayed as UNSAT with `kissat` (exit code 20).  The temporary
CNFs totaled 327 MB and are reproducible rather than checked into git.

Example reproduction for one partition:

```sh
python3 research/problems/erdos-85-wip-01/order64_outside_classifier.py \
  '8,8' --limit 100000 \
  --emit-cnf-dir /tmp/order64-cnf/8_8/c \
  --emit-r-completeness-cnf /tmp/order64-cnf/8_8/r-complete.cnf
find /tmp/order64-cnf/8_8 -name '*.cnf' -print0 | \
  xargs -0 -P 8 -I '{}' sh -c \
    'kissat "$1" >/dev/null 2>&1; test $? -eq 20' _ '{}'
```

## Certification boundary

This census is decisive computational evidence, but it is not yet the final
Lean theorem.  The remaining certification task is to connect the emitted
CNF semantics to the graph-facing outside-feasibility package and replay the
UNSAT certificates in Lean (or replace them with compact arithmetic
certificates).  Until that bridge is complete, the order-64 branch should be
reported as computationally closed, not formally closed.
