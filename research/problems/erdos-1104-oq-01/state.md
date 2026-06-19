# Current State

**Phase**: ACT
**Since**: 2026-06-19
**Iteration**: 2

## Current Focus

Mycielskian construction as the constructive engine for triangle-free graphs of large
chromatic number (the lower-bound side of Erdős #1104). Built the Mycielskian from
scratch (absent from Mathlib) and proved the **full Mycielski theorem**: triangle-free
preservation, the constructive `(n+1)`-colouring upper bound, **and the chromatic lower
bound** `(M G).Colorable (n+1) → G.Colorable n` (Mycielski's recolouring argument).
Together the two bounds pin `χ(M(G)) = χ(G)+1` exactly. The iterated witness family is
packaged on top. 281 lines, 0 sorries, 0 axioms.

## Active Approach

`SimpleGraph.fromRel`-based Mycielskian on `Option (V ⊕ V)`; case analysis on the
Option/Sum vertex structure for triangle-free preservation; explicit `Coloring.mk`
using `Fin.castSucc` + apex top colour for the upper bound; for the lower bound, recolour
`G` by `D u := if C u = a then C u' else C u` (apex colour `a := C z`), show `D` avoids
`a` and is proper, then transport into `Fin n` via `Fintype.equivFinOfCardEq` on the
`n`-element complement `Fin (n+1) \ {a}`; structural recursion on the iterate count `k`
for the witness family.

## Blockers

None — the previously-open chromatic lower bound is now proven. The Mycielski theorem is
complete and machine-checked.

## Next Steps

- Instantiate the witness tower at a concrete base (`cycleGraph 5` or `⊤ : SimpleGraph
  (Fin 2)`) and combine both bounds to conclude `χ(mycielskianIter base k) = k + base`.
- Discharge the parent `erdos-1104` `mycielski_construction` axiom against this
  verified construction.
- Consider upstreaming the Mycielskian to Mathlib.
