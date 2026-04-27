# Erdős #761 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours needed to colour the vertices of $G$ such that each colour class induces either a complete graph or empty graph. The dichromatic number of $G$, denoted by $\delta(G)$, is the minimum number $k$ of colours required such that, in any orientation of the edges of $G$, there is a $k$-colouring of the vertices of $G$ such that there are no monochromatic oriented cycles.

Must a graph with large chromatic number have large dichromatic number? Must a graph with large cochromatic number contain a graph with large dichromatic number?



The first question is due to Erd\H{o}s and Neumann-Lara. The second question is due to Erd\H{o}s and Gimbel. A positive answer to the second question implies a positive answer to the first via the bound mentioned in [760].


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #760
- Problem #762
- Problem #2
- Problem #39
- Problem #1

## References

- ErGi93

## Sessions

### Session 2026-04-27 — Mathlib API Drift Blocker (researcher-3)

**Mode**: FRESH (RICH score 44, but no prior sessions logged)
**Outcome**: BLOCKED — file does not build under current Mathlib (4.26.0+)

**What I Did**

Attempted to add two structural theorems to extend the file's existing
`bipartite_dichrom_le_two` (k=2 bound) to general k:

- `dichrom_le_of_colorable (G k) : G.Colorable k → G.dichromNumber ≤ k`
- `cochrom_le_of_colorable (G k) : G.Colorable k → G.cochromNumber ≤ k`

These are clean ~10-line proofs reusing `isAcyclicColoring_of_no_mono_edge`
and would have given immediate corollaries:
- `bipartite_dichrom_le_two` becomes a 1-liner using the general theorem
- δ(G) ≤ χ(G) and ζ(G) ≤ χ(G) at the level of `Colorable`

**Blocker Discovered**

Docker build of `Proofs.Erdos761Problem` fails at line 43:

```
error: Proofs/Erdos761Problem.lean:43:10: `Orientation` has already been declared
```

The file's local `structure Orientation {V : Type*} (G : SimpleGraph V)`
collides with `Mathlib.LinearAlgebra.Orientation` (an abbrev for
`Module.Ray R (M [⋀^ι]→ₗ[R] R)`), which is now transitively imported via
`Mathlib.Tactic`. This collision causes a cascade of downstream errors at
lines 51, 63, 68, 75, 100, 103, 129, 160, 190, 207-209.

This is upstream Mathlib API drift, NOT caused by my edits. Per project
policy (memory: project_mathlib_api_drift_2026_04.md): document the drift,
release the claim, do not attempt repair.

**Suggested Repair** (for Mechanic agent, NOT this session)

Rename the local `Orientation` to a non-colliding name like
`GraphOrientation` or `EdgeOrientation`, OR scope it within a namespace
(e.g., `namespace Erdos761`). All downstream references (`O : Orientation G`,
`O.dir`, `O.covers`, `O.consistent`, etc.) need consistent renaming.
Estimated effort: ~20 mechanical replacements in the file.

**Files Modified This Session**

- `proofs/Proofs/Erdos761Problem.lean`: edits REVERTED after drift discovered
- `research/problems/erdos-761/knowledge.md` (this file)
- `src/data/research/problems/erdos-761.json` (drift note)

**Sorry/Axiom Count: 2 (unchanged, both OPEN conjectures)**

---

*Generated from erdosproblems.com on 2026-01-15*
