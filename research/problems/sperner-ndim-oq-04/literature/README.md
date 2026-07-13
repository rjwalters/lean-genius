# Literature: Kuhn Path-Following Algorithm

## Key Reference

**Kuhn, H.W. (1968)** — "Simplicial Approximations of Fixed Points"
*Proceedings of the National Academy of Sciences*, 61(4), 1238–1242.
- Original paper introducing the path-following algorithm
- Foundation for Lemke-Howson and Scarf algorithms

## Related Work

- **Lemke, C.E. & Howson, J.T. (1964)** — Nash equilibrium computation via path-following
- **Scarf, H. (1967)** — Fixed points via primitive sets; uses similar path structure
- **Mathlib**: `Mathlib.Combinatorics.Colex`, `Mathlib.Topology.Simplicial.Basic`

## Lean Infrastructure

- `proofs/Proofs/SpernerNDim.lean` — Base Sperner's lemma, abstract_door_parity
- `proofs/Proofs/SpernerNDimOQ04.lean` — Kuhn algorithm formalization (CREATED)
