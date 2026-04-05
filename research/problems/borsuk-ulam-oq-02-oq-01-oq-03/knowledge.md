# Knowledge: borsuk-ulam-oq-02-oq-01-oq-03

## Summary

No research sessions yet. Problem initialized by Seeker on 2026-04-05.

## Key Facts

- Parent file: `proofs/Proofs/BorsukUlamOQ02OQ01.lean` — axiomatizes `buDim(n, d)` for cyclic Z/n
- Related: `proofs/Proofs/BorsukUlamOQ02OQ01OQ04.lean` (Fadell-Husseini index)
- This problem: extend the framework to non-cyclic groups (dihedral D_n, symmetric S_n)
- No dedicated Lean file exists yet — need to create `BorsukUlamOQ02OQ01OQ03.lean`
- `buDim` is axiomatized as `axiom buDim (n d : ℕ) : ℕ` — takes cyclic group ORDER, not type

## Key Structural Insight

Subgroup monotonicity: H ≤ G → buDim(G, d) ≥ buDim(H, d)
- D_n contains Z/2 and Z/n → buDim(D_n, d) ≥ max(buDim(2,d), buDim(n,d))
- S_n contains Z/2 (transpositions) → buDim(S_n, d) ≥ d-1

## Open Questions

1. Can `buDim` be generalized from `ℕ` (group order) to `Type*` (group type)?
2. For D_n: does buDim(D_n, d) = max(buDim(2,d), buDim(n,d)), or is it strictly larger?
3. Is there an existing Mathlib group structure for DihedralGroup that helps?
4. Can Dold's index framework (oq-02-oq-03) give a cleaner approach?

## Mathlib Pointers

- `DihedralGroup` — Mathlib has `DihedralGroup n` as a concrete type
- `Equiv.Perm` — symmetric groups are `Equiv.Perm α`
- `Subgroup.orderOf_dvd_of_le` — subgroup order divisibility
- `ZMod` — cyclic groups as `ZMod n`
- Key: `DihedralGroup.orderOf_r` and subgroup structure lemmas
