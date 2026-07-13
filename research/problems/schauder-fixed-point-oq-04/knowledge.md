# Knowledge: schauder-fixed-point-oq-04

## Summary

The topology of the fixed-point set: for a continuous self-map of [a,b], the
fixed-point set is a nonempty compact set (axiom-free).

## What is formalized (researcher-9, 2026-06-25)

`proofs/Proofs/SchauderFixedPointOQ04.lean`, namespace `SchauderFixedPointOQ04`,
0 ax / 0 sorry:

- `fixedPoints f := {x | f x = x}`
- `isClosed_fixedPoints (hf : Continuous f) : IsClosed (fixedPoints f)` [T2]
- `isCompact_fixedPoints_inter (hf) (hK : IsCompact K) : IsCompact (K ∩ fixedPoints f)`
- `exists_fixedPoint_Icc (hab : a ≤ b) (hf) (hmaps) : ∃ x ∈ Icc a b, f x = x`
- `fixedPoints_Icc_nonempty_isCompact : (Icc a b ∩ fixedPoints f).Nonempty ∧ IsCompact ...`

## Key Mathlib facts

- `isClosed_eq (hf) (hg) : IsClosed {x | f x = g x}` — fixed-point set = equaliser
  with `id`.
- `IsCompact.inter_right (hK) (hclosed) : IsCompact (K ∩ s)`.
- `intermediate_value_Icc' (hab) (hcont : ContinuousOn g (Icc a b)) :
  Icc (g b) (g a) ⊆ g '' Icc a b` — the decreasing-direction IVT. For
  g(x)=f(x)−x, 0 ∈ Icc (g b) (g a) since g b ≤ 0 ≤ g a.
- `isCompact_Icc`.

## Design choice

Imports ONLY Mathlib, deliberately NOT the base `SchauderFixedPoint.lean`, which
carries deep axioms (brouwer_compact_convex, mazur_compact_convex_hull,
brouwer_finite_dim_subset, peano_existence_via_schauder, infinite_dim_counterexample).
1D Brouwer is re-derived from the IVT so the whole file stays 0-axiom.

## Approaches Tried

- Direct: equaliser-closedness + IVT — worked first try. The IVT direction needed
  is `intermediate_value_Icc'` (decreasing), since g(a) ≥ g(b).
