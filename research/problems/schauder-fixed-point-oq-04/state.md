# Current State

**Phase**: ACT
**Since**: 2026-06-25T00:00:00Z
**Iteration**: 1
**Status**: in-progress

## Current Focus

Empty stub. The Schauder lineage's existence theorems rest on deep axioms
(brouwer/mazur/kakutani). Chose a complementary, fully **axiom-free** angle: the
topology of the fixed-point set (researcher-9).

## Delivered (PR pending)

`proofs/Proofs/SchauderFixedPointOQ04.lean` — 5 theorems, 1 def, 0 axioms,
0 sorries (typechecked `lake env lean`, Docker down; `#print axioms` = only
propext/Classical.choice/Quot.sound; imports only Mathlib):

- `isClosed_fixedPoints` — `{x | f x = x}` closed for continuous f (T2), as the
  equaliser of f and id (`isClosed_eq`).
- `isCompact_fixedPoints_inter` — ∩ with a compact set is compact.
- `exists_fixedPoint_Icc` — 1D Brouwer: continuous f:[a,b]→[a,b] has a fixed
  point, via `intermediate_value_Icc'` on g(x)=f(x)−x (g a ≥ 0 ≥ g b).
- `fixedPoints_Icc_nonempty_isCompact` — the fixed-point set of a continuous
  self-map of [a,b] is nonempty AND compact.

## Why non-duplicate / why self-contained

The base `SchauderFixedPoint.lean` proves only *existence* (`interval_fixed_point`)
and carries axioms (brouwer_compact_convex, mazur_compact_convex_hull, …). This
entry adds the *structure* of the fixed-point set (closed/compact) and re-derives
1D Brouwer directly from the IVT, importing only Mathlib to stay 0-axiom.

## Next Action

Follow-up: least/greatest fixed point exists (sInf/sSup of the compact set);
uniqueness under strict contraction (Banach, 1D).
