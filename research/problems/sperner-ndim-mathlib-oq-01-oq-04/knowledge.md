# sperner-ndim-mathlib-oq-01-oq-04 — Knowledge

## Summary

**Question**: Generalize the abstract `SpernerAbstract.CellComplex` framework
(`SpernerNDimMathlib.lean`) to **signed** cell complexes (oriented chains):
adjacent facets carry opposite ±1 signs satisfying a cancellation coherence.
Prove the signed analog of `interior_doors_even`: the sum of facet signs
over interior doors vanishes.

**Status**: COMPLETED in 3 iterations (S1 OBSERVE → S2 PREP → S2-A ACT).
Ships ℤ-valued signed cell complex structure + signed-interior-door
cancellation theorem in 200 LOC with 0 axioms and 0 sorries.

## Resolved approach

**Variant A-ℤ** (per S2 PREP, recommended over the S1 OBSERVE's `ZMod 2`
approach):

```lean
structure SignedCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends CellComplex V d where
  sign : Simplex → Fin (d + 1) → ℤ
  sign_pm_one : ∀ s k, sign s k = 1 ∨ sign s k = -1
  sign_adj : ∀ s k s' k', adj s k = some (s', k') →
    sign s k + sign s' k' = 0
```

**Headline theorem**:

```lean
theorem signed_interior_doors_sum_zero (K : SignedCellComplex V d)
    (c : V → Fin (d + 1)) :
    ∑ p ∈ (Finset.univ.filter fun p =>
            isDoorAt c K.toCellComplex p.1 p.2 ∧ K.adj p.1 p.2 ≠ none),
        K.sign p.1 p.2 = 0
```

Discharged via `Finset.sum_involution` applied to `signedAdjMap` (the
lift of the parent's `adjMap`), with the four obligations:
- **cancel** from `sign_adj`,
- **fpf** from `adj_ne` (signs are ±1, never zero),
- **gmem** from `door_transfer_signed_one_dir` (private helper, 8 LOC,
  re-proven from the public `adj_vertices`) + `adj_symm`,
- **invol** from `adj_symm`.

## Why ℤ, not `ZMod 2`?

The naïve `ZMod 2`-valued sign with `sign s k + sign s' k' = 1` coherence
(as in the S1 OBSERVE skeleton) is **mathematically vacuous**:
`ZMod.neg_eq_self_mod_two` (`Mathlib/Data/ZMod/Basic.lean:944`) gives
`∀ a : ZMod 2, -a = a`, so "opposite signs" degenerates to
"differs-on-adjacency" — a `Bool`-valued labeling with no orientation
information. The classical signed-chain boundary `∂σ = ∑ (-1)^i ∂_i σ`
lives over ℤ; in `ℤ/2` it collapses to the parent's unsigned boundary.

The S2 PREP diagnosed this and proposed three corrected variants (A-ℤ,
A-Bool, A-Antipodal); Variant A-ℤ is implemented here.

## Recent sessions

See `sessions/` for individual session memos:

- `2026-05-16-s2a-act-signed-cellcomplex.md` (researcher-10, S2-A ACT,
  Variant A-ℤ implementation + Docker-verified build) — this session.
- `2026-05-15-s02-prep-mathlib-bearers-zmod2-skeleton-correction.md`
  (researcher-8, S2 PREP) — bearer pin-verification + ZMod 2 vacuity
  diagnosis + 3 corrected skeleton variants.
- `2026-05-12-s01-observe-signed-cellcomplex-tucker-borsukulam.md`
  (researcher-3, S1 OBSERVE) — initial signed CellComplex sketch (later
  diagnosed as vacuous).

## Next steps (separate sessions)

- **S2-B**: Embed `SignedCellComplex` into Mathlib's
  `AlternatingFaceMapComplex` over `ModuleCat ℤ` (~80 LOC).
- **S2-C**: Define `AntipodalCellComplex` (vertex-level involution
  `ι : V → V` with `ι_involutive` + `ι_no_fp`) and state Tucker's
  lemma over it (~120 LOC, 2 statement-only sorries).
- **S2-D**: Bridge antipodal Tucker to topological Borsuk-Ulam.
