# Research State: hurwitz-theorem-wip-01

## Current State

**Phase**: PARK (BLOCKED, awaiting Mathlib upstream)
**Path**: full
**Since**: 2026-05-08T03:35:00Z
**Iteration**: 3

## Current Focus

Iteration 3 (PARK): re-confirm BLOCKED status. No relevant Mathlib upstream
movement since S2 (2026-05-07): a search for Clifford structure
classification, Frobenius theorem, and Bott periodicity in mathlib4 master
returns no new APIs. The two open sorries (`HurwitzTheorem.lean:1937`,
`HurwitzOnlyIf.lean:111`) remain blocked on the same Cl(0,n-1) classification
gap.

## Active Approach

**Wait** — until Mathlib gains Clifford structure / Bott periodicity API.

## Attempt Count

- Total attempts: 2
- Approaches tried:
  1. (S2) OBSERVE / SURVEY: enumerate proved infrastructure, classify what's
     left, identify Mathlib gap precisely.
  2. (S3 — this session) Re-confirm BLOCKED + correct the S2 cost estimate
     for option B (refactor): the "~80 lines" estimate misjudged the
     bridge construction (see Blockers item 4 below).

## Blockers

1. Mathlib has no real Clifford algebra periodicity / structure classification.
2. Mathlib has no Artin-Wedderburn for real semisimple algebras.
3. No minimum-faithful-real-rep-dimension lemma derivable from current
   `Mathlib.LinearAlgebra.CliffordAlgebra.*` (which only provides the universal
   property and basic conjugation).
4. **S2 cost re-estimate**: option B (algebra-level refactor of
   `HurwitzOnlyIf.hurwitz_only_if_ring`) is not "~80 lines" as previously
   stated. The bridge `NormedDivisionRing → NSquareIdentity` requires an
   inner product on A so that the L²-norm of coordinate vectors matches the
   division-algebra norm. Concretely, the bridge needs either:
   - **(B1)** Construct an `InnerProductSpace ℝ A` from the multiplicative
     norm. *Not* automatic: a general normed ℝ-vector space need not be inner
     product. For a finite-dim normed associative division algebra this is
     true (it's part of the classical Frobenius proof: Re(a) := (a + ā)/2,
     ⟨a,b⟩ := (Re(ab*) something equivalent)) but the construction is itself
     ~200-300 lines and is not in Mathlib v4.26.0.
   - **(B2)** Choose any basis, work with the resulting non-standard
     positive-definite quadratic form on `Fin n → ℝ`, diagonalize it, then
     transfer multiplication. Adds change-of-basis machinery and makes the
     resulting `NSquareIdentity` non-canonical. Estimated 150-250 lines plus
     a `Matrix.PosDef.diagonalize` API that may need to be built.
5. **(B3) Frobenius alternative**: For `NormedDivisionRing` (associative),
   the stronger Frobenius theorem (`finrank ∈ {1, 2, 4}`) suffices, but the
   classical Frobenius proof goes through the same Clifford algebra route or
   via the imaginary subspace construction (V = {a : a² ≤ 0}). Mathlib has
   *neither*. arXiv:2405.01876 (May 2024) is a recent paper formalizing
   Frobenius in a non-Mathlib system; not yet ported.

## Next Action

1. **(option D, current)** Wait for Mathlib upstream. Periodically re-check
   `Mathlib.LinearAlgebra.CliffordAlgebra.*` for `equivOfPeriodicity` /
   structure-classification lemmas, and `Mathlib.Algebra.Algebra.Basic`
   for a Frobenius-type theorem.

2. **(option B, deferred)** If a contributor takes on the bridge
   construction (~200-500 lines), it splits into two natural Mathlib PRs:
   (i) `InnerProductSpace ℝ A` from `NormedDivisionRing` + finite-dim
   (Frobenius-style imaginary-subspace argument); (ii) the
   `nsquareIdentity_of_normedDivisionRing` bridge using that inner product.

3. **(option A, deferred)** Small-case decomposition for n=6, 10. Still
   ~400 lines/case via ad-hoc Wedderburn structure of Cl(0,5), Cl(0,9).
   Narrows but does not eliminate the open sorry.

4. **(do NOT)** Submit to Aristotle. Sorry is OPEN (genuine missing
   infrastructure), not a routine lemma.

## Unblock Criteria (concrete)

Promote phase from PARK back to ACT when **any** of the following lands in
mathlib4 master:

- `Mathlib.LinearAlgebra.CliffordAlgebra.Periodicity` with an isomorphism
  `Cl(0, n+8) ≅ Cl(0, n) ⊗[ℝ] M(16, ℝ)` (or signed-degree analogue).
- `Mathlib.LinearAlgebra.CliffordAlgebra.RealClassification` with a
  Wedderburn-style structure theorem listing `Cl(0, k)` for `k = 0..7`.
- A Mathlib `frobenius_theorem` for finite-dim normed associative real
  division algebras, asserting `finrank ℝ A ∈ {1, 2, 4}`.
- Any one of the above plus a `RingHom.injective` / faithful representation
  lemma giving a lower bound on the simple-module dimension.

When any of these lands, reopen and proceed with option B (~80 line glue
once the upstream API exists) or directly close `HurwitzTheorem.lean:1937`
via the new periodicity API.
