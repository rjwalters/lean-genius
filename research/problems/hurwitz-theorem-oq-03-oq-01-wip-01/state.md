# Research State: hurwitz-theorem-oq-03-oq-01-wip-01

## Current State
**Phase**: DONE
**Path**: full
**Since**: 2026-07-05
**Iteration**: 9

## Current Focus
Iter 9 (build-VERIFIED, docker 2715 jobs, **0 sorry / 0 axiom in the whole file**):
**the Frobenius theorem for normed division rings is now fully machine-checked.** The last
sorry (`hurwitz_only_if_ring`, strictly non-commutative branch) is discharged by extracting
and proving the pure linear-algebra core as a standalone theorem.

New verified theorem:

- `finrank_imaginarySubmodule_mem`: `finrank ℝ (Im A) ∈ {0, 1, 3}`. Pure finite-dimensional
  inner-product-space count, no further division-ring input. Proof:
  - `finrank ≤ 1`: already in `{0,1}`.
  - `finrank ≥ 2`: pick nonzero `x`; rank–nullity on the functional `B(x, ·) : Im A → ℝ`
    (`LinearMap.finrank_range_add_finrank_ker`) gives its kernel dimension `≥ finrank − 1 ≥ 1`,
    so there is a nonzero `y` with `B(x, y) = 0`. Set `z = x*y ∈ Im A`
    (`imaginary_mul_mem_imaginarySubmodule`), nonzero (no zero divisors), `B`-orthogonal to
    `x, y` (`imaginaryBilin_mul_orthogonal`), with positive diagonal (positive-definiteness).
    - **Upper bound** `finrank ≤ 3`: the map `w ↦ (B(w,x), B(w,y), B(w,z)) : Im A → ℝ³`
      (`LinearMap.pi ![B.flip x, B.flip y, B.flip z]`) is injective — its kernel is trivial by
      `eq_zero_of_orthogonal_to_triple` — so `LinearMap.finrank_le_finrank_of_injective` +
      `Module.finrank_fin_fun` give `finrank ℝ (Im A) ≤ 3`.
    - **Lower bound** `finrank ≥ 3`: `![x, y, z]` is `B`-orthogonal with positive diagonal,
      hence linearly independent (`Fintype.linearIndependent_iff`; kill each coefficient by
      applying the flip functionals `B.flip x/y/z` and using `mul_eq_zero` against the
      positive diagonal). `LinearIndependent.fintype_card_le_finrank` gives `3 ≤ finrank`.
    - Combined: `finrank ℝ (Im A) = 3`.

`hurwitz_only_if_ring` is now closed with no case split on commutativity:
`finrank_eq_imaginary_add_one` gives `finrank ℝ A = finrank ℝ (Im A) + 1`, and
`finrank_imaginarySubmodule_mem` pins `finrank ℝ (Im A) ∈ {0,1,3}`, so
`finrank ℝ A ∈ {1,2,4} ⊆ {1,2,4,8} = admissibleDimensions`.

## Active Approach
COMPLETE. Frobenius' theorem (`NormedDivisionRing` over ℝ ⟹ `finrank ∈ {1,2,4}`) is fully
verified, 0 sorry / 0 axiom (standard `propext`/`Classical.choice`/`Quot.sound` only; no
`sorryAx`, no `Lean.ofReduceBool`). The metric route (positive-definite `imaginaryBilin`) sidesteps
the Clifford / Radon–Hurwitz representation machinery Mathlib lacks.

## Attempt Count
- Total attempts: 5 (code, shipped)
- Approaches tried: 3

## Blockers
- None. The remaining sorry has been eliminated.

## Next Action
- Ship: commit + PR + update `meta.json` (status → verified, badge → verified, sorries 0).
- Optional follow-up (separate entry): the octonion (dim 8) case needs a non-associative
  framework beyond `NormedDivisionRing`; `hurwitz_only_if_ring` proves the associative
  bound `{1,2,4}`, which is the sharp Frobenius statement for this typeclass.
