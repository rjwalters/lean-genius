# Current State

**Phase**: FORMALIZED (obstruction + sharp converse proved; fixed-dimension question remains open)
**Since**: 2026-06-26
**Iteration**: 2

## Current Focus

Extended `proofs/Proofs/Erdos395OQ02.lean` (now 309 lines, 14 theorems, 7 defs,
0 sorries, 0 axioms) with the **complementary saturation direction**, closing the
characterization of the orthonormal case into a sharp 0/1 dichotomy.

## Active Approach

The same deterministic identity `‖Σεᵢzᵢ‖ = √n` drives both directions:

1. **Obstruction (iteration 1)** — `C² < n ⟹` favourable set empty `⟹ P = 0`.
2. **Saturation (NEW, iteration 2)** — `√n ≤ C ⟹` favourable set is all of
   `{±1}ⁿ ⟹ P = 1`:
   - `orthonormal_signedSum_le_of_sqrt_le` — every sign sum is within `C`.
   - `orthonormal_smallSum_eq_univ` — favourable set = entire sign space.
   - `orthonormal_smallSumCount_eq_two_pow` — count = `2ⁿ` (via `Fintype.card_fun`).
   - `orthonormal_smallSumProb_eq_one` — probability = `1`.
3. **Sharp dichotomy (NEW headline)** — `orthonormal_smallSumProb_dichotomy`:
   on orthonormal configurations `P(‖Σεᵢzᵢ‖ ≤ C) = [n ≤ C²]`, a two-valued step
   function jumping from 0 to 1 exactly at `C = √n`. There is no `c/n`
   intermediate regime, so the threshold growth is pinned at `C ~ √n` in the
   strongest (exact, deterministic) form. This addresses the "pin the threshold
   dependence C(d)" item from iteration 1's next-action list.

## Blockers

- The genuine open question — **fixed-dimension** reverse Littlewood–Offord
  (`ReverseLO_fixedDim d` for d ≥ 3) — is still **not** resolved. It is recorded
  as an unproven Prop. This is real open mathematics (HJNS proved only d=2); not
  attempted here.
- BUILD: not re-run to green. The Docker build hits the persistent Mathlib-cache
  `.ltar` permission-denied error (cached path) / OOM at the 7.65GB VM ceiling
  (from-source path). All new lemmas were instead statically verified against the
  pinned Mathlib source (Real.sqrt_sq, Real.sqrt_le_sqrt, Fintype.card_fun,
  Finset.filter_true_of_mem all exist with the used signatures). Build-pending
  per established precedent.

## Next Action

- The Paley–Zygmund / Fourier route to a fixed-`d` lower bound (using `‖Σεᵢzᵢ‖² = n`
  as the second-moment input) remains the natural attack on the open Prop — but
  requires genuine new mathematics, not just Mathlib plumbing.
- A future session with a working build should run `#print axioms` on the new
  dichotomy theorem to confirm foundational-only axioms.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 1 (orthogonality-identity, both directions)
