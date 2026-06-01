# Research State: triangular-reciprocals-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-01 (S2 — researcher-1 OBSERVE→ORIENT pass)
**Iteration**: 2
**Prior**: OBSERVE iter 1 (2026-04-05, template only — no actual observation recorded)

## Current Focus
Approach lock-in. With problem.md now filled and the Mathlib API mapped, the next
iteration should DECIDE between the direct partial-fraction route and the digamma
route, and scaffold the Lean file accordingly.

## Active Approach
**Approach 1 — Direct partial fractions + harmonic telescoping (provisional).**
- Lemma 1: $\tfrac{1}{n(n+k)} = \tfrac{1}{k}(\tfrac{1}{n} - \tfrac{1}{n+k})$ for $n, k \ge 1$.
- Lemma 2: $\sum_{n=1}^{N} \tfrac{1}{n(n+k)} = \tfrac{1}{k}\bigl(H_k - (H_{N+k} - H_N)\bigr)$
  via reindexing.
- Lemma 3: $H_{N+k} - H_N \to 0$ as $N \to \infty$, bounded by $k/(N+1)$.
- Lemma 4: summability via comparison with $\sum 1/n^2$.
- Main: `HasSum (fun n => 1/((n+1)*((n+1)+k))) (H_k/k)`.

Approach 2 (digamma) is parked: Mathlib has $\Gamma'$ at integers but not the digamma
series expansion, so it would require us to prove the series identity from scratch.

## Attempt Count
- Total attempts: 0 (S2 is the first substantive research pass; iter 1 was template only)
- Current approach attempts: 0 (not yet executed)
- Approaches tried: 0

## Blockers
None.

## Next Action

DECIDE phase (S3):
1. Confirm Approach 1 by sketching Lemma 2 reindex in detail (ℕ-shift between
   `Finset.range`, `Finset.Icc`, and the partial-fraction telescoping).
2. Verify the ℝ-cast of `harmonic k` (Mathlib defines `harmonic : ℕ → ℚ`).
3. Pick a file name. Candidates:
   - `Proofs/TriangularReciprocalsOQ02.lean` (Aristotle-friendly, matches slug).
   - `Proofs/TriangularReciprocalsHarmonic.lean` (semantically descriptive).
   Recommendation: `TriangularReciprocalsOQ02.lean` to match the gallery slug pattern
   used by `HarmonicDivergenceOQ01.lean`, `HarmonicDivergenceOQ02.lean`, etc.
4. Then ACT (S4): scaffold the file with the four lemmas + main theorem, leaving each
   `by sorry` for incremental closure.

## Key Observations from S2 (researcher-1, 2026-06-01)

- `Proofs/TriangularReciprocalGeneralized.lean` (202 lines) handles the **alternating**
  generalization (slug `triangular-reciprocals-oq-03`), not this one. Its
  `partial_fraction` lemma is for $\tfrac{1}{n(n+k)} = \tfrac{1}{k}(\tfrac{1}{n} -
  \tfrac{1}{n+k})$ — directly transferable.
- `Mathlib.NumberTheory.Harmonic.Defs` puts `harmonic` in ℚ, so the final ℝ-valued
  `tsum` requires a `push_cast` step on every harmonic reference.
- `Mathlib.NumberTheory.Harmonic.GammaDeriv.deriv_Gamma_nat` gives the digamma identity
  $\Gamma'(n+1) = n!(-\gamma + H_n)$, which yields the optional corollary
  $\sum 1/(n(n+k)) = (\psi(k+1) + \gamma)/k$ once the main identity is proved.
- No gallery dir `src/data/proofs/triangular-reciprocals-oq-02/` exists yet — will need
  to be created when the Lean file lands.
