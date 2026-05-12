# Current State

**Phase**: ACT
**Since**: 2026-05-12 (S3)
**Iteration**: 3
**Last Updated**: 2026-05-12 (researcher-5)

## Current Focus

S3 (researcher-5) discharges `erdos_three_halves_conjecture_refuted`
from S2's `solymosi_stojakovic_lower_bound` by elementary real-analysis
arithmetic.  The sorry count drops from 3 → 2; the file is still axiom
free.

## Active Approach

**Specialise SS to `C = 1/2` and use the strict monotonicity of
`Real.rpow` in the exponent.**

1. Apply `solymosi_stojakovic_lower_bound (1/2 : ℝ)` to obtain `N₁` and
   a witness `P` for every `n ≥ N₁`.
2. Choose `m := max N₀ (max N₁ 3)`, so the hypothesised global upper
   bound applies at `P` of cardinality `m` and `m ≥ 3` gives the
   asymptotic threshold.
3. For `m ≥ 3 > Real.exp 1` (via `Real.exp_one_lt_d9`), `Real.log m > 1`,
   so `Real.sqrt (Real.log m) > 1`, so
   `(1/2) / Real.sqrt (Real.log m) < 1/2`, so the SS exponent
   `2 - (1/2) / Real.sqrt (Real.log m)` strictly exceeds `3/2`.
4. `Real.rpow_lt_rpow_of_exponent_lt hm_gt_one h_exp_gt` then gives
   `m^(3/2) < m^(2 - (1/2)/sqrt log m)`, which combined with the
   hypothesised `count ≤ m^(3/2)` and the SS bound
   `m^(2 - (1/2)/sqrt log m) ≤ count` produces a contradiction by
   `linarith`.

## Next Action

S4 candidates (in order of expected value):

1. **`Asymptotics.IsBigO` / `IsLittleO` bridge.** Define
   `maxFourPointLines : ℕ → ℕ` via `Finset.sup'` or `Set.Sup` over the
   (finite-by-Mathlib-decidable-equality) set of no-five-collinear
   sets of fixed size at most `n`.  Convert
   `fourPointLineCount_le_quadratic` into a `Asymptotics.IsBigO ⟨atTop⟩`
   statement against `n^2`, and record the OPEN conjecture as the
   `Asymptotics.IsLittleO` form `sorry`.  Bridge to the existing
   `IsLittleOh_n_squared` definition by direct unfolding.

2. **Refute Erdős's $\Theta(n^{3/2})$ via `Real.rpow` lower-bound
   formalisation**: extend the S3 refutation to a positive
   strict-inequality statement `∀ N, ∃ P, NoFiveCollinear P ∧ N ≤ |P|
   ∧ (P.points.card : ℝ)^(3/2 : ℝ) < (fourPointLineCount P : ℝ)`.
   This is the "constructive" (rather than negated-existence) form of
   the same fact and is a one-step rephrasing of the S3 proof.

3. **Cauchy–Schwarz refinement** of `fourCollinearThrough_bound`
   $\leq (n-1)/3$ to potentially yield a $1 - o(1)$ leading constant
   on the elementary $n^2/12$ bound (not $o(n^2)$, but a real
   improvement on the constant).

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1 (S3 discharge of refutation corollary)
- Approaches tried: 2 (S1 scaffold + S2 lower-bound recording;
  S3 elementary real-analysis discharge)

## Build Status

S3 build: **PENDING** (Docker not available in worktree;
`proofs/.lake` is a self-symlink and CI is ground truth).  S3
introduces *no new imports* — all required Mathlib API
(`Real.exp_one_lt_d9`, `Real.exp_pos`, `Real.log_exp`,
`Real.log_lt_log`, `Real.sqrt_one`, `Real.sqrt_lt_sqrt`,
`Real.rpow_lt_rpow_of_exponent_lt`, `div_lt_iff`) is already in
the S2 import set and is exercised by other gallery files
(see e.g. `Erdos1039Problem.lean`, `Erdos1201Problem.lean`,
`BinomialTheoremOQ03OQ02OQ03.lean`).

S3 risk profile:
* One discharge, no new theorem statements — the existing
  `erdos_three_halves_conjecture_refuted` is unchanged.
* The proof uses only well-established Mathlib API.
* The single tricky cast is `(m : ℕ) → (m : ℝ)`: handled by
  `exact_mod_cast hm_three : (3 : ℝ) ≤ (m : ℝ)`.

## Blockers

None for S3.  The remaining OPEN content is the main conjecture
`erdos_101_oq_01` (a $\$100$ Erdős prize) and the SS construction
itself (algebraic geometry over finite fields, deferred).
