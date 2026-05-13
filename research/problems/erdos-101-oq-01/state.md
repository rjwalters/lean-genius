# Current State

**Phase**: ACT
**Since**: 2026-05-13 (S4)
**Iteration**: 4
**Last Updated**: 2026-05-13 (researcher-1)

## Current Focus

S4 (researcher-1) extends S3's negated-existence refutation
`erdos_three_halves_conjecture_refuted` to its positive constructive
form `erdos_three_halves_conjecture_refuted_constructive`: for every
threshold `N`, an explicit no-five-collinear witness `P` with
`|P| ≥ N` and `|P|^{3/2} < fourPointLineCount P`. The proof reuses
S3's chain verbatim through the `Real.rpow_lt_rpow_of_exponent_lt`
step; only the final assembly differs (witness delivery vs.
contradiction). Sorries unchanged at 2 (main conjecture +
`solymosi_stojakovic_lower_bound`); axioms unchanged at 0; theorems
8 → 9. File grows 383 → 470 LOC (+87).

## Previous Focus

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

S5 candidates (in order of expected value):

1. **`Asymptotics.IsBigO` / `IsLittleO` bridge** (S4-candidate-1
   carried forward). Define `maxFourPointLines : ℕ → ℕ` via
   `Finset.sup'` or `Set.Sup` over the (finite-by-Mathlib-decidable-
   equality) set of no-five-collinear sets of fixed size at most `n`.
   Convert `fourPointLineCount_le_quadratic` into a
   `Asymptotics.IsBigO ⟨atTop⟩` statement against `n^2`, and record
   the OPEN conjecture as the `Asymptotics.IsLittleO` form `sorry`.
   Bridge to the existing `IsLittleOh_n_squared` definition by direct
   unfolding.

2. **Cauchy–Schwarz refinement** of `fourCollinearThrough_bound`
   $\leq (n-1)/3$ to potentially yield a $1 - o(1)$ leading constant
   on the elementary $n^2/12$ bound (not $o(n^2)$, but a real
   improvement on the constant).

3. **Witness extraction at fixed `n`**: pin down what
   `fourPointLineCount` is for small no-five-collinear sets via
   `decide` on the underlying finite combinatorics — would supply
   `native_decide`-certified examples for the gallery entry.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 1 (S4 constructive refutation, this iteration)
- Approaches tried: 3 (S1 scaffold + S2 lower-bound recording;
  S3 elementary real-analysis discharge; S4 constructive rephrasing
  of S3 chain)

## Build Status

S4 build: **PENDING** (Docker not available in worktree;
`proofs/.lake` is a self-symlink and CI is ground truth). S4 introduces
*no new imports* — the same Mathlib API as S3 is used
(`Real.exp_one_lt_d9`, `Real.exp_pos`, `Real.log_exp`,
`Real.log_lt_log`, `Real.sqrt_one`, `Real.sqrt_lt_sqrt`,
`Real.rpow_lt_rpow_of_exponent_lt`, `div_lt_iff`).

S4 risk profile:
* One new theorem statement
  (`erdos_three_halves_conjecture_refuted_constructive`); no edits
  to S3's `erdos_three_halves_conjecture_refuted`.
* The proof is structurally a copy of S3 through the
  `Real.rpow_lt_rpow_of_exponent_lt` step; only the final assembly
  changes from `linarith [hP_lb, hP_ub_m, h_rpow_lt]` (contradiction)
  to `linarith [hP_lb, h_rpow_lt]` (chain `m^(3/2) < m^(2-...) ≤ count`).
* `hcard.symm ▸ hm_N` provides the `N ≤ P.points.card` part of the
  triple after destructuring; `rw [hcard]` rewrites `P.points.card`
  to `m` in the final inequality.

## Blockers

None for S4.  The remaining OPEN content is the main conjecture
`erdos_101_oq_01` (a $\$100$ Erdős prize) and the SS construction
itself (algebraic geometry over finite fields, deferred).
