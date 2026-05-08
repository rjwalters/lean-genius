# Current State

**Phase**: ORIENT (sharpened, ready for ACT)
**Since**: 2026-05-08T07:50:00Z
**Iteration**: 3

## Current Focus

Session 3 (SURVEY): pinned down the exact Mathlib lemma to use for differentiating
`E(k) = ∫₀^{π/2} √(1 - k²·sin²θ) dθ` and `K(k) = ∫₀^{π/2} 1/√(1 - k²·sin²θ) dθ`
under the integral sign. The lemma is:

**`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`** in
`Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`.

The dominated form (uniform integrable bound on `F'`) is the right fit: on any
compact subinterval `[k₀ - δ, k₀ + δ] ⊂ (0, 1)`, both the integrand and its
k-derivative admit straightforward bounds. See
`sessions/2026-05-08-s03-mathlib-survey.md` for the full hypothesis-by-hypothesis
plan, the algebraic split that takes `∫ F'` to `(E - K)/k`, and the parallel
plan for `dK/dk`.

Stub already exists in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (Iteration 2);
the general Legendre relation is currently an axiom. With the lemma now pinned,
Session 4 can begin ACT-mode proof of `dE_dk`.

## Active Approach

**ODE / Wronskian (Whittaker–Watson §22.41)**: prove `dE/dk = (E - K)/k` and
`dK/dk = (E - k'²K)/(k·k'²)` by differentiation under the integral via
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, then show
the bracketed combination `f(k) = E·K' + E'·K - K·K'` has zero derivative on
(0, 1), hence is constant; pin the constant via `legendre_relation_symmetric`.

**Why this approach over the AGM/Brent-Salamin path**: the AGM/Landen approach
needs Mathlib's quadratic AGM convergence theorem (also missing) plus a
non-trivial Landen transformation lemma. The ODE/Wronskian approach uses only
the now-pinned `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
plus `Continuous.intervalIntegrable` and standard chain-rule lemmas.

## Blockers

1. ~~Mathlib has differentiation-under-the-integral but it's not yet wired up to~~
   ~~`ellipticK`/`ellipticE`. ~80-150 lines of plumbing per derivative.~~
   **Status: NOT a Mathlib gap — Mathlib has
   `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The
   "plumbing" is gallery-side, ~75-100 lines per derivative (see Next Action).**
2. The Legendre ODE for K(k) (k(1-k²)y'' + (1-3k²)y' - k·y = 0) has no Mathlib
   infrastructure for second-order ODEs of this form. May not be needed if we
   compute the derivatives directly. **Status: avoidable; the Wronskian
   argument needs only first derivatives and `eq_of_hasDerivAt_eq_zero` (in
   Mathlib).**

## Next Action

**Session 4 (ACT)**: Prove `dE_dk` in
`proofs/Proofs/AmgmInequalityOQ04OQ02.lean`. Target signature:

```lean
theorem dE_dk (k : ℝ) (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticE ((ellipticE k - ellipticK k) / k) k
```

Plan (from S3 survey):

1. Set `F (k : ℝ) (θ : ℝ) := √(1 - k²·sin²θ)` and
   `F' (k : ℝ) (θ : ℝ) := -k·sin²θ / √(1 - k²·sin²θ)`.
2. Choose `δ` with `0 < δ < min k (1 - k)`; set
   `s := Set.Ioo (k - δ) (k + δ)` and
   `bound (θ : ℝ) := (k + δ)·sin²θ / √(1 - (k + δ)²·sin²θ)`.
3. Discharge the seven hypotheses of
   `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`:
   `hs`, `hF_meas`, `hF_int`, `hF'_meas`, `h_bound`, `bound_integrable`,
   `h_diff`. Each is straightforward (chain rule for the integrand, monotonicity
   for the bound, `Continuous.intervalIntegrable` for integrability).
4. Convert the conclusion `HasDerivAt E (∫ F' dθ) k` to
   `HasDerivAt E ((E k - K k)/k) k` via the algebraic identity
   `-k²·sin²θ = (1 - k²·sin²θ) - 1`, integrating to `E·k - K·k` and dividing
   by `k`.

Estimated ~75-100 lines.

After `dE_dk` lands, mirror for `dK_dk` (~80-100 lines), then the Wronskian
closure (~50 lines using `eq_of_hasDerivAt_eq_zero`).

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 2 (S2 stub, S3 SURVEY)
- Approaches tried: 1 (ODE/Wronskian — stub written; Mathlib lemma pinned)

## References

- `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean` —
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (the
  workhorse for `dE/dk` and `dK/dk`).
- `Mathlib/Analysis/Calculus/ParametricIntegral.lean` — non-interval analogue
  (used internally; not directly needed).
- `Mathlib/Analysis/Calculus/MeanValue.lean` —
  `eq_of_hasDerivAt_eq_zero` style lemma for the constant-Wronskian step.
- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` — gallery file with `ellipticE`,
  `ellipticK`, complementary modulus, and the symmetric Legendre relation
  derived from the general axiom (1 axiom, 0 sorries; this iteration's target
  is to eliminate the 1 axiom).
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-08-s03-mathlib-survey.md`
  (this iteration's full plan).
