import Mathlib
import Proofs.AmgmInequalityOQ04
import Proofs.AmgmInequalityOQ04OQ01
import Proofs.AmgmInequalityOQ04OQ03Wallis

/-
# AGM: Hypergeometric Series Representation of K(k)

Open Question (OQ-04-OQ-03 from AmgmInequality):
Express the complete elliptic integral of the first kind through the Gauss
hypergeometric series, the standard route toward Gauss's AGM theorem
  M(a, b) = a·π / (2·K(k')),   k = b/a,  k' = √(1 - k²).

## The Identity

The classical power-series representation is
  K(k) = (π/2) · ₂F₁(1/2, 1/2; 1; k²)
       = (π/2) · ∑_{n≥0} ((2n choose n) / 4ⁿ)² · k^{2n}
       = (π/2) · [1 + (1/2)² k² + (1·3/(2·4))² k⁴ + ⋯].

The n-th series coefficient is cₙ = ((1/2)_n / n!)² = ((2n choose n)/4ⁿ)², where
(1/2)_n is the rising factorial; the second equality is the identity
(1/2)_n / n! = (2n choose n)/4ⁿ for the central binomial coefficient.

## What This File Does

`ellipticK` is the rigorous interval-integral definition from the companion
file `AmgmInequalityOQ04OQ01.lean`. This file:

1. Defines the series coefficients `hypCoeff n = (centralBinom n / 4ⁿ)²`.
2. Defines `hyp2F1 x = ∑' n, hypCoeff n · xⁿ`, the realization of
   ₂F₁(1/2,1/2;1;x) as a power series.
3. Proves verifiable structural facts: `c₀ = 1`, `c₁ = 1/4`, every `cₙ > 0`,
   and `₂F₁(…;0) = 1`.
4. Proves the **k = 0 consistency theorem** independently of the deep identity:
   `K(0) = (π/2)·₂F₁(…;0)`, i.e. both sides equal π/2. This checks that the
   axiomatized identity below has the correct value at the one point where K is
   elementary.
5. States the deep series identity `ellipticK_eq_hyp2F1` as an axiom.

## Why the Main Identity is Axiomatized

Proving `K(k) = (π/2)·₂F₁(1/2,1/2;1;k²)` rigorously requires:
- the binomial series (1 - u)^{-1/2} = ∑ (2n choose n)/4ⁿ · uⁿ for |u| < 1
  (PROVED in §10, `hasSum_inv_sqrt_one_sub` / `hasSum_ellipticIntegrand`, via
  Mathlib's `Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`),
- the Wallis integral ∫₀^{π/2} sin^{2n}θ dθ = (π/2)·(2n choose n)/4ⁿ
  (PROVED as `wallisHalf_even` in the companion
  `AmgmInequalityOQ04OQ03Wallis.lean`), and
- substituting u = k² sin²θ and integrating term by term over [0, π/2] —
  justifying the sum/integral interchange (dominated convergence, delicate as
  k → 1). This interchange is the one remaining leg; until it lands the full
  identity stays axiomatized. This mirrors the companion file's treatment of
  the AGM–K connection. (Reference: Borwein & Borwein, *Pi and the AGM*, 1987.)

## Status
- [x] series coefficients defined
- [x] c₀ = 1, c₁ = 1/4, cₙ > 0 (proved, 0 sorry)
- [x] ₂F₁(…;0) = 1 (proved)
- [x] k = 0 consistency with `ellipticK` (proved, independent of the axiom)
- [x] summability + uniform convergence + continuity of ₂F₁ on (-1,1) (§6–§9)
- [x] binomial series 1/√(1-u) = ∑ (centralBinom n/4ⁿ)uⁿ, |u| < 1 (§10)
- [x] pointwise series expansion of the K integrand (§10)
- [x] K(k) = (π/2)·₂F₁(1/2,1/2;1;k²) — **PROVED** (§11: dominated-convergence
      sum/integral interchange + Wallis values; formerly the file's one axiom)

Axioms: 0
Sorries: 0
-/

namespace AmgmInequalityOQ04OQ03

open Real AmgmInequalityOQ04OQ01

-- ============================================================================
-- § 1. The Hypergeometric Series for K
-- ============================================================================

/-- The n-th coefficient of the hypergeometric series for K:
    `cₙ = ((2n choose n) / 4ⁿ)² = (centralBinom n / 4ⁿ)²`.
    These are the squares of the `4ⁿ`-normalized central binomial coefficients. -/
noncomputable def hypCoeff (n : ℕ) : ℝ :=
  ((Nat.centralBinom n : ℝ) / 4 ^ n) ^ 2

/-- The Gauss hypergeometric function ₂F₁(1/2, 1/2; 1; x) realized as a power
    series: `₂F₁(1/2,1/2;1;x) = ∑_{n≥0} cₙ xⁿ`. -/
noncomputable def hyp2F1 (x : ℝ) : ℝ :=
  ∑' n : ℕ, hypCoeff n * x ^ n

-- ============================================================================
-- § 2. Basic Properties of the Coefficients
-- ============================================================================

/-- `c₀ = 1`: the constant term of the series. -/
lemma hypCoeff_zero : hypCoeff 0 = 1 := by
  simp [hypCoeff, Nat.centralBinom_zero]

/-- `c₁ = 1/4`, matching the classical expansion
    `K(k) = (π/2)[1 + (1/2)² k² + ⋯]` whose `k²` coefficient is `(1/2)² = 1/4`. -/
lemma hypCoeff_one : hypCoeff 1 = 1 / 4 := by
  have h : Nat.centralBinom 1 = 2 := by decide
  unfold hypCoeff
  rw [h]
  norm_num

/-- Every coefficient is nonnegative (it is a square). -/
lemma hypCoeff_nonneg (n : ℕ) : 0 ≤ hypCoeff n := by
  unfold hypCoeff; positivity

/-- Every coefficient is strictly positive (central binomial coefficients are
    positive). -/
lemma hypCoeff_pos (n : ℕ) : 0 < hypCoeff n := by
  have hb : (0 : ℝ) < (Nat.centralBinom n : ℝ) / 4 ^ n :=
    div_pos (by exact_mod_cast Nat.centralBinom_pos n) (by positivity)
  simpa [hypCoeff] using pow_pos hb 2

-- ============================================================================
-- § 3. Value at the Origin
-- ============================================================================

/-- `₂F₁(1/2,1/2;1;0) = 1`: only the constant term survives at `x = 0`. -/
theorem hyp2F1_zero : hyp2F1 0 = 1 := by
  have h : ∀ n : ℕ, n ≠ 0 → hypCoeff n * (0 : ℝ) ^ n = 0 := by
    intro n hn
    rw [zero_pow hn, mul_zero]
  unfold hyp2F1
  rw [tsum_eq_single 0 h]
  simp [hypCoeff_zero]

-- ============================================================================
-- § 4. Consistency with the Elliptic Integral at k = 0
-- ============================================================================

/-- **Consistency at k = 0**, proved independently of the axiomatized identity:
    `K(0) = (π/2)·₂F₁(1/2,1/2;1;0)`. Both sides equal `π/2`
    (`ellipticK_zero` gives the left side; `hyp2F1_zero` the right). This
    verifies the value of the hypergeometric identity at the one point where the
    elliptic integral is elementary. -/
theorem ellipticK_hyp2F1_consistent_zero :
    ellipticK 0 = (π / 2) * hyp2F1 0 := by
  rw [hyp2F1_zero, mul_one, ellipticK_zero]

-- ============================================================================
-- § 5. The Hypergeometric Identity for K (Axiomatized)
-- ============================================================================

/- **Hypergeometric series representation of K** — formerly the file's one
   axiom, now a THEOREM: see § 11 at the end of the file
   (`ellipticK_eq_hyp2F1`, proved by term-by-term integration of the § 10
   binomial series against the Wallis values, with the sum/integral
   interchange justified by dominated convergence). The statement had to move
   below the § 6–§ 10 machinery it consumes. -/

-- ============================================================================
-- § 6. Summability of the Hypergeometric Series  (S2 ACT, 2026-06-01)
-- ============================================================================
--
-- Real progress toward discharging the §5 axiom: term-by-term integration of
-- the binomial series requires *summability* of `∑ hypCoeff n · k^(2n)` as a
-- prerequisite (sum/integral interchange via dominated convergence).
-- This section establishes that summability for |x| < 1 via direct comparison
-- with the geometric series, using the standard central-binomial bound
-- `C(2n, n) ≤ 4^n` (which Mathlib v4.26.0 has only as a lower bound
-- `Nat.four_pow_lt_mul_centralBinom`).

/-- The central binomial coefficient is bounded above by `4^n`.
    Proof: `C(2n, n)` is one entry in the binomial row of `(1+1)^(2n) = 2^(2n)
    = 4^n`; since every entry is nonnegative, the single entry is ≤ the row
    sum. -/
lemma centralBinom_le_four_pow (n : ℕ) : Nat.centralBinom n ≤ 4 ^ n := by
  have hmem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  have hsum : Nat.choose (2 * n) n
      ≤ ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m :=
    Finset.single_le_sum (f := fun m => Nat.choose (2 * n) m)
      (fun _ _ => Nat.zero_le _) hmem
  have hpow : 2 ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]; norm_num
  calc Nat.centralBinom n
      = Nat.choose (2 * n) n := Nat.centralBinom_eq_two_mul_choose n
    _ ≤ ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m := hsum
    _ = 2 ^ (2 * n) := Nat.sum_range_choose (2 * n)
    _ = 4 ^ n := hpow

/-- Each hypergeometric coefficient is bounded above by `1`:
    `cₙ = (C(2n,n) / 4ⁿ)² ≤ 1`, using `centralBinom_le_four_pow` and
    `pow_le_one₀` (Mathlib v4.26.0 name; `pow_le_one` from earlier
    snapshots was renamed). -/
lemma hypCoeff_le_one (n : ℕ) : hypCoeff n ≤ 1 := by
  have hb : ((Nat.centralBinom n : ℝ) / 4 ^ n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h := centralBinom_le_four_pow n
    have hcast : (4 ^ n : ℝ) = ((4 ^ n : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast h
  have h0 : (0 : ℝ) ≤ (Nat.centralBinom n : ℝ) / 4 ^ n :=
    div_nonneg (by exact_mod_cast Nat.zero_le _) (by positivity)
  show ((Nat.centralBinom n : ℝ) / 4 ^ n) ^ 2 ≤ 1
  exact pow_le_one₀ h0 hb

/-- **Summability of the hypergeometric series** for `|x| < 1`.
    Proof: `|hypCoeff n · xⁿ| = hypCoeff n · |x|ⁿ ≤ |x|ⁿ` (using
    `hypCoeff_le_one` + `hypCoeff_nonneg`), and `∑ |x|ⁿ` is the convergent
    geometric series. Then absolute-summability implies summability in `ℝ`.

    This is the structural input that the term-by-term integration step of the
    discharge of `ellipticK_eq_hyp2F1` will consume (dominated-convergence-style
    sum/integral interchange on `[0, π/2]`). -/
theorem summable_hyp2F1 (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => hypCoeff n * x ^ n) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (abs_nonneg _) hx)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (hypCoeff_nonneg n)]
  have hc : hypCoeff n ≤ 1 := hypCoeff_le_one n
  have hxn : (0 : ℝ) ≤ |x| ^ n := pow_nonneg (abs_nonneg _) n
  calc hypCoeff n * |x| ^ n
      ≤ 1 * |x| ^ n := mul_le_mul_of_nonneg_right hc hxn
    _ = |x| ^ n := one_mul _

-- ============================================================================
-- §7 : Per-term M-test bound on compact subsets of (-1, 1)        (S4a ACT)
-- ============================================================================
--
-- Strengthens the per-term inequality from §6: instead of an `|x|`-dependent
-- bound, gives an `x`-independent bound `|hypCoeff n · x^n| ≤ R^n` valid
-- uniformly on `{x : |x| ≤ R}`. This is the M-test primitive needed to
-- extend `summable_hyp2F1` to a uniform-on-compacta summability statement
-- (`TendstoUniformlyOn`) — itself an input to the term-by-term integration
-- step in the eventual discharge of `ellipticK_eq_hyp2F1`.

/-- **Per-term uniform bound for the hypergeometric series on compact
    subsets of `(-1, 1)`** (S4a ACT, 2026-06-09).

For any `0 ≤ R` and `x` with `|x| ≤ R`, the n-th term satisfies the
**`x`-independent** bound `|hypCoeff n · x^n| ≤ R^n`. The M-test then
gives summability of `∑ R^n` (for `R < 1`) as a dominating series valid
*uniformly* across the compact set `[-R, R]`. Compare `summable_hyp2F1`
(§6), where the dominating series `∑ |x|^n` depends on the chosen `x`.

Proof:
`|hypCoeff n · x^n| = hypCoeff n · |x|^n ≤ 1 · |x|^n = |x|^n ≤ R^n`,
using `hypCoeff_le_one` and monotonicity of `(·)^n` on nonnegatives. -/
lemma hypCoeff_mul_pow_abs_le_of_abs_le
    (R : ℝ) (n : ℕ) (x : ℝ) (hx : |x| ≤ R) :
    |hypCoeff n * x ^ n| ≤ R ^ n := by
  have hR : 0 ≤ R := le_trans (abs_nonneg _) hx
  rw [abs_mul, abs_pow, abs_of_nonneg (hypCoeff_nonneg n)]
  calc hypCoeff n * |x| ^ n
      ≤ 1 * |x| ^ n :=
        mul_le_mul_of_nonneg_right (hypCoeff_le_one n)
          (pow_nonneg (abs_nonneg _) n)
    _ = |x| ^ n := one_mul _
    _ ≤ R ^ n := pow_le_pow_left₀ (abs_nonneg _) hx n

-- ============================================================================
-- §8 : Uniform M-test inputs + Summable on closed ball             (S4b ACT)
-- ============================================================================
--
-- Combines S4a's `x`-independent per-term bound (§7) with the convergent
-- geometric series `∑ R^n` for `R < 1`. Concretely:
--
-- (i) Provides per-`x` summability on the closed ball `{x : |x| ≤ R}` via
--     the *uniform* dominating series `R^n` — compare `summable_hyp2F1`
--     (§6), which uses the `x`-dependent series `|x|^n`. Although the
--     conclusion matches §6, the proof path now factors through a single
--     `x`-independent dominating series, which is the structural setup
--     required for the Weierstrass M-test conclusion.
--
-- (ii) Packages the M-test hypotheses as an explicit lemma
--      `hyp2F1_mtest_inputs_on_closedBall` consumable by the
--      `TendstoUniformlyOn` step (S5 ACT).

/-- **Summable via uniform M-test on closed ball** (S4b ACT, 2026-06-09).

For `R < 1` and any `x` with `|x| ≤ R`, the series `∑ hypCoeff n · xⁿ`
is summable. Proved by direct comparison with the geometric series
`∑ R^n` whose summands are *independent* of `x`. Compare `summable_hyp2F1`
(§6), where the dominating series `∑ |x|ⁿ` varies with `x`. Provides the
per-`x` summability needed at every point of the compact subset
`{x : |x| ≤ R}`, with the proof path that prepares the M-test step. -/
theorem summable_hyp2F1_on_closedBall
    (R : ℝ) (hR : R < 1) (x : ℝ) (hx : |x| ≤ R) :
    Summable (fun n : ℕ => hypCoeff n * x ^ n) := by
  have hRnn : 0 ≤ R := le_trans (abs_nonneg _) hx
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one hRnn hR)
  rw [Real.norm_eq_abs]
  exact hypCoeff_mul_pow_abs_le_of_abs_le R n x hx

/-- **M-test inputs for the hypergeometric series on closed ball**
    (S4b ACT, 2026-06-09).

Bundles the two Weierstrass-M-test hypotheses on `{x : |x| ≤ R}`:
(a) `∑ R^n` is summable (since `R < 1`), and
(b) the per-term uniform bound `|hypCoeff n · x^n| ≤ R^n` holds for
    every `x` with `|x| ≤ R`.

This is exactly the data consumed by `tendstoUniformlyOn_tsum` in
Mathlib's `Analysis.NormedSpace.FunctionSeries`. Packaged as a single
lemma so the `TendstoUniformlyOn` step (S5 ACT) is a one-liner. -/
theorem hyp2F1_mtest_inputs_on_closedBall
    (R : ℝ) (hR : R < 1) (hRnn : 0 ≤ R) :
    Summable (fun n : ℕ => R ^ n) ∧
      ∀ (n : ℕ) (x : ℝ), x ∈ {y : ℝ | |y| ≤ R} →
        ‖hypCoeff n * x ^ n‖ ≤ R ^ n := by
  refine ⟨summable_geometric_of_lt_one hRnn hR, fun n x hx => ?_⟩
  rw [Real.norm_eq_abs]
  exact hypCoeff_mul_pow_abs_le_of_abs_le R n x hx

-- ============================================================================
-- §9 : Uniform convergence on closed balls + continuity            (S5 ACT)
-- ============================================================================
--
-- Consumes the §8 M-test package through Mathlib's Weierstrass M-test
-- (`tendstoUniformlyOn_tsum_nat`) and extracts the payoff: the partial sums
-- of the hypergeometric series converge to `hyp2F1` UNIFORMLY on every closed
-- ball `{x : |x| ≤ R}`, `R < 1`; being polynomials, they are continuous, so
-- `hyp2F1` is continuous on each closed ball and hence at every point of the
-- open unit ball. Continuity is the analytic ingredient the eventual Gauss
-- AGM-limit argument needs on the `K`-side of the axiomatized identity
-- (`ellipticK_eq_hyp2F1`): the AGM iteration's limit exchange happens inside
-- the open unit ball of the modulus.

/-- **Weierstrass M-test payoff** (S5 ACT): on the closed ball `{x : |x| ≤ R}`
with `R < 1`, the partial sums `x ↦ ∑_{n < N} cₙ xⁿ` converge uniformly to
`hyp2F1`. One-liner from the §8 package + `tendstoUniformlyOn_tsum_nat`,
exactly as the S4b design intended. -/
theorem hyp2F1_tendstoUniformlyOn_closedBall (R : ℝ) (hR : R < 1) (hRnn : 0 ≤ R) :
    TendstoUniformlyOn
      (fun N : ℕ => fun x : ℝ => ∑ n ∈ Finset.range N, hypCoeff n * x ^ n)
      hyp2F1 Filter.atTop {y : ℝ | |y| ≤ R} := by
  obtain ⟨hsum, hbound⟩ := hyp2F1_mtest_inputs_on_closedBall R hR hRnn
  exact tendstoUniformlyOn_tsum_nat hsum hbound

/-- The partial sums are polynomials, hence continuous. -/
private lemma continuous_partialSum (N : ℕ) :
    Continuous (fun x : ℝ => ∑ n ∈ Finset.range N, hypCoeff n * x ^ n) :=
  continuous_finsetSum _ fun n _ => (continuous_pow n).const_mul (hypCoeff n)

/-- **Continuity of `₂F₁(1/2,1/2;1;·)` on closed balls** (S5 ACT): a uniform
limit of continuous partial sums is continuous on `{x : |x| ≤ R}`, `R < 1`. -/
theorem hyp2F1_continuousOn_closedBall (R : ℝ) (hR : R < 1) (hRnn : 0 ≤ R) :
    ContinuousOn hyp2F1 {y : ℝ | |y| ≤ R} :=
  (hyp2F1_tendstoUniformlyOn_closedBall R hR hRnn).continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun N =>
      (continuous_partialSum N).continuousOn))

/-- **Continuity of `₂F₁(1/2,1/2;1;·)` at every point of the open unit ball**
(S5 ACT): each `x` with `|x| < 1` lies in the interior of the closed ball of
radius `(|x| + 1)/2 < 1`, on which `hyp2F1` is continuous. -/
theorem hyp2F1_continuousAt {x : ℝ} (hx : |x| < 1) : ContinuousAt hyp2F1 x := by
  set R : ℝ := (|x| + 1) / 2 with hRdef
  have hxR : |x| < R := by
    rw [hRdef]; linarith
  have hR : R < 1 := by
    rw [hRdef]; linarith
  have hRnn : 0 ≤ R := le_trans (abs_nonneg x) hxR.le
  have hmem : {y : ℝ | |y| ≤ R} ∈ nhds x := by
    refine Filter.mem_of_superset ?_ (fun y (hy : |y| < R) => le_of_lt hy)
    exact (isOpen_lt continuous_abs continuous_const).mem_nhds hxR
  exact (hyp2F1_continuousOn_closedBall R hR hRnn).continuousAt hmem

/-- **Continuity on the open unit ball** (S5 ACT), packaged as `ContinuousOn`
for downstream use with the axiomatized identity `ellipticK_eq_hyp2F1` (whose
modulus square `k²` ranges over `[0, 1)`). -/
theorem hyp2F1_continuousOn_ball : ContinuousOn hyp2F1 {y : ℝ | |y| < 1} :=
  fun _ hy => (hyp2F1_continuousAt hy).continuousWithinAt

-- ============================================================================
-- § 10. Leg 3: the binomial series (1-u)^(-1/2) = ∑ (centralBinom n/4ⁿ) uⁿ
--       (S6 ACT)
-- ============================================================================
-- Mathlib's `Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero` provides
-- the power series of `x ↦ 1/(1-x)^a` on the unit ball with coefficients
-- `Ring.choose (a + n - 1) n`. Specializing to `a = 1/2` and identifying the
-- generalized binomial coefficient with `centralBinom n / 4ⁿ` yields the
-- binomial series leg of the axiom-discharge plan, landed directly on the
-- integrand of `ellipticK`.

/-- Rising factorial at `1/2`: `(1/2)ₙ = n! · centralBinom n / 4ⁿ`.
    Induction threads `Nat.succ_mul_centralBinom_succ` through
    `ascPochhammer_succ_eval`, the same recurrence used for the Wallis
    closed form (Leg 2). -/
lemma ascPochhammer_eval_half (n : ℕ) :
    (ascPochhammer ℝ n).eval (1 / 2 : ℝ)
      = (n.factorial : ℝ) * Nat.centralBinom n / 4 ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hcb : ((m : ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ)
          = 2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ m
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hC : (Nat.centralBinom (m + 1) : ℝ)
          = 2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) / ((m : ℝ) + 1) := by
        field_simp
        linarith [hcb]
      rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ, hC]
      push_cast
      have h4 : (4 : ℝ) ^ m ≠ 0 := by positivity
      field_simp
      ring

/-- The generalized binomial coefficient of the series for `(1-u)^{-1/2}`:
    `Ring.multichoose (1/2) n = centralBinom n / 4ⁿ`. -/
lemma multichoose_half (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) n = (Nat.centralBinom n : ℝ) / 4 ^ n := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
  rw [Polynomial.ascPochhammer_smeval_eq_eval, ascPochhammer_eval_half,
    nsmul_eq_mul] at h
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  refine mul_left_cancel₀ hfac ?_
  rw [h]; ring

/-- `Ring.choose (1/2 + n - 1) n = centralBinom n / 4ⁿ`, the exact coefficient
    form consumed by Mathlib's binomial power series. -/
lemma ringChoose_half (n : ℕ) :
    Ring.choose ((1 / 2 : ℝ) + n - 1) n = (Nat.centralBinom n : ℝ) / 4 ^ n := by
  rw [← Ring.multichoose_eq, multichoose_half]

/-- The hypergeometric coefficient is the square of the binomial-series
    coefficient: `cₙ = (centralBinom n / 4ⁿ)²`. Together with the Wallis
    closed form `wallisHalf_even` (Leg 2) this is why term-by-term
    integration of the binomial series produces exactly `hyp2F1`. -/
lemma hypCoeff_eq_sq (n : ℕ) :
    hypCoeff n = ((Nat.centralBinom n : ℝ) / 4 ^ n) ^ 2 := rfl

/-- **The binomial series for the inverse square root** (Leg 3 of the
    axiom-discharge plan): for `|u| < 1`,
    `1/√(1-u) = ∑_{n≥0} (centralBinom n / 4ⁿ) uⁿ`. -/
theorem hasSum_inv_sqrt_one_sub {u : ℝ} (hu : |u| < 1) :
    HasSum (fun n : ℕ => (Nat.centralBinom n : ℝ) / 4 ^ n * u ^ n)
      (1 / Real.sqrt (1 - u)) := by
  have H := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)
  have hu' : u ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero]
    exact ENNReal.ofReal_lt_one.mpr hu
  have hs := H.hasSum hu'
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq,
    ringChoose_half, smul_eq_mul] at hs
  rw [Real.sqrt_eq_rpow]
  exact hs

/-- The binomial series in `tsum` form. -/
theorem inv_sqrt_one_sub_eq_tsum {u : ℝ} (hu : |u| < 1) :
    1 / Real.sqrt (1 - u) = ∑' n : ℕ, (Nat.centralBinom n : ℝ) / 4 ^ n * u ^ n :=
  (hasSum_inv_sqrt_one_sub hu).tsum_eq.symm

/-- **Series expansion of the elliptic integrand** (Leg 3 landed on the
    target): for `k² < 1` the integrand of `K(k)` expands pointwise as
    `1/√(1-k²sin²θ) = ∑ (centralBinom n / 4ⁿ) (k² sin²θ)ⁿ`, at every `θ`.
    Term-by-term integration over `[0, π/2]` against the Wallis values
    `wallisHalf_even` is now the only remaining step (Leg 4, the
    sum/integral interchange) to discharge `ellipticK_eq_hyp2F1`. -/
theorem hasSum_ellipticIntegrand (k θ : ℝ) (hk : k ^ 2 < 1) :
    HasSum (fun n : ℕ =>
        (Nat.centralBinom n : ℝ) / 4 ^ n * (k ^ 2 * Real.sin θ ^ 2) ^ n)
      (ellipticIntegrand k θ) := by
  have hsin : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hu : |k ^ 2 * Real.sin θ ^ 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg k, sq_nonneg (Real.sin θ)]
  simpa [ellipticIntegrand] using hasSum_inv_sqrt_one_sub hu

-- ============================================================================
-- § 11. Term-by-Term Integration: the Main Identity, PROVED  (S7, Leg 5)
-- ============================================================================
--
-- The final leg. The § 10 pointwise expansion of the integrand is integrated
-- term by term over [0, π/2]: the sum/integral interchange is dominated
-- convergence (`intervalIntegral.hasSum_integral_of_dominated_convergence`)
-- with the θ-independent dominating series `(centralBinom n/4ⁿ)·(k²)ⁿ`
-- (summable by the § 10 binomial series at u = k²), and each term integrates
-- to `(π/2)·hypCoeff n·(k²)ⁿ` by the Wallis values `wallisHalf_even`.
-- This discharges the former axiom: the file is now 0 axioms, 0 sorries.

open MeasureTheory in
/-- **The sum/integral interchange** (Leg 5): integrating the § 10 series
    expansion of the K integrand term by term over `[0, π/2]`. Dominated
    convergence with the constant-in-`θ` bound `(centralBinom n/4ⁿ)·(k²)ⁿ`,
    whose sum is the (finite) binomial series at `u = k² < 1`. -/
theorem hasSum_integral_ellipticIntegrand (k : ℝ) (hk : k ^ 2 < 1) :
    HasSum
      (fun n : ℕ => ∫ θ in (0 : ℝ)..π / 2,
        (Nat.centralBinom n : ℝ) / 4 ^ n * (k ^ 2 * Real.sin θ ^ 2) ^ n)
      (ellipticK k) := by
  have hk2 : |k ^ 2| < 1 := by rwa [abs_of_nonneg (sq_nonneg k)]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n _ => (Nat.centralBinom n : ℝ) / 4 ^ n * (k ^ 2) ^ n)
    (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · -- measurability of each term
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  · -- the θ-independent bound
    filter_upwards with θ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hbase : k ^ 2 * Real.sin θ ^ 2 ≤ k ^ 2 := by
      nlinarith [Real.sin_sq_le_one θ, sq_nonneg k]
    have hpow : (k ^ 2 * Real.sin θ ^ 2) ^ n ≤ (k ^ 2) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  · -- summability of the bound
    filter_upwards with θ _
    exact (hasSum_inv_sqrt_one_sub hk2).summable
  · -- integrability of the (constant) summed bound
    exact intervalIntegrable_const
  · -- pointwise convergence to the integrand
    filter_upwards with θ _
    exact hasSum_ellipticIntegrand k θ hk

/-- **Each term integrates to a hypergeometric coefficient**: pulling constants
    out and evaluating the Wallis integral `∫₀^{π/2} sin^{2n}θ dθ`. -/
theorem integral_term_eq_hypCoeff (k : ℝ) (n : ℕ) :
    (∫ θ in (0 : ℝ)..π / 2,
        (Nat.centralBinom n : ℝ) / 4 ^ n * (k ^ 2 * Real.sin θ ^ 2) ^ n)
      = (π / 2) * (hypCoeff n * (k ^ 2) ^ n) := by
  have hsplit : ∀ θ : ℝ,
      (Nat.centralBinom n : ℝ) / 4 ^ n * (k ^ 2 * Real.sin θ ^ 2) ^ n
        = ((Nat.centralBinom n : ℝ) / 4 ^ n * (k ^ 2) ^ n)
            * Real.sin θ ^ (2 * n) := by
    intro θ
    rw [mul_pow, pow_mul]
    ring
  simp_rw [hsplit]
  rw [intervalIntegral.integral_const_mul]
  rw [show (∫ θ in (0 : ℝ)..π / 2, Real.sin θ ^ (2 * n))
      = AmgmInequalityOQ04OQ03Wallis.wallisHalf (2 * n) from rfl]
  rw [AmgmInequalityOQ04OQ03Wallis.wallisHalf_even n]
  unfold hypCoeff
  ring

/-- **Hypergeometric series representation of K — the main identity, PROVED**
    (formerly this file's one axiom): for `k² < 1`,

      `K(k) = (π/2) · ₂F₁(1/2, 1/2; 1; k²)`.

    Proof: the § 10 binomial series expands the integrand pointwise
    (`hasSum_ellipticIntegrand`); dominated convergence integrates it term by
    term (`hasSum_integral_ellipticIntegrand`); each term is a Wallis integral
    evaluating to `(π/2)·hypCoeff n·(k²)ⁿ` (`integral_term_eq_hypCoeff`); and
    the resulting sum is `(π/2)·hyp2F1(k²)` by summability (§ 6). -/
theorem ellipticK_eq_hyp2F1 (k : ℝ) (hk : k ^ 2 < 1) :
    ellipticK k = (π / 2) * hyp2F1 (k ^ 2) := by
  have hsum := hasSum_integral_ellipticIntegrand k hk
  simp_rw [integral_term_eq_hypCoeff k] at hsum
  have hk2 : |k ^ 2| < 1 := by rwa [abs_of_nonneg (sq_nonneg k)]
  have h2 : HasSum (fun n : ℕ => (π / 2) * (hypCoeff n * (k ^ 2) ^ n))
      ((π / 2) * hyp2F1 (k ^ 2)) :=
    ((summable_hyp2F1 (k ^ 2) hk2).hasSum).mul_left _
  exact hsum.unique h2

/-- Sanity check: the theorem specialized at `k = 0` reproduces the
    independently proved consistency theorem (both reduce to `K(0) = π/2`). -/
theorem ellipticK_eq_hyp2F1_zero :
    ellipticK 0 = (π / 2) * hyp2F1 ((0 : ℝ) ^ 2) :=
  ellipticK_eq_hyp2F1 0 (by norm_num)

end AmgmInequalityOQ04OQ03
