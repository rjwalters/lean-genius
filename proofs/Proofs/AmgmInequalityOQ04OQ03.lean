import Mathlib
import Proofs.AmgmInequalityOQ04
import Proofs.AmgmInequalityOQ04OQ01

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
- the binomial series (1 - u)^{-1/2} = ∑ (2n choose n)/4ⁿ · uⁿ for |u| < 1,
- substituting u = k² sin²θ and integrating term by term over [0, π/2],
- justifying the sum/integral interchange (dominated convergence, delicate as
  k → 1), and
- the Wallis integral ∫₀^{π/2} sin^{2n}θ dθ = (π/2)·(2n choose n)/4ⁿ.

Mathlib has the central binomial coefficient and `integral_sin_pow`
recurrences but neither a general ₂F₁ nor the term-by-term integration lemma in
the form needed here, so the full identity is a multi-hundred-line build left
to future work. This mirrors the companion file's treatment of the AGM–K
connection. (Reference: Borwein & Borwein, *Pi and the AGM*, 1987.)

## Status
- [x] series coefficients defined
- [x] c₀ = 1, c₁ = 1/4, cₙ > 0 (proved, 0 sorry)
- [x] ₂F₁(…;0) = 1 (proved)
- [x] k = 0 consistency with `ellipticK` (proved, independent of the axiom)
- [ ] K(k) = (π/2)·₂F₁(1/2,1/2;1;k²) (axiomatized — see above)

Axioms: 1 (ellipticK_eq_hyp2F1 — the hypergeometric series identity for K)
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

/-- **Hypergeometric series representation of K** (axiomatized deep identity):
    for `|k| < 1`,
      `K(k) = (π/2) · ₂F₁(1/2, 1/2; 1; k²)`.
    See the file header for the proof outline (binomial series + Wallis
    integrals + term-by-term integration) and why it is left axiomatized.
    The `k = 0` instance is independently verified by
    `ellipticK_hyp2F1_consistent_zero`. -/
axiom ellipticK_eq_hyp2F1 (k : ℝ) (hk : k ^ 2 < 1) :
    ellipticK k = (π / 2) * hyp2F1 (k ^ 2)

/-- Sanity check: the axiom specialized at `k = 0` reproduces the independently
    proved consistency theorem (both reduce to `K(0) = π/2`). -/
theorem ellipticK_eq_hyp2F1_zero :
    ellipticK 0 = (π / 2) * hyp2F1 ((0 : ℝ) ^ 2) :=
  ellipticK_eq_hyp2F1 0 (by norm_num)

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

end AmgmInequalityOQ04OQ03
