import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-
# Basel Problem: Apéry Technique for ζ(5)

Open Question (OQ-03 from ZetaFiveIrrationality):
Can Apéry's method for proving ζ(3) irrational be extended to ζ(5)?

## Background

Apéry (1978) proved ζ(3) irrational by constructing integer sequences (aₙ, bₙ)
satisfying a 3-term recurrence such that bₙ·ζ(3) - aₙ → 0 geometrically with
bₙ·ζ(3) - aₙ ≠ 0. The geometric decay combined with integrality properties proves
irrationality via a simple denominators argument.

## This File

1. `apery_criterion`: The irrationality criterion Apéry exploited. (PROVED, 0 sorry)
2. `AperyWitness`: Abstract structure capturing Apéry's method.
3. `zetaFive_irrational_if_apery_witness`: Conditional theorem for ζ(5). (PROVED)
4. `geometric_decay_tendsto`: Geometric decay implies convergence to 0. (PROVED)
5. `StrongAperyWitness`: Enhanced structure with geometric decay rate.

## Status

OPEN. No Apéry-type sequences for ζ(5) are known as of 2026.
- Zudilin (2001): at least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational.
- Ball-Rivoal: infinitely many odd zeta values are irrational.
- But which specific ζ(2k+1) for k ≥ 2 are irrational remains unknown.

Axioms: 0
Sorries: 0
-/

namespace BaselProblemOQ01OQ03

open Filter BigOperators Real

-- ============================================================
-- Part I: The Apéry Irrationality Criterion
-- ============================================================

/-- **Irrationality Criterion** (Apéry's core technique):
    If there exist integer sequences (pₙ, qₙ) such that qₙ·α - pₙ tends to 0
    but is never 0, then α is irrational.

    Proof: If α = a/b ∈ ℚ (denominator b > 0), then
    qₙ·α - pₙ = (qₙ·a - pₙ·b)/b. The numerator is a nonzero integer,
    so |qₙ·α - pₙ| ≥ 1/b. But the sequence tends to 0 — contradiction. -/
theorem apery_criterion (α : ℝ) (p q : ℕ → ℤ)
    (happrox : Tendsto (fun n => (q n : ℝ) * α - (p n : ℝ)) atTop (nhds 0))
    (hnonzero : ∀ n, (q n : ℝ) * α - (p n : ℝ) ≠ 0) :
    Irrational α := by
  rintro ⟨r, rfl⟩
  -- r.den > 0
  have hd_pos : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  -- Lower bound: |q n * r - p n| ≥ 1/r.den for each n
  have hlb : ∀ n, 1 / (r.den : ℝ) ≤ |(q n : ℝ) * (r : ℝ) - (p n : ℝ)| := fun n => by
    -- Write r = num/den and collect into integer/den
    have hrw : (q n : ℝ) * (r : ℝ) - (p n : ℝ) =
        ((q n * r.num - p n * r.den : ℤ) : ℝ) / (r.den : ℝ) := by
      rw [Rat.cast_def]; push_cast; field_simp [hd_pos.ne']
    -- The integer numerator is nonzero (otherwise q n * r = p n, contradiction)
    have hnum_ne : (q n * r.num - p n * r.den : ℤ) ≠ 0 := by
      intro heq
      apply hnonzero n
      rw [hrw, show ((q n * r.num - p n * (r.den : ℤ) : ℤ) : ℝ) = 0 from by
        exact_mod_cast heq, zero_div]
    -- A nonzero integer has absolute value ≥ 1
    have hnum_abs : (1 : ℝ) ≤ |((q n * r.num - p n * r.den : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hnum_ne
    -- Therefore 1/den ≤ |num|/den
    rw [hrw, abs_div, abs_of_pos hd_pos]
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum_abs (inv_nonneg.mpr hd_pos.le)
  -- Contradiction: happrox gives arbitrarily small values but hlb gives lower bound 1/r.den
  have hpos : (0 : ℝ) < 1 / r.den := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp happrox _ hpos
  have hsmall := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at hsmall
  linarith [hlb N]

-- ============================================================
-- Part II: Abstract Apéry Witness
-- ============================================================

/-- **ApéryWitness**: The data needed to prove α irrational via Apéry's method.

    For ζ(3), Apéry (1978) found sequences satisfying the recurrence
      (n+1)³ uₙ₊₁ = (2n+1)(17n²+17n+5) uₙ - n³ uₙ₋₁
    with initial conditions producing qₙ·ζ(3) - pₙ with rate (1/√34)ⁿ.

    For ζ(5), no such sequences are known despite extensive computer searches. -/
structure AperyWitness (α : ℝ) where
  /-- Integer numerator sequence -/
  p : ℕ → ℤ
  /-- Integer denominator sequence -/
  q : ℕ → ℤ
  /-- The approximations qₙ·α - pₙ tend to 0 -/
  tendsto_zero : Tendsto (fun n => (q n : ℝ) * α - (p n : ℝ)) atTop (nhds 0)
  /-- The approximations never equal 0 exactly -/
  never_zero : ∀ n, (q n : ℝ) * α - (p n : ℝ) ≠ 0

/-- **Apéry Irrationality Theorem**: Any real number admitting an Apéry witness
    is irrational. This is the abstract template of Apéry's 1978 proof. -/
theorem apery_implies_irrational {α : ℝ} (w : AperyWitness α) : Irrational α :=
  apery_criterion α w.p w.q w.tendsto_zero w.never_zero

-- ============================================================
-- Part III: ζ(5) Definition and Conditional Theorem
-- ============================================================

/-- ζ(5) = ∑_{n=1}^∞ 1/n^5 ≈ 1.0369277551... -/
noncomputable def zetaFive : ℝ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ 5)

/-- **Main Conditional Theorem**: If an Apéry witness exists for ζ(5),
    then ζ(5) is irrational.

    This is the precise formalization of what "proving ζ(5) irrational via
    Apéry's method" means. The open problem is constructing such a witness. -/
theorem zetaFive_irrational_if_apery_witness (w : AperyWitness zetaFive) :
    Irrational zetaFive :=
  apery_implies_irrational w

-- ============================================================
-- Part IV: Geometric Decay — The Quantitative Condition
-- ============================================================

/-- **Geometric decay**: the sequence |f n| ≤ C · rⁿ for some rate r < 1.
    Apéry showed this for ζ(3) with r = (√2 - 1)⁴ ≈ 0.029 (rate 1/√34). -/
structure HasGeometricDecay (f : ℕ → ℝ) (r : ℝ) : Prop where
  rate_lt_one : r < 1
  const_bound : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |f n| ≤ C * r ^ n

/-- Geometric decay with r ∈ [0,1) implies convergence to 0. -/
theorem geometric_decay_tendsto {f : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r)
    (hdecay : HasGeometricDecay f r) :
    Tendsto f atTop (nhds 0) := by
  obtain ⟨hr1, C, _, hbound⟩ := hdecay
  have hpow : Tendsto (fun n : ℕ => C * r ^ n) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
    simp only [mul_zero] at h
    exact h
  apply squeeze_zero_norm _ hpow
  intro n
  rw [norm_eq_abs]
  exact hbound n

/-- **Strong Apéry Witness**: An Apéry witness with geometric decay rate.
    Constructing such a witness for ζ(5) is the central open problem. -/
structure StrongAperyWitness (α : ℝ) where
  /-- Integer numerator sequence -/
  p : ℕ → ℤ
  /-- Integer denominator sequence -/
  q : ℕ → ℤ
  /-- The approximation error never equals 0 -/
  never_zero : ∀ n, (q n : ℝ) * α - (p n : ℝ) ≠ 0
  /-- The decay rate r ∈ [0,1) -/
  rate : ℝ
  /-- Rate is nonneg (needed for convergence) -/
  rate_nonneg : 0 ≤ rate
  /-- The error decays geometrically -/
  error_decay : HasGeometricDecay (fun n => (q n : ℝ) * α - (p n : ℝ)) rate

/-- A StrongAperyWitness gives a standard AperyWitness
    (geometric decay implies convergence to 0). -/
def StrongAperyWitness.toAperyWitness (α : ℝ) (w : StrongAperyWitness α) :
    AperyWitness α where
  p := w.p
  q := w.q
  tendsto_zero := geometric_decay_tendsto w.rate_nonneg w.error_decay
  never_zero := w.never_zero

/-- **Strong Conditional Theorem**: A geometrically-decaying Apéry witness
    (quantitative form) also suffices to prove irrationality. -/
theorem zetaFive_irrational_if_strong_witness (w : StrongAperyWitness zetaFive) :
    Irrational zetaFive :=
  apery_implies_irrational (w.toAperyWitness zetaFive)

-- ============================================================
-- Part V: Apéry's ζ(3) Recurrence — The Template
-- ============================================================

/-- **Apéry's recurrence for ζ(3)**:
      (n+1)³ uₙ₊₁ = (2n+1)(17n²+17n+5) uₙ - n³ uₙ₋₁
    With initial conditions b₀ = 1, b₁ = 5 this produces the denominator sequence.
    With a₀ = 0, a₁ = 6 this produces the numerator sequence.
    Apéry proved bₙ·ζ(3) - aₙ → 0 at rate ~ (1/√34)ⁿ, proving ζ(3) irrational. -/
def SatisfiesApery_ζ3_Recurrence (u : ℤ → ℤ) : Prop :=
  ∀ n : ℕ, (n + 1 : ℤ) ^ 3 * u (n + 1) =
    (2 * ↑n + 1) * (17 * ↑n ^ 2 + 17 * ↑n + 5) * u n - (n : ℤ) ^ 3 * u (n - 1)

/-- For ζ(5), the analogous question is whether a recurrence like
      P(n) uₙ₊₁ = Q(n) uₙ - R(n) uₙ₋₁
    with polynomial P, Q, R exists producing sequences bₙ, aₙ with
    bₙ·ζ(5) - aₙ → 0 geometrically.

    Computer searches (Zagier et al.) up to order ~ 10³ have found no such recurrence.
    The obstruction: ζ(5) likely requires higher-dimensional Padé approximants. -/
def IsAperyTypeRecurrence (P Q R : ℤ → ℤ) (u : ℤ → ℤ) : Prop :=
  ∀ n : ℕ, P n * u (n + 1) = Q n * u n - R n * u (n - 1)

/-- The open problem: does there exist a polynomial recurrence producing
    a StrongAperyWitness for ζ(5)?
    Formalizing a NEGATIVE answer (impossibility) would be groundbreaking. -/
def OpenProblem_ζ5_Apery : Prop :=
  ∃ _ : StrongAperyWitness zetaFive, True

end BaselProblemOQ01OQ03
