/-
# Erdős Problem #510 (Chowla's Cosine Problem) — Foundational Lemmas

Axiom-free foundational scaffolding for the cosine sum

    cosineSum A θ = ∑_{n ∈ A} cos(n·θ),     minCosineSum A = ⨅_θ cosineSum A θ,

as defined in `Proofs/Erdos510Problem.lean`.

Chowla's cosine problem asks whether there is an absolute constant `c > 0` such
that every finite `A ⊂ ℕ⁺` of size `N` admits an angle `θ` with
`cosineSum A θ < −c√N`.  The deep quantitative bounds (Bourgain, Ruzsa, Bedert)
remain open/hard, but the *elementary structure* of the cosine sum and its
infimum is fully provable from Mathlib.  This file establishes:

* evaluation lemmas: on the empty set, singletons, `insert`, at `θ = 0` and
  `θ = π`;
* the trivial two-sided bound `|cosineSum A θ| ≤ N` (so the sum lives in
  `[−N, N]`);
* evenness `cosineSum A (−θ) = cosineSum A θ` and `2π`-periodicity;
* continuity of `θ ↦ cosineSum A θ`;
* boundedness-below of the range, hence the basic `minCosineSum` bounds
  `−N ≤ minCosineSum A ≤ N` and `minCosineSum A ≤ cosineSum A θ`;
* the exact value `minCosineSum {n} = −1` for `n ≥ 1`;
* the alternating-sum bound `minCosineSum A ≤ ∑_{n ∈ A} (−1)ⁿ` (evaluation at
  `θ = π`), and the **sharp** all-odd case `minCosineSum A = −A.card` when every
  `n ∈ A` is odd — an explicit infinite family attaining the extreme `−N`;
* **Chowla's `√N` bound for sum-free sets**: the third moment
  `∫₀^{2π} (cosineSum A)³` vanishes when `A` is sum-free (triple-product
  orthogonality), and a moment bootstrap then gives
  `minCosineSum A ≤ −√(N/2)` — the conjectured `√N` growth rate with explicit
  constant `1/√2`, on the sum-free subclass;
* **linear growth for the interval family**: the Dirichlet-kernel telescoping
  identity `2 sin(θ/2)·∑_{n=1}^N cos(nθ) = sin((2N+1)θ/2) − sin(θ/2)`, and its
  evaluation at `θ₀ = 3π/(2N+1)` (the middle of the kernel's first negative
  lobe), giving `minCosineSum {1,…,N} ≤ −1/2 − (2N+1)/(3π)` — the maximally
  additively-structured set sits at the opposite extreme (`≍ −N`) from the
  conjectured general `−c√N`;
* **the L¹–L⁴ analytic engine for the Sidon route**: Cauchy–Schwarz for
  interval integrals (`sq_integral_mul_le`, via `discrim_le_zero`), the L¹
  bound `∫|f| ≤ 4π·(−minCosineSum)` (`integral_abs_cosineSum_le`, from
  `∫f = 0`), the moment chain `(πN)³ ≤ (∫f⁴)·(∫|f|)²`
  (`pow_three_second_moment_le`, Cauchy–Schwarz twice through `∫|f|³`), and
  their combination `minCosineSum_le_neg_sqrt_of_fourth_moment`: any
  fourth-moment bound `∫f⁴ ≤ B` yields
  `minCosineSum A ≤ −√(π³N³/B)/(4π)`.  The remaining *combinatorial* step —
  the Sidon (`B₂[1]`) quadruple count `∫f⁴ = O(N²)` — will instantiate `B`
  and give Chowla's `−c√N` on the Sidon class.

All results are `0`-axiom / `0`-sorry.  The genuinely open content — the
`−c√N` lower bound for *general* sets (those with additive structure, where
the third moment is large) — is untouched (it is the mission, not the
scaffolding).

Reference: <https://erdosproblems.com/510>
-/

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Proofs.Erdos510Problem

open Finset Real

namespace Erdos510WIP01

variable (A : Finset ℕ) (θ : ℝ)

/-! ## Evaluation lemmas -/

/-- The cosine sum of the empty set is `0`. -/
theorem cosineSum_empty : cosineSum ∅ θ = 0 := by
  simp [cosineSum]

/-- The cosine sum of a singleton is a single cosine. -/
theorem cosineSum_singleton (n : ℕ) : cosineSum {n} θ = Real.cos (n * θ) := by
  simp [cosineSum]

/-- Adding a fresh frequency `n ∉ A` adds one cosine term. -/
theorem cosineSum_insert {n : ℕ} {A : Finset ℕ} (h : n ∉ A) :
    cosineSum (insert n A) θ = Real.cos (n * θ) + cosineSum A θ := by
  simp [cosineSum, Finset.sum_insert h]

/-- At `θ = 0` every term is `cos 0 = 1`, so the sum is the cardinality `N`. -/
theorem cosineSum_zero_angle : cosineSum A 0 = A.card := by
  simp [cosineSum]

/-- At `θ = π` the sum collapses to an alternating sum `∑ (−1)ⁿ`. -/
theorem cosineSum_pi : cosineSum A π = ∑ n ∈ A, (-1 : ℝ) ^ n := by
  simp only [cosineSum]
  exact Finset.sum_congr rfl (fun n _ => Real.cos_nat_mul_pi n)

/-! ## Symmetry and periodicity -/

/-- The cosine sum is even in the angle: `cosineSum A (−θ) = cosineSum A θ`. -/
theorem cosineSum_neg : cosineSum A (-θ) = cosineSum A θ := by
  simp only [cosineSum, mul_neg, Real.cos_neg]

/-- The cosine sum is `2π`-periodic in the angle. -/
theorem cosineSum_add_two_pi : cosineSum A (θ + 2 * π) = cosineSum A θ := by
  simp only [cosineSum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [show (n : ℝ) * (θ + 2 * π) = n * θ + n * (2 * π) from by ring,
    Real.cos_add_nat_mul_two_pi]

/-! ## Trivial two-sided bound -/

/-- Triangle inequality plus `|cos| ≤ 1`: the cosine sum is bounded by `N`. -/
theorem abs_cosineSum_le_card : |cosineSum A θ| ≤ A.card := by
  simp only [cosineSum]
  calc |∑ n ∈ A, Real.cos (n * θ)| ≤ ∑ n ∈ A, |Real.cos (n * θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ A, (1 : ℝ) := Finset.sum_le_sum
        (fun n _ => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    _ = A.card := by simp

/-- Upper bound `cosineSum A θ ≤ N`. -/
theorem cosineSum_le_card : cosineSum A θ ≤ A.card :=
  (le_abs_self _).trans (abs_cosineSum_le_card A θ)

/-- Lower bound `−N ≤ cosineSum A θ`. -/
theorem neg_card_le_cosineSum : -(A.card : ℝ) ≤ cosineSum A θ :=
  (abs_le.mp (abs_cosineSum_le_card A θ)).1

/-! ## Continuity -/

/-- `θ ↦ cosineSum A θ` is continuous (a finite sum of continuous cosines). -/
theorem continuous_cosineSum : Continuous (cosineSum A) := by
  show Continuous (fun θ => ∑ n ∈ A, Real.cos (n * θ))
  exact continuous_finsetSum _
    (fun n _ => Real.continuous_cos.comp (continuous_const.mul continuous_id))

/-! ## The infimum `minCosineSum` -/

/-- The range of `cosineSum A` is bounded below (by `−N`). -/
theorem bddBelow_range_cosineSum : BddBelow (Set.range (cosineSum A)) := by
  refine ⟨-(A.card : ℝ), ?_⟩
  rintro x ⟨θ, rfl⟩
  exact neg_card_le_cosineSum A θ

/-- `minCosineSum A` is a lower bound for every cosine sum value. -/
theorem minCosineSum_le : minCosineSum A ≤ cosineSum A θ :=
  ciInf_le (bddBelow_range_cosineSum A) θ

/-- `−N` bounds `minCosineSum A` from below. -/
theorem neg_card_le_minCosineSum : -(A.card : ℝ) ≤ minCosineSum A :=
  le_ciInf (fun θ => neg_card_le_cosineSum A θ)

/-- `minCosineSum A ≤ N` (via the value at `θ = 0`). -/
theorem minCosineSum_le_card : minCosineSum A ≤ A.card :=
  (minCosineSum_le A 0).trans_eq (cosineSum_zero_angle A)

/-- The minimum cosine sum of the empty set is `0`. -/
theorem minCosineSum_empty : minCosineSum ∅ = 0 := by
  have h : cosineSum ∅ = fun _ : ℝ => (0 : ℝ) := funext (fun θ => cosineSum_empty θ)
  simp only [minCosineSum, h]
  exact ciInf_const

/-- Exact value for a single positive frequency: `minCosineSum {n} = −1`
    for `n ≥ 1`.  The bound `−1 ≤ cos` gives `≥ −1`; the angle `θ = π/n`
    (where `cos(n·θ) = cos π = −1`) gives `≤ −1`. -/
theorem minCosineSum_singleton {n : ℕ} (hn : 1 ≤ n) : minCosineSum {n} = -1 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hval : cosineSum {n} (π / n) = -1 := by
    rw [cosineSum_singleton]
    have hπ : (n : ℝ) * (π / n) = π := by field_simp
    rw [hπ, Real.cos_pi]
  apply le_antisymm
  · exact (minCosineSum_le {n} (π / n)).trans_eq hval
  · exact le_ciInf (fun θ => by rw [cosineSum_singleton]; exact Real.neg_one_le_cos _)

/-! ## The infimum is attained -/

/-- **The minimum cosine sum is attained.**  `cosineSum A` is continuous and
`2π`-periodic, so its infimum over all of `ℝ` equals its minimum over the compact
interval `[0, 2π]`, and is realised at some concrete angle `θ₀`.  This upgrades
`minCosineSum` from an `iInf` to an attained minimum — the structural
prerequisite for locating the extremal angle in the Chowla problem. -/
theorem exists_eq_minCosineSum (A : Finset ℕ) :
    ∃ θ₀ : ℝ, cosineSum A θ₀ = minCosineSum A := by
  have hper : Function.Periodic (cosineSum A) (2 * π) := fun θ => cosineSum_add_two_pi A θ
  have himg : cosineSum A '' Set.Icc 0 (0 + 2 * π) = Set.range (cosineSum A) :=
    hper.image_Icc Real.two_pi_pos 0
  have hne : (Set.Icc (0 : ℝ) (0 + 2 * π)).Nonempty :=
    ⟨0, Set.left_mem_Icc.mpr (by have := Real.two_pi_pos; linarith)⟩
  obtain ⟨θ₀, _, hmin⟩ :=
    isCompact_Icc.exists_isMinOn hne (continuous_cosineSum A).continuousOn
  refine ⟨θ₀, le_antisymm ?_ (minCosineSum_le A θ₀)⟩
  -- `cosineSum A θ₀` is a lower bound of the whole range, hence `≤` the infimum
  refine le_ciInf (fun θ => ?_)
  have hmem : cosineSum A θ ∈ Set.range (cosineSum A) := ⟨θ, rfl⟩
  rw [← himg] at hmem
  obtain ⟨y, hy, hyeq⟩ := hmem
  rw [← hyeq]
  exact isMinOn_iff.mp hmin y hy

/-! ## The minimum is nonpositive for positive-frequency sets

For a set `A` of *positive* frequencies (`0 ∉ A`), each term `cos(nθ)` integrates to `0`
over a full period, so `∫₀^{2π} cosineSum A = 0`. Since `minCosineSum A` is a pointwise
lower bound, integrating the constant gives `2π · minCosineSum A ≤ 0`, whence
`minCosineSum A ≤ 0`. This is the elementary sign fact behind the Chowla problem: a
positive-frequency cosine sum must dip to `0` or below somewhere. -/

/-- A single positive-frequency cosine integrates to zero over a full period. -/
theorem integral_cos_mul_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    ∫ θ in (0 : ℝ)..(2 * π), Real.cos ((n : ℝ) * θ) = 0 := by
  have hcn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [intervalIntegral.integral_comp_mul_left (f := fun x => Real.cos x) hcn, integral_cos]
  have h1 : Real.sin ((n : ℝ) * (2 * π)) = 0 := by
    rw [show (n : ℝ) * (2 * π) = ((2 * n : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi (2 * n)
  rw [mul_zero, h1, Real.sin_zero, sub_zero, smul_zero]

/-- `∫₀^{2π} cosineSum A = 0` for a positive-frequency set (`0 ∉ A`). -/
theorem integral_cosineSum_eq_zero (A : Finset ℕ) (hA : 0 ∉ A) :
    ∫ θ in (0 : ℝ)..(2 * π), cosineSum A θ = 0 := by
  simp only [cosineSum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_eq_zero (fun n hn => ?_)
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => hA (h ▸ hn))
    exact integral_cos_mul_eq_zero hn1
  · intro n _
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- **The Chowla cosine sum is nonpositive at its minimum for positive frequencies.**
If `0 ∉ A` then `minCosineSum A ≤ 0`: since `∫₀^{2π} cosineSum A = 0` and
`minCosineSum A ≤ cosineSum A θ` pointwise, the constant `minCosineSum A` integrates to
`2π · minCosineSum A ≤ 0`. -/
theorem minCosineSum_nonpos (A : Finset ℕ) (hA : 0 ∉ A) : minCosineSum A ≤ 0 := by
  have hint : ∫ θ in (0 : ℝ)..(2 * π), cosineSum A θ = 0 := integral_cosineSum_eq_zero A hA
  have hmono := intervalIntegral.integral_mono_on
    (a := (0 : ℝ)) (b := 2 * π) (μ := MeasureTheory.volume)
    (f := fun _ => minCosineSum A) (g := cosineSum A)
    Real.two_pi_pos.le intervalIntegrable_const
    ((continuous_cosineSum A).intervalIntegrable _ _)
    (fun θ _ => minCosineSum_le A θ)
  rw [intervalIntegral.integral_const, hint] at hmono
  simp only [smul_eq_mul, sub_zero] at hmono
  nlinarith [Real.two_pi_pos]

/-! ## The minimum is *strictly* negative for nonempty positive-frequency sets

The nonpositivity bound above is not tight: for a *nonempty* positive-frequency set the
minimum is strictly below `0`.  The point is that `cosineSum A` cannot be `≡ 0`: it takes
the value `N = A.card ≥ 1` at `θ = 0`.  If its minimum were `0` the (continuous, nonnegative)
integrand would still have integral `0` over a full period, yet it is *strictly* positive on
a whole subinterval near `0` — forcing the period integral to be positive, a contradiction.
So the minimum must be `< 0`, i.e. every nonempty positive-frequency cosine sum genuinely
dips below zero somewhere. -/

/-- **The Chowla cosine sum is strictly negative at its minimum** for a nonempty
positive-frequency set.  If `0 ∉ A` and `A ≠ ∅` then `minCosineSum A < 0`.  Combined with
`∫₀^{2π} cosineSum A = 0`: were the minimum `0`, the nonnegative integrand would be strictly
positive on a subinterval about `θ = 0` (where `cosineSum A 0 = A.card ≥ 1`), making the
period integral positive — impossible. This strengthens `minCosineSum_nonpos` and is the
qualitative core of the Chowla problem (the quantitative `−c√N` bound stays deep). -/
theorem minCosineSum_neg (A : Finset ℕ) (hA : 0 ∉ A) (hne : A.Nonempty) :
    minCosineSum A < 0 := by
  rcases (minCosineSum_nonpos A hA).lt_or_eq with h | h
  · exact h
  exfalso
  -- If the minimum is `0`, the sum is pointwise `≥ 0`.
  have hnn : ∀ θ, 0 ≤ cosineSum A θ := fun θ => h ▸ minCosineSum_le A θ
  -- The sum is strictly positive at `θ = 0` (value `A.card ≥ 1`).
  have hc0 : 0 < cosineSum A 0 := by
    rw [cosineSum_zero_angle]; exact_mod_cast Finset.card_pos.mpr hne
  -- `{θ | 0 < cosineSum A θ}` is open and contains `0`, so it holds on a ball `(−ε, ε)`.
  have hopen : IsOpen {θ : ℝ | 0 < cosineSum A θ} :=
    isOpen_lt continuous_const (continuous_cosineSum A)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hc0
  -- Work on the interval `[δ/2, δ]` with `δ = min ε π`, safely inside `(0, 2π)`.
  set δ := min ε π with hδ
  have hδpos : 0 < δ := lt_min hε Real.pi_pos
  have hδle : δ ≤ π := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hcd : ∀ x ∈ Set.Ioo (δ / 2) δ, 0 < cosineSum A x := by
    intro x hx
    apply hball
    rw [Real.ball_eq_Ioo]
    exact ⟨by simp only [zero_sub]; linarith [hx.1], by simpa using lt_of_lt_of_le hx.2 hδε⟩
  -- Strict positivity of the middle integral, nonnegativity of the two outer ones.
  have hpos : 0 < ∫ x in (δ / 2)..δ, cosineSum A x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_cosineSum A).intervalIntegrable _ _) hcd (by linarith)
  have hn1 : 0 ≤ ∫ x in (0 : ℝ)..(δ / 2), cosineSum A x :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => hnn u)
  have hn3 : 0 ≤ ∫ x in δ..(2 * π), cosineSum A x :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun u _ => hnn u)
  -- Split `∫₀^{2π} = ∫₀^{δ/2} + ∫_{δ/2}^{δ} + ∫_δ^{2π}`, which is then `> 0`.
  have i1 : IntervalIntegrable (cosineSum A) MeasureTheory.volume 0 (δ / 2) :=
    (continuous_cosineSum A).intervalIntegrable _ _
  have i2 : IntervalIntegrable (cosineSum A) MeasureTheory.volume (δ / 2) δ :=
    (continuous_cosineSum A).intervalIntegrable _ _
  have i3 : IntervalIntegrable (cosineSum A) MeasureTheory.volume δ (2 * π) :=
    (continuous_cosineSum A).intervalIntegrable _ _
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals i1 i2
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3
  have hint : ∫ θ in (0 : ℝ)..(2 * π), cosineSum A θ = 0 := integral_cosineSum_eq_zero A hA
  linarith [hadd1, hadd2, hpos, hn1, hn3, hint]

/-- **Every nonempty positive-frequency cosine sum dips below zero.**  There is an angle
`θ` with `cosineSum A θ < 0`.  Immediate from `minCosineSum_neg` and the attainment of the
minimum (`exists_eq_minCosineSum`): the minimizing angle already realises a negative value. -/
theorem exists_angle_cosineSum_neg (A : Finset ℕ) (hA : 0 ∉ A) (hne : A.Nonempty) :
    ∃ θ : ℝ, cosineSum A θ < 0 := by
  obtain ⟨θ₀, hθ₀⟩ := exists_eq_minCosineSum A
  exact ⟨θ₀, hθ₀.trans_lt (minCosineSum_neg A hA hne)⟩

/-! ## A quantitative uniform bound: `minCosineSum A ≤ −1/2`

The strict bound `minCosineSum A < 0` above is qualitative.  A **second-moment / L²
averaging** argument upgrades it to a *uniform quantitative constant*: every nonempty
positive-frequency set satisfies `minCosineSum A ≤ −1/2`.  The mechanism is orthogonality
of the characters `cos(nθ)` over a full period:

* first moment  `∫₀^{2π} cosineSum A = 0`                    (`integral_cosineSum_eq_zero`);
* second moment `∫₀^{2π} (cosineSum A)² = π · N`             (`integral_cosineSum_sq`).

Writing `f = cosineSum A`, `m = minCosineSum A`, `N = |A|`, the sum obeys the pointwise
sandwich `m ≤ f ≤ N`, so `(f − m)(N − f) ≥ 0` pointwise and its period integral is
nonnegative.  Expanding, `∫(f − m)(N − f) = −πN − 2πmN ≥ 0`, and dividing by `2πN > 0`
gives `m ≤ −1/2`.  This is a *fixed constant* — it does **not** grow like `√N` — so it is a
genuinely different (and unblocked) result from the deep `−c√N` lower bound, which stays
open. -/

/-- A single nonzero-integer-frequency cosine integrates to zero over a full period.  The
`ℤ`-frequency generalisation of `integral_cos_mul_eq_zero`, needed for the orthogonality
relation where the difference frequency `n − m` can be negative. -/
theorem integral_cos_int_mul_eq_zero (k : ℤ) (hk : k ≠ 0) :
    ∫ θ in (0 : ℝ)..(2 * π), Real.cos ((k : ℝ) * θ) = 0 := by
  have hck : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  rw [intervalIntegral.integral_comp_mul_left (f := fun x => Real.cos x) hck, integral_cos]
  have h1 : Real.sin ((k : ℝ) * (2 * π)) = 0 := by
    rw [show (k : ℝ) * (2 * π) = ((2 * k : ℤ) : ℝ) * π by push_cast; ring]
    exact Real.sin_int_mul_pi (2 * k)
  rw [mul_zero, h1, Real.sin_zero, sub_zero, smul_zero]

/-- **Orthogonality of the cosine characters over a full period.**  For positive
frequencies `n, m ≥ 1`,
  `∫₀^{2π} cos(nθ)·cos(mθ) dθ = π` if `n = m` and `0` otherwise.
Proof by the product-to-sum identity `cos(nθ)cos(mθ) = ½(cos((n+m)θ) + cos((n−m)θ))`: the
`(n+m)`-term always integrates to `0` (positive frequency), while the `(n−m)`-term is
`cos 0 = 1` (integral `2π`) exactly when `n = m` and integrates to `0` otherwise. -/
theorem integral_cos_mul_cos {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∫ θ in (0 : ℝ)..(2 * π), Real.cos ((n : ℝ) * θ) * Real.cos ((m : ℝ) * θ))
      = if n = m then π else 0 := by
  -- product-to-sum, as a function equality (avoids `integral_congr`/`integral_div` whnf blowup)
  have hfun : (fun θ : ℝ => Real.cos ((n : ℝ) * θ) * Real.cos ((m : ℝ) * θ))
      = fun θ => (1 / 2) * Real.cos (((n : ℝ) + (m : ℝ)) * θ)
                 + (1 / 2) * Real.cos (((n : ℝ) - (m : ℝ)) * θ) := by
    funext θ
    have e1 : ((n : ℝ) + (m : ℝ)) * θ = (n : ℝ) * θ + (m : ℝ) * θ := by ring
    have e2 : ((n : ℝ) - (m : ℝ)) * θ = (n : ℝ) * θ - (m : ℝ) * θ := by ring
    rw [e1, e2, Real.cos_add, Real.cos_sub]; ring
  have hI1 : IntervalIntegrable (fun θ => (1 / 2) * Real.cos (((n : ℝ) + (m : ℝ)) * θ))
      MeasureTheory.volume 0 (2 * π) :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul _).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun θ => (1 / 2) * Real.cos (((n : ℝ) - (m : ℝ)) * θ))
      MeasureTheory.volume 0 (2 * π) :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul _).intervalIntegrable _ _
  have hsum : (∫ θ in (0 : ℝ)..(2 * π), Real.cos (((n : ℝ) + (m : ℝ)) * θ)) = 0 := by
    rw [show ((n : ℝ) + (m : ℝ)) = ((n + m : ℕ) : ℝ) by push_cast; ring]
    exact integral_cos_mul_eq_zero (by omega)
  have hdiff : (∫ θ in (0 : ℝ)..(2 * π), Real.cos (((n : ℝ) - (m : ℝ)) * θ))
      = if n = m then 2 * π else 0 := by
    by_cases hnm : n = m
    · rw [if_pos hnm]
      have h0 : (n : ℝ) - (m : ℝ) = 0 := by rw [hnm]; ring
      simp only [h0, zero_mul, Real.cos_zero]
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    · rw [if_neg hnm]
      have hk : ((n : ℤ) - (m : ℤ)) ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hnm
      have h := integral_cos_int_mul_eq_zero ((n : ℤ) - (m : ℤ)) hk
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at h
      exact h
  rw [hfun, intervalIntegral.integral_add hI1 hI2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsum, hdiff]
  by_cases hnm : n = m
  · rw [if_pos hnm, if_pos hnm]; ring
  · rw [if_neg hnm, if_neg hnm]; ring

/-- **The second moment of the Chowla cosine sum: `∫₀^{2π} (cosineSum A)² = π · |A|`.**
Expand the square as the double sum `∑_{n,m} cos(nθ)cos(mθ)`, integrate term by term, and
apply orthogonality (`integral_cos_mul_cos`): only the diagonal `n = m` survives, each
contributing `π`, for a total of `π · |A|`.  (Requires `0 ∉ A` so every frequency is
`≥ 1`.) -/
theorem integral_cosineSum_sq (A : Finset ℕ) (hA : 0 ∉ A) :
    ∫ θ in (0 : ℝ)..(2 * π), (cosineSum A θ) ^ 2 = π * A.card := by
  have hexp : ∀ θ : ℝ, (cosineSum A θ) ^ 2
      = ∑ n ∈ A, ∑ m ∈ A, Real.cos ((n : ℝ) * θ) * Real.cos ((m : ℝ) * θ) := by
    intro θ
    rw [sq]
    simp only [cosineSum]
    rw [Finset.sum_mul_sum]
  have hcont : ∀ n : ℕ, Continuous (fun θ : ℝ => Real.cos ((n : ℝ) * θ)) :=
    fun n => Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hintprod : ∀ n m : ℕ, IntervalIntegrable
      (fun θ => Real.cos ((n : ℝ) * θ) * Real.cos ((m : ℝ) * θ)) MeasureTheory.volume 0 (2 * π) :=
    fun n m => ((hcont n).mul (hcont m)).intervalIntegrable _ _
  have hintinner : ∀ n : ℕ, IntervalIntegrable
      (fun θ => ∑ m ∈ A, Real.cos ((n : ℝ) * θ) * Real.cos ((m : ℝ) * θ))
      MeasureTheory.volume 0 (2 * π) :=
    fun n => (continuous_finsetSum A (fun m _ => (hcont n).mul (hcont m))).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun θ _ => hexp θ),
      intervalIntegral.integral_finsetSum (fun n _ => hintinner n)]
  have hstep : ∀ n ∈ A,
      (∫ θ in (0 : ℝ)..(2 * π), ∑ m ∈ A, Real.cos ((n : ℝ) * θ) * Real.cos ((m : ℝ) * θ))
        = ∑ m ∈ A, if n = m then π else (0 : ℝ) := by
    intro n hn
    rw [intervalIntegral.integral_finsetSum (fun m _ => hintprod n m)]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    exact integral_cos_mul_cos (Nat.one_le_iff_ne_zero.mpr (fun h => hA (h ▸ hn)))
      (Nat.one_le_iff_ne_zero.mpr (fun h => hA (h ▸ hm)))
  rw [Finset.sum_congr rfl hstep]
  have hdiag : ∀ n ∈ A, (∑ m ∈ A, if n = m then π else (0 : ℝ)) = π := by
    intro n hn
    rw [Finset.sum_ite_eq A n (fun _ => (π : ℝ)), if_pos hn]
  rw [Finset.sum_congr rfl hdiag, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Uniform quantitative bound: `minCosineSum A ≤ −1/2`** for every nonempty
positive-frequency set.  Second-moment argument: with `f = cosineSum A`, `m = minCosineSum A`,
`N = |A|`, the first and second moments are `∫f = 0` and `∫f² = πN`, and `m ≤ f ≤ N`
pointwise.  Hence `∫(f − m)(N − f) ≥ 0`; expanding gives `−πN − 2πmN ≥ 0`, so `m ≤ −1/2`.
A fixed constant (not the deep `−c√N` growth), and strictly sharper than `minCosineSum_neg`. -/
theorem minCosineSum_le_neg_half (A : Finset ℕ) (hA : 0 ∉ A) (hne : A.Nonempty) :
    minCosineSum A ≤ -1 / 2 := by
  set g := cosineSum A with hg
  set m := minCosineSum A with hm
  set N : ℝ := (A.card : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Finset.card_pos.mpr hne
  have I1 : ∫ θ in (0 : ℝ)..(2 * π), g θ = 0 := integral_cosineSum_eq_zero A hA
  have I2 : ∫ θ in (0 : ℝ)..(2 * π), (g θ) ^ 2 = π * N := integral_cosineSum_sq A hA
  have hlow : ∀ θ, m ≤ g θ := fun θ => minCosineSum_le A θ
  have hupp : ∀ θ, g θ ≤ N := fun θ => cosineSum_le_card A θ
  have hg_int : IntervalIntegrable g MeasureTheory.volume 0 (2 * π) :=
    (continuous_cosineSum A).intervalIntegrable _ _
  have hg2_int : IntervalIntegrable (fun θ => (g θ) ^ 2) MeasureTheory.volume 0 (2 * π) :=
    ((continuous_cosineSum A).pow 2).intervalIntegrable _ _
  -- The nonnegative integrand `(f − m)(N − f)`.
  have hnonneg : 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), (g θ - m) * (N - g θ) := by
    apply intervalIntegral.integral_nonneg (by positivity)
    intro θ _
    exact mul_nonneg (by linarith [hlow θ]) (by linarith [hupp θ])
  -- Evaluate that integral in closed form.
  have hneg2 : IntervalIntegrable (fun θ => -(g θ) ^ 2) MeasureTheory.volume 0 (2 * π) :=
    hg2_int.neg
  have hcm : IntervalIntegrable (fun θ => (N + m) * g θ) MeasureTheory.volume 0 (2 * π) :=
    hg_int.const_mul _
  have hA1 : IntervalIntegrable (fun θ => -(g θ) ^ 2 + (N + m) * g θ)
      MeasureTheory.volume 0 (2 * π) := hneg2.add hcm
  have hcompute : (∫ θ in (0 : ℝ)..(2 * π), (g θ - m) * (N - g θ)) = -(π * N) - 2 * π * m * N := by
    rw [intervalIntegral.integral_congr
          (fun θ _ => show (g θ - m) * (N - g θ) = -(g θ) ^ 2 + (N + m) * g θ - m * N by ring),
        intervalIntegral.integral_sub hA1 intervalIntegrable_const,
        intervalIntegral.integral_add hneg2 hcm,
        intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, I1, I2]
    simp only [smul_eq_mul]; ring
  rw [hcompute] at hnonneg
  have hpi : 0 < π := Real.pi_pos
  nlinarith [hnonneg, mul_pos hpi hNpos]

/-! ## Evaluation at `θ = π`: the alternating-sum bound and the all-odd sharp case -/

/-- **The minimum is bounded by the alternating sum.**  Evaluating at `θ = π`
(`cosineSum_pi`) and using that `minCosineSum` is a pointwise lower bound gives
`minCosineSum A ≤ ∑_{n ∈ A} (−1)ⁿ = #{even ∈ A} − #{odd ∈ A}` — a computable upper bound on the
Chowla minimum for any frequency set, negative exactly when `A` has more odd than even
elements. -/
theorem minCosineSum_le_alternating (A : Finset ℕ) :
    minCosineSum A ≤ ∑ n ∈ A, (-1 : ℝ) ^ n := by
  have h := minCosineSum_le A π
  rwa [cosineSum_pi] at h

/-- **Sharp minimum for all-odd frequency sets.**  If every element of `A` is odd then each
`cos(nπ) = −1`, so `cosineSum A π = −N`, which already meets the global lower bound
`−N ≤ minCosineSum A`.  Hence `minCosineSum A = −A.card`: the all-odd sets are an explicit
infinite family whose Chowla cosine sum attains the extreme value `−N` (far beyond the
conjectured `−c√N`, but exactly), sharpening the singleton case `minCosineSum {n} = −1`. -/
theorem minCosineSum_forall_odd (A : Finset ℕ) (hodd : ∀ n ∈ A, Odd n) :
    minCosineSum A = -A.card := by
  refine le_antisymm ?_ (neg_card_le_minCosineSum A)
  have hsum : (∑ n ∈ A, (-1 : ℝ) ^ n) = -A.card := by
    have hterm : ∀ n ∈ A, (-1 : ℝ) ^ n = -1 := fun n hn => (hodd n hn).neg_one_pow
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_neg_one]
  have h := minCosineSum_le_alternating A
  rwa [hsum] at h

/-! ## Dilation invariance: reduction to primitive frequency sets

Scaling every frequency by a common factor `d ≥ 1` (`A ↦ d·A := A.image (d · ·)`)
leaves the whole Chowla cosine minimum unchanged: dilating the frequencies merely
rescales the angle (`θ ↦ d·θ`), and since `θ` ranges over all of `ℝ` this is a
bijective reparametrisation of the range.  This is the standard structural reduction
that lets one assume `gcd A = 1` (a *primitive* set) when studying `minCosineSum`. -/

/-- **Dilation rescales the angle.**  For a scaling factor `d ≠ 0`, the cosine sum of
the dilated set `d·A = A.image (d · ·)` at angle `θ` equals the cosine sum of `A` at
the scaled angle `d·θ`:  `∑_{n∈A} cos((d n) θ) = ∑_{n∈A} cos(n (d θ))`. -/
theorem cosineSum_dilate {d : ℕ} (hd : d ≠ 0) :
    cosineSum (A.image (fun n => d * n)) θ = cosineSum A ((d : ℝ) * θ) := by
  unfold cosineSum
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl (fun n _ => ?_)
    congr 1
    push_cast
    ring
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) hab

/-- **The Chowla cosine minimum is dilation-invariant.**  For any scaling factor
`d ≥ 1`, `minCosineSum (d·A) = minCosineSum A`.  The range of `cosineSum (d·A)` equals
the range of `cosineSum A` (the map `θ ↦ d·θ` is a surjection of `ℝ` onto itself when
`d ≠ 0`), so the two infima coincide.  Consequently every frequency set has the same
minimum as its primitive core `A / gcd A`, reducing the general problem to primitive
sets. -/
theorem minCosineSum_dilate {d : ℕ} (hd : d ≠ 0) :
    minCosineSum (A.image (fun n => d * n)) = minCosineSum A := by
  have hrange : Set.range (cosineSum (A.image (fun n => d * n)))
      = Set.range (cosineSum A) := by
    ext y
    simp only [Set.mem_range]
    constructor
    · rintro ⟨θ, rfl⟩
      exact ⟨(d : ℝ) * θ, (cosineSum_dilate A θ hd).symm⟩
    · rintro ⟨φ, rfl⟩
      refine ⟨φ / d, ?_⟩
      rw [cosineSum_dilate A (φ / d) hd]
      congr 1
      field_simp
  show sInf (Set.range (cosineSum (A.image (fun n => d * n))))
      = sInf (Set.range (cosineSum A))
  rw [hrange]

/-! ## The third moment and Chowla's `√N` bound for sum-free sets

For a **sum-free** frequency set (`a, b ∈ A → a + b ∉ A`), the third moment
`∫₀^{2π} (cosineSum A)³` vanishes: expanding the cube, each triple product
`cos(aθ)cos(bθ)cos(cθ)` splits into four cosines at the signed frequencies
`±a±b±c`, and sum-freeness makes every one of them nonzero, so each integrates
to `0` over a period.  Combining the three moments `∫f = 0`, `∫f² = πN`,
`∫f³ = 0` with the pointwise bound `f ≥ m := minCosineSum A` via the
Cauchy–Schwarz-type inequality `∫ (f−m)·((−2m)(f−m) − (N+2m²))² ≥ 0`
(the nonnegative integrand `u·(αu−β)²` with the optimal linear factor, scaled
to clear denominators) yields `m² ≥ N/2`, i.e.

    `minCosineSum A ≤ −√(N/2)`.

This is the conjectured `−c√N` **growth rate** of Chowla's problem (with the
explicit constant `c = 1/√2`), established here for the *sum-free subclass* —
e.g. every "top half" interval `{N+1, …, 2N}`.  The general conjecture is NOT
touched: sets with additive structure (where the third moment is large and
positive) are exactly the hard case, and remain the open mission. -/

/-- **Triple-product orthogonality.**  If none of the three additive relations
`a + b = c`, `a + c = b`, `b + c = a` holds, the triple product
`cos(aθ)cos(bθ)cos(cθ)` integrates to `0` over a full period: product-to-sum
splits it into four cosines at the signed integer frequencies `a+b+c`, `a+b−c`,
`a−b+c`, `a−b−c`, each nonzero under the hypotheses (the first is zero only if
`a = b = c = 0`, which already violates `a + b ≠ c`). -/
theorem integral_cos_mul_cos_mul_cos_eq_zero {a b c : ℕ}
    (h1 : a + b ≠ c) (h2 : a + c ≠ b) (h3 : b + c ≠ a) :
    (∫ θ in (0 : ℝ)..(2 * π),
      Real.cos ((a : ℝ) * θ) * Real.cos ((b : ℝ) * θ) * Real.cos ((c : ℝ) * θ)) = 0 := by
  have hk1 : ((a : ℤ) + b + c) ≠ 0 := by omega
  have hk2 : ((a : ℤ) + b - c) ≠ 0 := by omega
  have hk3 : ((a : ℤ) - b + c) ≠ 0 := by omega
  have hk4 : ((a : ℤ) - b - c) ≠ 0 := by omega
  -- product-to-sum, as a function equality
  have hfun : (fun θ : ℝ =>
        Real.cos ((a : ℝ) * θ) * Real.cos ((b : ℝ) * θ) * Real.cos ((c : ℝ) * θ))
      = fun θ => ((1 / 4) * Real.cos ((((a : ℤ) + b + c : ℤ) : ℝ) * θ)
          + (1 / 4) * Real.cos ((((a : ℤ) + b - c : ℤ) : ℝ) * θ))
          + ((1 / 4) * Real.cos ((((a : ℤ) - b + c : ℤ) : ℝ) * θ)
          + (1 / 4) * Real.cos ((((a : ℤ) - b - c : ℤ) : ℝ) * θ)) := by
    funext θ
    push_cast
    have e1 : ((a : ℝ) + b + c) * θ = ((a : ℝ) * θ + (b : ℝ) * θ) + (c : ℝ) * θ := by ring
    have e2 : ((a : ℝ) + b - c) * θ = ((a : ℝ) * θ + (b : ℝ) * θ) - (c : ℝ) * θ := by ring
    have e3 : ((a : ℝ) - b + c) * θ = ((a : ℝ) * θ - (b : ℝ) * θ) + (c : ℝ) * θ := by ring
    have e4 : ((a : ℝ) - b - c) * θ = ((a : ℝ) * θ - (b : ℝ) * θ) - (c : ℝ) * θ := by ring
    rw [e1, e2, e3, e4]
    simp only [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
    ring
  have hcos : ∀ k : ℤ, IntervalIntegrable
      (fun θ : ℝ => (1 / 4) * Real.cos ((k : ℝ) * θ)) MeasureTheory.volume 0 (2 * π) :=
    fun k => ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).const_mul _).intervalIntegrable _ _
  rw [hfun, intervalIntegral.integral_add ((hcos _).add (hcos _)) ((hcos _).add (hcos _)),
      intervalIntegral.integral_add (hcos _) (hcos _),
      intervalIntegral.integral_add (hcos _) (hcos _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_int_mul_eq_zero _ hk1, integral_cos_int_mul_eq_zero _ hk2,
      integral_cos_int_mul_eq_zero _ hk3, integral_cos_int_mul_eq_zero _ hk4]
  ring

/-- **The third moment vanishes on sum-free sets:** `∫₀^{2π} (cosineSum A)³ = 0`
when `a, b ∈ A → a + b ∉ A`.  Expand the cube into the triple sum
`∑_{a,b,c ∈ A} cos(aθ)cos(bθ)cos(cθ)`; sum-freeness rules out all three additive
relations for every triple, so each term integrates to `0`
(`integral_cos_mul_cos_mul_cos_eq_zero`).  (In general the third moment equals
`(3π/2)·#{(a,b) ∈ A² : a + b ∈ A}`; only the vanishing case is needed here.) -/
theorem integral_cosineSum_cube_eq_zero (A : Finset ℕ)
    (hsf : ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A) :
    ∫ θ in (0 : ℝ)..(2 * π), (cosineSum A θ) ^ 3 = 0 := by
  have hexp : ∀ θ : ℝ, (cosineSum A θ) ^ 3
      = ∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ A,
          Real.cos ((a : ℝ) * θ) * Real.cos ((b : ℝ) * θ) * Real.cos ((c : ℝ) * θ) := by
    intro θ
    have h3 : (cosineSum A θ) ^ 3 = cosineSum A θ * cosineSum A θ * cosineSum A θ := by ring
    rw [h3]
    simp only [cosineSum]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]
  have hcont : ∀ n : ℕ, Continuous (fun θ : ℝ => Real.cos ((n : ℝ) * θ)) :=
    fun n => Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hint3 : ∀ a b c : ℕ, IntervalIntegrable
      (fun θ => Real.cos ((a : ℝ) * θ) * Real.cos ((b : ℝ) * θ) * Real.cos ((c : ℝ) * θ))
      MeasureTheory.volume 0 (2 * π) :=
    fun a b c => (((hcont a).mul (hcont b)).mul (hcont c)).intervalIntegrable _ _
  have hint2 : ∀ a b : ℕ, IntervalIntegrable
      (fun θ => ∑ c ∈ A,
        Real.cos ((a : ℝ) * θ) * Real.cos ((b : ℝ) * θ) * Real.cos ((c : ℝ) * θ))
      MeasureTheory.volume 0 (2 * π) :=
    fun a b => (continuous_finsetSum A
      (fun c _ => ((hcont a).mul (hcont b)).mul (hcont c))).intervalIntegrable _ _
  have hint1 : ∀ a : ℕ, IntervalIntegrable
      (fun θ => ∑ b ∈ A, ∑ c ∈ A,
        Real.cos ((a : ℝ) * θ) * Real.cos ((b : ℝ) * θ) * Real.cos ((c : ℝ) * θ))
      MeasureTheory.volume 0 (2 * π) :=
    fun a => (continuous_finsetSum A (fun b _ => continuous_finsetSum A
      (fun c _ => ((hcont a).mul (hcont b)).mul (hcont c)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun θ _ => hexp θ),
      intervalIntegral.integral_finsetSum (fun a _ => hint1 a)]
  refine Finset.sum_eq_zero (fun a ha => ?_)
  rw [intervalIntegral.integral_finsetSum (fun b _ => hint2 a b)]
  refine Finset.sum_eq_zero (fun b hb => ?_)
  rw [intervalIntegral.integral_finsetSum (fun c _ => hint3 a b c)]
  refine Finset.sum_eq_zero (fun c hc => ?_)
  exact integral_cos_mul_cos_mul_cos_eq_zero
    (fun h => hsf a ha b hb (by rw [h]; exact hc))
    (fun h => hsf a ha c hc (by rw [h]; exact hb))
    (fun h => hsf b hb c hc (by rw [h]; exact ha))

/-- **Chowla's `√N` bound for sum-free sets:** if `A` is nonempty and sum-free
(`a, b ∈ A → a + b ∉ A`), then `minCosineSum A ≤ −√(N/2)` where `N = |A|`.
Moment bootstrap: with `f = cosineSum A`, `m = minCosineSum A` the three moments
are `∫f = 0`, `∫f² = πN`, `∫f³ = 0` (sum-freeness kills the third moment), and
`f − m ≥ 0` pointwise, so the Cauchy–Schwarz-type integrand
`(f−m)·((−2m)(f−m) − (N+2m²))² ≥ 0` integrates to `2πmN(N − 2m²) ≥ 0`; since
`m < 0 < N` this forces `N ≤ 2m²`, i.e. `m ≤ −√(N/2)`.  This establishes the
conjectured `√N` growth rate (with explicit constant `1/√2`) on the sum-free
subclass; the general case — sets with additive structure — remains open. -/
theorem minCosineSum_le_neg_sqrt_half_card (A : Finset ℕ) (hne : A.Nonempty)
    (hsf : ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A) :
    minCosineSum A ≤ -Real.sqrt ((A.card : ℝ) / 2) := by
  have hA : 0 ∉ A := by
    intro h0
    exact hsf 0 h0 0 h0 (by simpa using h0)
  set g := cosineSum A with hg
  set m := minCosineSum A with hm
  set N : ℝ := (A.card : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Finset.card_pos.mpr hne
  have hmneg : m < 0 := minCosineSum_neg A hA hne
  have I1 : ∫ θ in (0 : ℝ)..(2 * π), g θ = 0 := integral_cosineSum_eq_zero A hA
  have I2 : ∫ θ in (0 : ℝ)..(2 * π), (g θ) ^ 2 = π * N := integral_cosineSum_sq A hA
  have I3 : ∫ θ in (0 : ℝ)..(2 * π), (g θ) ^ 3 = 0 := integral_cosineSum_cube_eq_zero A hsf
  have hlow : ∀ θ, m ≤ g θ := fun θ => minCosineSum_le A θ
  -- The nonnegative integrand `u·(αu − β)²` with `u = f − m ≥ 0`, `α = −2m`, `β = N + 2m²`.
  have hnonneg : 0 ≤ ∫ θ in (0 : ℝ)..(2 * π),
      (g θ - m) * ((-2 * m) * (g θ - m) - (N + 2 * m ^ 2)) ^ 2 := by
    apply intervalIntegral.integral_nonneg (by positivity)
    intro θ _
    exact mul_nonneg (by linarith [hlow θ]) (sq_nonneg _)
  -- Evaluate that integral in closed form via the three moments.
  have hc3 : IntervalIntegrable (fun θ => 4 * m ^ 2 * (g θ) ^ 3)
      MeasureTheory.volume 0 (2 * π) :=
    (((continuous_cosineSum A).pow 3).const_mul _).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun θ => (4 * m * N - 4 * m ^ 3) * (g θ) ^ 2)
      MeasureTheory.volume 0 (2 * π) :=
    (((continuous_cosineSum A).pow 2).const_mul _).intervalIntegrable _ _
  have hc1 : IntervalIntegrable (fun θ => (N ^ 2 - 4 * N * m ^ 2) * g θ)
      MeasureTheory.volume 0 (2 * π) :=
    ((continuous_cosineSum A).const_mul _).intervalIntegrable _ _
  have hcompute : (∫ θ in (0 : ℝ)..(2 * π),
      (g θ - m) * ((-2 * m) * (g θ - m) - (N + 2 * m ^ 2)) ^ 2)
      = 2 * π * m * N * (N - 2 * m ^ 2) := by
    rw [intervalIntegral.integral_congr (fun θ _ => show
          (g θ - m) * ((-2 * m) * (g θ - m) - (N + 2 * m ^ 2)) ^ 2
            = 4 * m ^ 2 * (g θ) ^ 3 + ((4 * m * N - 4 * m ^ 3) * (g θ) ^ 2
              + ((N ^ 2 - 4 * N * m ^ 2) * g θ + -(m * N ^ 2))) by ring),
        intervalIntegral.integral_add hc3 (hc2.add (hc1.add intervalIntegrable_const)),
        intervalIntegral.integral_add hc2 (hc1.add intervalIntegrable_const),
        intervalIntegral.integral_add hc1 intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
        I1, I2, I3]
    simp only [smul_eq_mul]; ring
  rw [hcompute] at hnonneg
  -- `0 ≤ 2πmN(N − 2m²)` with `m < 0 < N` forces `N ≤ 2m²`.
  have hπ : 0 < π := Real.pi_pos
  have hQ : m * (π * N) < 0 := mul_neg_of_neg_of_pos hmneg (mul_pos hπ hNpos)
  have hkey : N ≤ 2 * m ^ 2 := by nlinarith [hnonneg, hQ]
  -- Convert `N ≤ 2m²` into `m ≤ −√(N/2)`.
  have habs : Real.sqrt (N / 2) ≤ -m := by
    have h1 : Real.sqrt (N / 2) ≤ Real.sqrt ((-m) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ -m)] at h1
  linarith

/-- **Existential form of the sum-free `√N` bound**, matching the shape of
Chowla's conjecture: a nonempty sum-free set admits an angle `θ` with
`cosineSum A θ < −(1/2)·√N` (strict, with the clean constant `c = 1/2 < 1/√2`).
The minimizing angle (`exists_eq_minCosineSum`) realises the value
`minCosineSum A ≤ −√(N/2)`, and `√(N/2) = √N/√2 > √N/2` for `N ≥ 1`. -/
theorem exists_angle_cosineSum_lt_neg_half_sqrt (A : Finset ℕ) (hne : A.Nonempty)
    (hsf : ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A) :
    ∃ θ, cosineSum A θ < -(1 / 2) * Real.sqrt (A.card : ℝ) := by
  obtain ⟨θ₀, hθ₀⟩ := exists_eq_minCosineSum A
  refine ⟨θ₀, ?_⟩
  have hbound := minCosineSum_le_neg_sqrt_half_card A hne hsf
  set N : ℝ := (A.card : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Finset.card_pos.mpr hne
  -- `(1/2)·√N = √(N/4) < √(N/2)`
  have h14 : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
    rw [show ((1 : ℝ) / 4) = (1 / 2) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hq : (1 / 2) * Real.sqrt N = Real.sqrt (N / 4) := by
    rw [show (N / 4) = N * (1 / 4) by ring, Real.sqrt_mul hNpos.le, h14]
    ring
  have hlt : Real.sqrt (N / 4) < Real.sqrt (N / 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  rw [hθ₀]
  calc minCosineSum A ≤ -Real.sqrt (N / 2) := hbound
    _ < -((1 / 2) * Real.sqrt N) := by rw [hq]; linarith
    _ = -(1 / 2) * Real.sqrt N := by ring

/-! ## The interval family `{1, …, N}`: linear growth of the minimum

Chowla's conjecture concerns sets with *additive structure* — for Sidon or
sum-free sets the minimum is only `≍ −√N`.  Here we pin down the opposite
extreme: the maximally structured set `A = {1, …, N}` has *linearly* negative
minimum.  The mechanism is the classical Dirichlet-kernel closed form:
multiplying the cosine sum by `2 sin(θ/2)` telescopes it via product-to-sum,
and at the angle `θ₀ = 3π/(2N+1)` — the middle of the kernel's first negative
lobe, where `sin((2N+1)θ₀/2) = sin(3π/2) = −1` — the sum evaluates exactly to
`−1/2 − 1/(2 sin(θ₀/2))`, which `sin x ≤ x` pushes below
`−1/2 − (2N+1)/(3π) < −0.21·N`. -/

/-- **Telescoping (Dirichlet-kernel) identity**: for every angle `θ`,
`2 sin(θ/2) · ∑_{n=1}^N cos(nθ) = sin((2N+1)θ/2) − sin(θ/2)`.
Each term satisfies the product-to-sum identity
`2 cos(nθ) sin(θ/2) = sin((2n+1)θ/2) − sin((2n−1)θ/2)`, so the sum
telescopes. -/
theorem two_sin_half_mul_cosineSum_Icc (N : ℕ) (θ : ℝ) :
    2 * Real.sin (θ / 2) * cosineSum (Finset.Icc 1 N) θ
      = Real.sin ((2 * (N : ℝ) + 1) * θ / 2) - Real.sin (θ / 2) := by
  induction N with
  | zero =>
      have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      have e : (2 * ((0 : ℕ) : ℝ) + 1) * θ / 2 = θ / 2 := by push_cast; ring
      rw [h0, cosineSum_empty, mul_zero, e, sub_self]
  | succ n ih =>
      have hnot : n + 1 ∉ Finset.Icc 1 n := by
        intro h
        exact absurd (Finset.mem_Icc.mp h).2 (by omega)
      have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, cosineSum_insert _ hnot, mul_add, ih]
      push_cast
      have key : Real.sin ((2 * ((n : ℝ) + 1) + 1) * θ / 2)
          = Real.sin ((2 * (n : ℝ) + 1) * θ / 2)
            + 2 * Real.sin (θ / 2) * Real.cos (((n : ℝ) + 1) * θ) := by
        have e1 : (2 * ((n : ℝ) + 1) + 1) * θ / 2 = ((n : ℝ) + 1) * θ + θ / 2 := by ring
        have e2 : (2 * (n : ℝ) + 1) * θ / 2 = ((n : ℝ) + 1) * θ - θ / 2 := by ring
        rw [e1, e2, Real.sin_add, Real.sin_sub]
        ring
      linarith [key]

/-- **Linear growth for the interval family**: for `N ≥ 1`,
`minCosineSum {1, …, N} ≤ −1/2 − (2N+1)/(3π)`.

Evaluate the telescoped sum at `θ₀ = 3π/(2N+1)`: there `(2N+1)θ₀/2 = 3π/2`
exactly, so `sin((2N+1)θ₀/2) = −1` and
`cosineSum {1,…,N} θ₀ = −1/2 − 1/(2 sin(θ₀/2))`; since
`0 < sin(θ₀/2) ≤ θ₀/2 = 3π/(2(2N+1))` this is at most `−1/2 − (2N+1)/(3π)`.
Together with the trivial floor `−N ≤ minCosineSum` (`neg_card_le_minCosineSum`)
the interval minimum is pinned to `Θ(N)`: linear, in sharp contrast with the
`≍ √N` behaviour of Sidon/sum-free sets.  Additive structure genuinely drives
the minimum down — the quantitative heart of Chowla's problem. -/
theorem minCosineSum_Icc_le (N : ℕ) (hN : 1 ≤ N) :
    minCosineSum (Finset.Icc 1 N) ≤ -1 / 2 - (2 * (N : ℝ) + 1) / (3 * π) := by
  have hπ : 0 < π := Real.pi_pos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hTpos : (0 : ℝ) < 2 * (N : ℝ) + 1 := by linarith
  have hTne : (2 * (N : ℝ) + 1) ≠ 0 := ne_of_gt hTpos
  set θ₀ : ℝ := 3 * π / (2 * (N : ℝ) + 1) with hθ₀
  have hhalf_pos : 0 < θ₀ / 2 := by rw [hθ₀]; positivity
  have hhalf_lt : θ₀ / 2 < π := by
    rw [hθ₀, div_div, div_lt_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hN1 hπ.le]
  have hspos : 0 < Real.sin (θ₀ / 2) := Real.sin_pos_of_pos_of_lt_pi hhalf_pos hhalf_lt
  have hsne : Real.sin (θ₀ / 2) ≠ 0 := ne_of_gt hspos
  have hslt : Real.sin (θ₀ / 2) < θ₀ / 2 := Real.sin_lt hhalf_pos
  have htel := two_sin_half_mul_cosineSum_Icc N θ₀
  -- at `θ₀` the leading sine argument is exactly `3π/2 = π/2 + π`
  have harg : (2 * (N : ℝ) + 1) * θ₀ / 2 = π / 2 + π := by
    rw [hθ₀]
    field_simp
    ring
  have hsin32 : Real.sin ((2 * (N : ℝ) + 1) * θ₀ / 2) = -1 := by
    rw [harg, Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two,
        Real.cos_pi_div_two]
    ring
  rw [hsin32] at htel
  -- `htel : 2 sin(θ₀/2) · cosineSum = −1 − sin(θ₀/2)`, so the sum is
  -- `−1/2 − 1/(2 sin(θ₀/2))`
  have hC : cosineSum (Finset.Icc 1 N) θ₀ = -1 / 2 - 1 / (2 * Real.sin (θ₀ / 2)) := by
    field_simp
    linarith [htel]
  -- `(2N+1)θ₀ = 3π`, hence `2(2N+1)·sin(θ₀/2) ≤ (2N+1)θ₀ = 3π`
  have h2 : (2 * (N : ℝ) + 1) * θ₀ = 3 * π := by
    rw [hθ₀]
    field_simp
  have h1 : (2 * (N : ℝ) + 1) / (3 * π) ≤ 1 / (2 * Real.sin (θ₀ / 2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hslt.le, h2, hTpos]
  calc minCosineSum (Finset.Icc 1 N)
      ≤ cosineSum (Finset.Icc 1 N) θ₀ := minCosineSum_le _ θ₀
    _ = -1 / 2 - 1 / (2 * Real.sin (θ₀ / 2)) := hC
    _ ≤ -1 / 2 - (2 * (N : ℝ) + 1) / (3 * π) := by linarith [h1]

/-- **The interval minimum is `Θ(N)`** — two-sided pinning: for `N ≥ 1`,
`−N ≤ minCosineSum {1,…,N} ≤ −(2N+1)/(3π) < −N·2/(3π)`.  Packaged as the
strict comparison against the general `√N` conjecture's scale: the interval
beats any `−c√N` bound once `N > (3πc/2)²`. -/
theorem minCosineSum_Icc_lt_neg_frac (N : ℕ) (hN : 1 ≤ N) :
    minCosineSum (Finset.Icc 1 N) < -(2 / (3 * π)) * (N : ℝ) := by
  have hπ : 0 < π := Real.pi_pos
  have h := minCosineSum_Icc_le N hN
  have e : -(2 / (3 * π)) * (N : ℝ) - (-1 / 2 - (2 * (N : ℝ) + 1) / (3 * π))
      = 1 / 2 + 1 / (3 * π) := by
    field_simp
    ring
  have hpos : (0 : ℝ) < 1 / 2 + 1 / (3 * π) := by positivity
  linarith

/-! ## Superadditivity of the minimum under disjoint union

Splitting the frequency set splits the cosine sum pointwise, so the minimum of a
disjoint union is at least the sum of the minima: the negativity `m(A) := −min`
is *subadditive*, `m(A ∪ B) ≤ m(A) + m(B)`.  With `minCosineSum_le_neg_half`
this brackets the union: `min A + min B ≤ min (A ∪ B) ≤ −1/2`.  It also shows
the trivial floor `−N` (attained exactly by all-odd sets,
`minCosineSum_forall_odd`) is the worst case of the union bound over
singletons (`minCosineSum_singleton = −1`). -/

/-- **Disjoint frequency sets add pointwise**: `cosineSum (A ∪ B) = cosineSum A
+ cosineSum B` when `Disjoint A B` (`Finset.sum_union`). -/
theorem cosineSum_union {A B : Finset ℕ} (hAB : Disjoint A B) (θ : ℝ) :
    cosineSum (A ∪ B) θ = cosineSum A θ + cosineSum B θ := by
  unfold cosineSum
  exact Finset.sum_union hAB

/-- **The Chowla minimum is superadditive on disjoint unions**:
`minCosineSum A + minCosineSum B ≤ minCosineSum (A ∪ B)`.  Pointwise each
summand is at least its own minimum; take the infimum.  Equivalently the
negativity `m = −min` is subadditive — the elementary "union bound" backbone
against which the conjectured `−c√N` (sublinear!) uniform bound is measured. -/
theorem add_minCosineSum_le_minCosineSum_union {A B : Finset ℕ}
    (hAB : Disjoint A B) :
    minCosineSum A + minCosineSum B ≤ minCosineSum (A ∪ B) := by
  unfold minCosineSum
  apply le_csInf (Set.range_nonempty _)
  rintro y ⟨θ, rfl⟩
  rw [cosineSum_union hAB θ]
  exact add_le_add (minCosineSum_le A θ) (minCosineSum_le B θ)

/-! ## The L¹–L⁴ analytic engine for the Sidon-class `√N` bound

Chowla's conjecture predicts `minCosineSum A ≤ −c·√N` for *every*
positive-frequency set.  For **Sidon sets** (`B₂[1]`: all pairwise sums
distinct) the classical elementary route is a moment argument:

1. the fourth moment `∫₀^{2π} f⁴` counts additive quadruples
   `a + b = c + d`, which the Sidon condition caps at `O(N²)`;
2. Cauchy–Schwarz twice (through the odd moment `∫|f|³`) turns the
   second-moment identity `∫f² = πN` into the L¹ lower bound
   `(πN)³ ≤ (∫f⁴)·(∫|f|)²`;
3. since `∫f = 0` over a period, the negative part of `f` carries half the
   L¹ mass, and the pointwise floor `f ≥ m := minCosineSum A` converts that
   mass into `∫|f| ≤ 4π·(−m)`.

This section formalizes the complete *analytic* engine (steps 2 and 3 and
their combination): any fourth-moment bound `∫f⁴ ≤ B` now yields
`minCosineSum A ≤ −√(π³N³/B)/(4π)`
(`minCosineSum_le_neg_sqrt_of_fourth_moment`).  Instantiating `B = O(N²)` —
the remaining *combinatorial* step 1, a quadruple count under the Sidon
condition — will give the conjectured `−c·√N` on the Sidon class,
complementing the sum-free class (`minCosineSum_le_neg_sqrt_half_card`,
third-moment mechanism) with an orthogonal fourth-moment mechanism. -/

/-- **Cauchy–Schwarz for interval integrals** (continuous integrands):
`(∫ u·v)² ≤ (∫u²)·(∫v²)` over `[0, 2π]`.  For every `t` the quadratic
`t²·∫u² − 2t·∫uv + ∫v² = ∫(t·u − v)²` is nonnegative, so its discriminant
is nonpositive (`discrim_le_zero`). -/
theorem sq_integral_mul_le (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ θ in (0 : ℝ)..(2 * π), u θ * v θ) ^ 2
      ≤ (∫ θ in (0 : ℝ)..(2 * π), (u θ) ^ 2)
        * (∫ θ in (0 : ℝ)..(2 * π), (v θ) ^ 2) := by
  set a : ℝ := ∫ θ in (0 : ℝ)..(2 * π), (u θ) ^ 2 with ha
  set b : ℝ := ∫ θ in (0 : ℝ)..(2 * π), u θ * v θ with hb
  set c : ℝ := ∫ θ in (0 : ℝ)..(2 * π), (v θ) ^ 2 with hc
  have hq : ∀ t : ℝ, 0 ≤ a * (t * t) + (-(2 * b)) * t + c := by
    intro t
    have hu2 : IntervalIntegrable (fun θ => t ^ 2 * (u θ) ^ 2)
        MeasureTheory.volume 0 (2 * π) :=
      ((hu.pow 2).const_mul _).intervalIntegrable _ _
    have huv : IntervalIntegrable (fun θ => (-(2 * t)) * (u θ * v θ))
        MeasureTheory.volume 0 (2 * π) :=
      ((hu.mul hv).const_mul _).intervalIntegrable _ _
    have hv2 : IntervalIntegrable (fun θ => (v θ) ^ 2)
        MeasureTheory.volume 0 (2 * π) :=
      (hv.pow 2).intervalIntegrable _ _
    have hnn : 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), (t * u θ - v θ) ^ 2 :=
      intervalIntegral.integral_nonneg (by positivity) (fun θ _ => sq_nonneg _)
    have hexp : (∫ θ in (0 : ℝ)..(2 * π), (t * u θ - v θ) ^ 2)
        = t ^ 2 * a + (-(2 * t)) * b + c := by
      rw [intervalIntegral.integral_congr (fun θ _ => show
            (t * u θ - v θ) ^ 2
              = t ^ 2 * (u θ) ^ 2 + ((-(2 * t)) * (u θ * v θ) + (v θ) ^ 2) by ring),
          intervalIntegral.integral_add hu2 (huv.add hv2),
          intervalIntegral.integral_add huv hv2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          ← ha, ← hb, ← hc]
      ring
    rw [hexp] at hnn
    nlinarith [hnn]
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

/-- **The L¹ norm is controlled by the minimum**: for a positive-frequency
set, `∫₀^{2π} |cosineSum A θ| dθ ≤ 4π·(−minCosineSum A)`.  Since `∫f = 0`
over a period, the positive and negative parts of `f` have equal mass, and
the negative part is pointwise at most `−m`; concretely `|f| ≤ f − 2m`
pointwise (both cases of the sign of `f θ`, using `m ≤ 0` and `m ≤ f θ`),
and the right side integrates to `−4πm`. -/
theorem integral_abs_cosineSum_le (A : Finset ℕ) (hA : 0 ∉ A) :
    ∫ θ in (0 : ℝ)..(2 * π), |cosineSum A θ| ≤ 4 * π * (-minCosineSum A) := by
  set g := cosineSum A with hg
  set m := minCosineSum A with hm
  have hm0 : m ≤ 0 := minCosineSum_nonpos A hA
  have hlow : ∀ θ, m ≤ g θ := fun θ => minCosineSum_le A θ
  have habs : IntervalIntegrable (fun θ => |g θ|) MeasureTheory.volume 0 (2 * π) :=
    (continuous_cosineSum A).abs.intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun θ => g θ - 2 * m) MeasureTheory.volume 0 (2 * π) :=
    ((continuous_cosineSum A).sub continuous_const).intervalIntegrable _ _
  have hmono : (∫ θ in (0 : ℝ)..(2 * π), |g θ|)
      ≤ ∫ θ in (0 : ℝ)..(2 * π), (g θ - 2 * m) := by
    refine intervalIntegral.integral_mono_on (by positivity) habs hgi (fun θ _ => ?_)
    exact abs_le.mpr ⟨by linarith [hlow θ], by linarith [hlow θ]⟩
  have hIg : ∫ θ in (0 : ℝ)..(2 * π), g θ = 0 := integral_cosineSum_eq_zero A hA
  have hval : (∫ θ in (0 : ℝ)..(2 * π), (g θ - 2 * m)) = 4 * π * (-m) := by
    rw [intervalIntegral.integral_sub ((continuous_cosineSum A).intervalIntegrable _ _)
        intervalIntegrable_const, hIg, intervalIntegral.integral_const]
    simp only [smul_eq_mul]; ring
  linarith [hmono, hval]

/-- **The L²–L⁴–L¹ moment chain**: `(πN)³ ≤ (∫f⁴)·(∫|f|)²` for the cosine
sum of a positive-frequency set.  Cauchy–Schwarz twice through the
half-power `s = √|f|`: first `(∫f²)² = (∫ s³·s)² ≤ (∫|f|³)·(∫|f|)`, then
`(∫|f|³)² = (∫ f²·|f|)² ≤ (∫f⁴)·(∫f²)`; combining and cancelling one
factor of `∫f² = πN > 0` gives the cube inequality.  This is the Hölder
step `‖f‖₂ ≤ ‖f‖₄^{2/3}·‖f‖₁^{1/3}` in integral form, with no fractional
powers anywhere. -/
theorem pow_three_second_moment_le (A : Finset ℕ) (hA : 0 ∉ A) (hne : A.Nonempty) :
    (π * (A.card : ℝ)) ^ 3
      ≤ (∫ θ in (0 : ℝ)..(2 * π), (cosineSum A θ) ^ 4)
        * (∫ θ in (0 : ℝ)..(2 * π), |cosineSum A θ|) ^ 2 := by
  set g := cosineSum A with hg
  have hgc : Continuous g := continuous_cosineSum A
  set s : ℝ → ℝ := fun θ => Real.sqrt |g θ| with hsdef
  have hsc : Continuous s := hgc.abs.sqrt
  have hs2 : ∀ θ, s θ ^ 2 = |g θ| := fun θ => Real.sq_sqrt (abs_nonneg _)
  -- Cauchy–Schwarz 1: `(∫f²)² ≤ (∫|f|³)·(∫|f|)`.
  have hCS1 := sq_integral_mul_le (fun θ => s θ ^ 3) s (hsc.pow 3) hsc
  have e1 : (∫ θ in (0 : ℝ)..(2 * π), s θ ^ 3 * s θ)
      = ∫ θ in (0 : ℝ)..(2 * π), (g θ) ^ 2 :=
    intervalIntegral.integral_congr (fun θ _ => by
      calc s θ ^ 3 * s θ = (s θ ^ 2) ^ 2 := by ring
        _ = |g θ| ^ 2 := by rw [hs2 θ]
        _ = (g θ) ^ 2 := sq_abs _)
  have e2 : (∫ θ in (0 : ℝ)..(2 * π), (s θ ^ 3) ^ 2)
      = ∫ θ in (0 : ℝ)..(2 * π), |g θ| ^ 3 :=
    intervalIntegral.integral_congr (fun θ _ => by
      calc (s θ ^ 3) ^ 2 = (s θ ^ 2) ^ 3 := by ring
        _ = |g θ| ^ 3 := by rw [hs2 θ])
  have e3 : (∫ θ in (0 : ℝ)..(2 * π), s θ ^ 2)
      = ∫ θ in (0 : ℝ)..(2 * π), |g θ| :=
    intervalIntegral.integral_congr (fun θ _ => hs2 θ)
  rw [e1, e2, e3] at hCS1
  -- Cauchy–Schwarz 2: `(∫|f|³)² ≤ (∫f⁴)·(∫f²)`.
  have hCS2 := sq_integral_mul_le (fun θ => (g θ) ^ 2) (fun θ => |g θ|)
    (hgc.pow 2) hgc.abs
  have e4 : (∫ θ in (0 : ℝ)..(2 * π), (g θ) ^ 2 * |g θ|)
      = ∫ θ in (0 : ℝ)..(2 * π), |g θ| ^ 3 :=
    intervalIntegral.integral_congr (fun θ _ => by
      calc (g θ) ^ 2 * |g θ| = |g θ| ^ 2 * |g θ| := by rw [sq_abs]
        _ = |g θ| ^ 3 := by ring)
  have e5 : (∫ θ in (0 : ℝ)..(2 * π), ((g θ) ^ 2) ^ 2)
      = ∫ θ in (0 : ℝ)..(2 * π), (g θ) ^ 4 :=
    intervalIntegral.integral_congr (fun θ _ => by ring)
  have e6 : (∫ θ in (0 : ℝ)..(2 * π), |g θ| ^ 2)
      = ∫ θ in (0 : ℝ)..(2 * π), (g θ) ^ 2 :=
    intervalIntegral.integral_congr (fun θ _ => sq_abs _)
  rw [e4, e5, e6] at hCS2
  -- Assemble with the second moment `∫f² = πN` and cancel one factor `πN > 0`.
  have hX : ∫ θ in (0 : ℝ)..(2 * π), (g θ) ^ 2 = π * A.card :=
    integral_cosineSum_sq A hA
  rw [hX] at hCS1 hCS2
  set F : ℝ := ∫ θ in (0 : ℝ)..(2 * π), (g θ) ^ 4 with hF
  set L : ℝ := ∫ θ in (0 : ℝ)..(2 * π), |g θ| with hLdef
  set T : ℝ := ∫ θ in (0 : ℝ)..(2 * π), |g θ| ^ 3 with hTdef
  have hNpos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hXpos : 0 < π * (A.card : ℝ) := mul_pos Real.pi_pos hNpos
  have hsq : ((π * (A.card : ℝ)) ^ 2) * ((π * (A.card : ℝ)) ^ 2)
      ≤ (T * L) * (T * L) :=
    mul_self_le_mul_self (sq_nonneg _) hCS1
  have hTL : T ^ 2 * L ^ 2 ≤ (F * (π * (A.card : ℝ))) * L ^ 2 :=
    mul_le_mul_of_nonneg_right hCS2 (sq_nonneg L)
  nlinarith [hsq, hTL, hXpos]

/-- **Conditional Chowla bound from a fourth-moment estimate**: any bound
`∫₀^{2π} f⁴ ≤ B` forces `minCosineSum A ≤ −√(π³N³/B)/(4π)`.  This is the
complete analytic engine for the Sidon route: the combinatorial quadruple
count `∫f⁴ ≤ O(N²)` for Sidon (`B₂[1]`) sets, once formalized, instantiates
`B` and yields the conjectured `−c·√N` on the Sidon class. -/
theorem minCosineSum_le_neg_sqrt_of_fourth_moment (A : Finset ℕ) (hA : 0 ∉ A)
    (hne : A.Nonempty) {B : ℝ}
    (hB : (∫ θ in (0 : ℝ)..(2 * π), (cosineSum A θ) ^ 4) ≤ B) :
    minCosineSum A ≤ -(Real.sqrt (π ^ 3 * (A.card : ℝ) ^ 3 / B) / (4 * π)) := by
  set g := cosineSum A with hg
  set m := minCosineSum A with hm
  set L : ℝ := ∫ θ in (0 : ℝ)..(2 * π), |g θ| with hLdef
  have hLnn : 0 ≤ L :=
    intervalIntegral.integral_nonneg (by positivity) (fun θ _ => abs_nonneg _)
  have hchain : (π * (A.card : ℝ)) ^ 3
      ≤ (∫ θ in (0 : ℝ)..(2 * π), (g θ) ^ 4) * L ^ 2 :=
    pow_three_second_moment_le A hA hne
  have hNpos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hXpos : 0 < π * (A.card : ℝ) := mul_pos Real.pi_pos hNpos
  have hcube : (π * (A.card : ℝ)) ^ 3 ≤ B * L ^ 2 :=
    le_trans hchain (mul_le_mul_of_nonneg_right hB (sq_nonneg L))
  have hBpos : 0 < B := by nlinarith [hcube, pow_pos hXpos 3, sq_nonneg L]
  -- `L ≥ √(π³N³/B)`.
  have hdiv : π ^ 3 * (A.card : ℝ) ^ 3 / B ≤ L ^ 2 := by
    rw [div_le_iff₀ hBpos]
    nlinarith [hcube]
  have hsqrt : Real.sqrt (π ^ 3 * (A.card : ℝ) ^ 3 / B) ≤ L := by
    calc Real.sqrt (π ^ 3 * (A.card : ℝ) ^ 3 / B) ≤ Real.sqrt (L ^ 2) :=
        Real.sqrt_le_sqrt hdiv
      _ = L := Real.sqrt_sq hLnn
  -- Convert the L¹ mass into the minimum via `∫|f| ≤ 4π·(−m)`.
  have hL1 : L ≤ 4 * π * (-m) := integral_abs_cosineSum_le A hA
  have h4π : (0 : ℝ) < 4 * π := by positivity
  have hfin : Real.sqrt (π ^ 3 * (A.card : ℝ) ^ 3 / B) / (4 * π) ≤ -m := by
    rw [div_le_iff₀ h4π]
    nlinarith [hsqrt, hL1]
  linarith [hfin]

end Erdos510WIP01
