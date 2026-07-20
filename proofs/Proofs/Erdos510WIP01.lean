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
* the exact value `minCosineSum {n} = −1` for `n ≥ 1`.

All results are `0`-axiom / `0`-sorry.  The genuinely open content — the
`−c√N` lower bound — is untouched (it is the mission, not the scaffolding).

Reference: <https://erdosproblems.com/510>
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

end Erdos510WIP01
