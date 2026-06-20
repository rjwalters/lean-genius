/-
  Banach Fixed-Point Theorem (the Contraction Mapping Principle), with an
  explicit geometric convergence rate, plus a concrete worked instance on ℝ.

  Let `(α, d)` be a NONEMPTY COMPLETE metric space and `f : α → α` a
  CONTRACTION: there is a constant `K < 1` with `d(f x, f y) ≤ K · d(x, y)`
  for all `x, y`.  The Banach fixed-point theorem then asserts:

    * (existence)      `f` has a fixed point `p`  (`f p = p`);
    * (uniqueness)     the fixed point is unique;
    * (Picard)         from ANY seed `x` the iterates `fⁿ x → p`;
    * (a-priori)       `d(fⁿ x, p) ≤ d(x, f x) · Kⁿ / (1 − K)` — a GEOMETRIC
                       error bound computable before iterating;
    * (a-posteriori)   `d(x, p) ≤ d(x, f x) / (1 − K)` — a bound from a single
                       step.

  Mathlib packages the contraction hypothesis as `ContractingWith K f`
  (`K < 1 ∧ LipschitzWith K f`) over an `EMetricSpace`, and provides the fixed
  point `ContractingWith.fixedPoint` together with all of the estimates above.
  This file restates the theorem in textbook form and then VERIFIES the
  hypotheses for a concrete map — the affine contraction `x ↦ x/2 + c` on ℝ,
  whose unique fixed point is `2c` and whose Picard iterates converge to it
  geometrically at rate `1/2`.

  The gallery's existing fixed-point entries are topological (Brouwer) and
  Banach-space-compact (Schauder); the METRIC contraction principle with an
  explicit geometric rate was previously absent.  Everything is fully verified:
  0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open scoped NNReal
open Filter Topology Function

namespace BanachFixedPointOQ01

/-! ### The abstract contraction mapping principle

`ContractingWith K f` is Mathlib's bundling of "`K < 1` and `f` is
`K`-Lipschitz".  Over a nonempty complete metric space these five statements
are the full Banach fixed-point theorem. -/

variable {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
variable {K : ℝ≥0} {f : α → α}

/-- **Existence.** A contraction on a nonempty complete metric space has a
fixed point. -/
theorem exists_fixedPoint (hf : ContractingWith K f) : ∃ p, IsFixedPt f p :=
  ⟨ContractingWith.fixedPoint f hf, hf.fixedPoint_isFixedPt⟩

omit [CompleteSpace α] [Nonempty α] in
/-- **Uniqueness.** Any two fixed points of a contraction coincide. -/
theorem fixedPoint_unique_of_isFixedPt (hf : ContractingWith K f) {x y : α}
    (hx : IsFixedPt f x) (hy : IsFixedPt f y) : x = y :=
  hf.fixedPoint_unique' hx hy

/-- **Picard iteration converges.** From any seed `x`, the iterates `fⁿ x`
converge to the fixed point. -/
theorem tendsto_iterate (hf : ContractingWith K f) (x : α) :
    Tendsto (fun n => f^[n] x) atTop (𝓝 (ContractingWith.fixedPoint f hf)) :=
  hf.tendsto_iterate_fixedPoint x

/-- **A-priori geometric error estimate.**
`d(fⁿ x, p) ≤ d(x, f x) · Kⁿ / (1 − K)` — the error decays geometrically with
ratio `K`, with a bound known in advance of iterating. -/
theorem apriori_estimate (hf : ContractingWith K f) (x : α) (n : ℕ) :
    dist (f^[n] x) (ContractingWith.fixedPoint f hf)
      ≤ dist x (f x) * (K : ℝ) ^ n / (1 - K) :=
  hf.apriori_dist_iterate_fixedPoint_le x n

/-- **A-posteriori error estimate.** A single application bounds the distance to
the fixed point: `d(x, p) ≤ d(x, f x) / (1 − K)`. -/
theorem aposteriori_estimate (hf : ContractingWith K f) (x : α) :
    dist x (ContractingWith.fixedPoint f hf) ≤ dist x (f x) / (1 - K) :=
  hf.dist_fixedPoint_le x

/-! ### A concrete contraction on ℝ

The affine map `x ↦ x/2 + c` is `(1/2)`-Lipschitz, hence a contraction; its
unique fixed point is `2c`, reached geometrically from any starting point. -/

/-- The affine map `x ↦ x/2 + c` on the real line. -/
noncomputable def contractAffine (c : ℝ) : ℝ → ℝ := fun x => x / 2 + c

/-- `x ↦ x/2 + c` is a contraction with ratio `1/2`. -/
theorem contractAffine_contracting (c : ℝ) :
    ContractingWith (1 / 2 : ℝ≥0) (contractAffine c) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hK : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by push_cast; ring
  rw [hK, Real.dist_eq, Real.dist_eq,
    show contractAffine c x - contractAffine c y = (x - y) / 2 from by
      simp only [contractAffine]; ring,
    abs_div, show |(2 : ℝ)| = 2 from by norm_num]
  linarith [abs_nonneg (x - y)]

/-- The unique fixed point of `x ↦ x/2 + c` is `2c`. -/
theorem contractAffine_fixedPoint (c : ℝ) :
    ContractingWith.fixedPoint (contractAffine c) (contractAffine_contracting c) = 2 * c := by
  have hfix : IsFixedPt (contractAffine c) (2 * c) := by
    show contractAffine c (2 * c) = 2 * c
    simp only [contractAffine]; ring
  exact ((contractAffine_contracting c).fixedPoint_unique hfix).symm

/-- Picard iteration for the concrete map converges to `2c` from any start. -/
theorem contractAffine_tendsto (c x : ℝ) :
    Tendsto (fun n => (contractAffine c)^[n] x) atTop (𝓝 (2 * c)) := by
  rw [← contractAffine_fixedPoint c]
  exact (contractAffine_contracting c).tendsto_iterate_fixedPoint x

/-- Explicit geometric error bound for the concrete iteration:
`|fⁿ x − 2c| ≤ |x − (x/2 + c)| · (1/2)ⁿ / (1 − 1/2)`. -/
theorem contractAffine_apriori (c x : ℝ) (n : ℕ) :
    dist ((contractAffine c)^[n] x) (2 * c)
      ≤ dist x (contractAffine c x) * (1 / 2 : ℝ) ^ n / (1 - 1 / 2 : ℝ) := by
  rw [← contractAffine_fixedPoint c]
  have h := (contractAffine_contracting c).apriori_dist_iterate_fixedPoint_le x n
  have hK : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by push_cast; ring
  rw [hK] at h
  exact h

end BanachFixedPointOQ01
