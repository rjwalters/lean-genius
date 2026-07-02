/-
  Erdős #671 — Orphan worktree for the single tractable supporting estimate.

  UNREGISTERED: this file is NOT part of the gallery entry. It exists only to
  develop / Aristotle-verify the one self-contained sorry of
  `Proofs/Erdos671Problem.lean`, namely `equidistant_diverges`, in isolation
  before any integration into the registered file.

  The registered theorem is
    `lebesgueConstant (equidistantNodes n hn) ≥ 2^(n-1) / n^2`.
  Since `lebesgueConstant = ⨆ x ∈ [-1,1], lebesgueFunction x`, a lower bound at
  any single admissible point x* dominates the constant (that sup-step needs
  `BddAbove`, handled separately). The mathematical heart is the *pointwise*
  estimate isolated here at x* = -1 + 1/(n-1), the midpoint of the first
  subinterval. This file carries no analysis — only a finite product/factorial
  inequality — and is the right target for `prove_file`.

  Reference numerics (research/problems/erdos-671/verify-equidistant-bound.py):
  the bound holds for all n = 2..25, with the dominant Lagrange basis index near
  the centre i ≈ (n-2)/2 (NOT an endpoint index).

  Session 2026-06-28 (researcher-2): the file is now BUILD-VERIFIED (Mathlib
  v4.26.0). The session-6 scaffold never compiled — `div_le_iff` was removed
  (→ `div_le_iff₀`) and a `linarith` lacked the `n ≥ 2` real cast. Both fixed.
  The monolithic pointwise sorry has been DECOMPOSED: the polynomial machinery
  (eval-as-product-of-ratios, abs distribution, single-term lower bound, and the
  midpoint / node-difference formulas) is now fully proved, leaving ONE residual
  sorry that is a pure finite real-arithmetic inequality: the existence of a
  central index whose explicit factorial ratio reaches `2^(n-1)/n^2`.
-/

import Mathlib

namespace Erdos671Orphan

open Polynomial

/-- Points for interpolation: a_i^n ∈ [-1, 1]. -/
structure InterpolationPoints (n : ℕ) where
  points : Fin n → ℝ
  in_interval : ∀ i, points i ∈ Set.Icc (-1 : ℝ) 1
  distinct : ∀ i j, i ≠ j → points i ≠ points j

/-- The Lagrange basis polynomial p_i^n. -/
noncomputable def lagrangeBasis {n : ℕ} (pts : InterpolationPoints n) (i : Fin n) :
    Polynomial ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).filter (fun k => k ≠ i),
    (Polynomial.C (1 / (pts.points i - pts.points j)) *
     (Polynomial.X - Polynomial.C (pts.points j)) : Polynomial ℝ)

/-- The Lebesgue function λ_n(x) = Σ |p_i^n(x)|. -/
noncomputable def lebesgueFunction {n : ℕ} (pts : InterpolationPoints n) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |(lagrangeBasis pts i).eval x|

/-- Equidistant nodes: x_k = -1 + 2k/(n-1). -/
noncomputable def equidistantNodes (n : ℕ) (hn : n ≥ 2) : InterpolationPoints n where
  points := fun k => -1 + 2 * (k.val : ℝ) / ((n : ℝ) - 1)
  in_interval := by
    intro k
    have hn_cast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hn
    have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    simp only [Set.mem_Icc]
    constructor
    · have : (0 : ℝ) ≤ 2 * (k.val : ℝ) / ((n : ℝ) - 1) :=
        div_nonneg (by positivity) (le_of_lt hn1_pos)
      linarith
    · -- k.val + 1 ≤ n  ⇒  (k.val : ℝ) ≤ n - 1
      have hk1 : (k.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt k.isLt
      have hkle : (k.val : ℝ) ≤ (n : ℝ) - 1 := by linarith
      have : 2 * (k.val : ℝ) / ((n : ℝ) - 1) ≤ 2 := by
        rw [div_le_iff₀ hn1_pos]; linarith
      linarith
  distinct := by
    intro k j hkj heq
    apply hkj
    have hn_cast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hn
    have hn1_ne : (n : ℝ) - 1 ≠ 0 := by linarith
    have h1 : 2 * (k.val : ℝ) / ((n : ℝ) - 1) = 2 * (j.val : ℝ) / ((n : ℝ) - 1) := by
      linarith
    have h2 : (k.val : ℝ) = j.val := by field_simp [hn1_ne] at h1; linarith
    exact Fin.ext (by exact_mod_cast h2)

/-- The evaluation point: midpoint of the first subinterval, x* = -1 + 1/(n-1). -/
noncomputable def midPoint (n : ℕ) : ℝ := -1 + 1 / ((n : ℝ) - 1)

/-- x* lies in [-1, 1] for n ≥ 2. -/
theorem midPoint_mem (n : ℕ) (hn : n ≥ 2) :
    midPoint n ∈ Set.Icc (-1 : ℝ) 1 := by
  have hn_cast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold midPoint
  simp only [Set.mem_Icc]
  constructor
  · have : (0 : ℝ) ≤ 1 / ((n : ℝ) - 1) := by positivity
    linarith
  · have : 1 / ((n : ℝ) - 1) ≤ 1 := by
      rw [div_le_one hn1_pos]; linarith
    linarith

/--
  EVAL AS A PRODUCT OF RATIOS.

  `p_i(x) = ∏_{j ≠ i} (x - a_j) / (a_i - a_j)`. This is the defining property of
  the Lagrange basis and the entry point for any pointwise estimate. Pure
  polynomial bookkeeping — no analysis.
-/
theorem lagrangeBasis_eval {n : ℕ} (pts : InterpolationPoints n) (i : Fin n) (x : ℝ) :
    (lagrangeBasis pts i).eval x =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).filter (fun k => k ≠ i),
        (x - pts.points j) / (pts.points i - pts.points j) := by
  unfold lagrangeBasis
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  ring

/-- `|p_i(x)| = ∏_{j ≠ i} |x - a_j| / |a_i - a_j|`. -/
theorem abs_lagrangeBasis_eval {n : ℕ} (pts : InterpolationPoints n) (i : Fin n) (x : ℝ) :
    |(lagrangeBasis pts i).eval x| =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).filter (fun k => k ≠ i),
        |x - pts.points j| / |pts.points i - pts.points j| := by
  rw [lagrangeBasis_eval, Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [abs_div]

/--
  SINGLE-TERM LOWER BOUND.

  The Lebesgue function dominates any single basis term: `λ_n(x) ≥ |p_i(x)|`.
  This reduces the pointwise bound to choosing one (central) index. Immediate
  from `Finset.single_le_sum` since every summand is nonnegative.
-/
theorem lebesgueFunction_ge_single {n : ℕ} (pts : InterpolationPoints n) (x : ℝ) (i : Fin n) :
    |(lagrangeBasis pts i).eval x| ≤ lebesgueFunction pts x := by
  unfold lebesgueFunction
  exact Finset.single_le_sum (f := fun k => |(lagrangeBasis pts k).eval x|)
    (fun k _ => abs_nonneg _) (Finset.mem_univ i)

/--
  NODE-DIFFERENCE FORMULA at the midpoint.

  At `x* = -1 + 1/(n-1)`, `x* - x_j = (1 - 2j)/(n-1)`. Combined with
  `x_i - x_j = 2(i-j)/(n-1)`, this is exactly what turns `lagrangeBasis_eval`
  into the explicit factorial ratio
  `|p_m(x*)| = (2n-3)!! / (|2m-1| · 2^(n-1) · m! · (n-1-m)!)`.
-/
theorem midPoint_sub_node (n : ℕ) (hn : n ≥ 2) (j : Fin n) :
    midPoint n - (equidistantNodes n hn).points j
      = (1 - 2 * (j.val : ℝ)) / ((n : ℝ) - 1) := by
  have hpts : (equidistantNodes n hn).points j = -1 + 2 * (j.val : ℝ) / ((n : ℝ) - 1) := rfl
  rw [hpts, midPoint]
  ring

/-- Difference of two equidistant nodes: `x_i - x_j = 2(i - j)/(n-1)`. -/
theorem node_sub_node (n : ℕ) (hn : n ≥ 2) (i j : Fin n) :
    (equidistantNodes n hn).points i - (equidistantNodes n hn).points j
      = 2 * ((i.val : ℝ) - (j.val : ℝ)) / ((n : ℝ) - 1) := by
  have hi : (equidistantNodes n hn).points i = -1 + 2 * (i.val : ℝ) / ((n : ℝ) - 1) := rfl
  have hj : (equidistantNodes n hn).points j = -1 + 2 * (j.val : ℝ) / ((n : ℝ) - 1) := rfl
  rw [hi, hj]
  ring

/--
  MIDPOINT BASIS TERM AS AN INTEGER RATIO PRODUCT.

  Substituting the two node-difference formulas into `abs_lagrangeBasis_eval`
  cancels the common `1/(n-1)` scale in every factor, leaving a product of purely
  *integer* ratios:
  `|p_m(x*)| = ∏_{j ≠ m} |2j - 1| / (2 · |m - j|)`.

  This is the key simplification: it removes ALL analytic / `(n-1)` structure, so
  the residual pointwise bound becomes a finite inequality about integers only.
  From here `∏_{j≠m} |2j-1| = (2n-3)!! / |2m-1|` and `∏_{j≠m} |m-j| = m!·(n-1-m)!`
  recover the factorial closed form, but the ratio product itself is already the
  cleanest object for the numeric estimate.
-/
theorem abs_lagrangeBasis_midPoint (n : ℕ) (hn : n ≥ 2) (m : Fin n) :
    |(lagrangeBasis (equidistantNodes n hn) m).eval (midPoint n)| =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).filter (fun k => k ≠ m),
        |2 * (j.val : ℝ) - 1| / (2 * |(m.val : ℝ) - (j.val : ℝ)|) := by
  have hn_cast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  rw [abs_lagrangeBasis_eval]
  apply Finset.prod_congr rfl
  intro j _
  rw [midPoint_sub_node n hn j, node_sub_node n hn m j]
  -- `|(1 - 2j)/(n-1)| / |2(m-j)/(n-1)| = |2j - 1| / (2 |m - j|)`
  have e1 : |(1 - 2 * (j.val : ℝ)) / ((n : ℝ) - 1)|
      = |2 * (j.val : ℝ) - 1| / ((n : ℝ) - 1) := by
    rw [abs_div, abs_of_pos hn1_pos, abs_sub_comm]
  have e2 : |2 * ((m.val : ℝ) - (j.val : ℝ)) / ((n : ℝ) - 1)|
      = 2 * |(m.val : ℝ) - (j.val : ℝ)| / ((n : ℝ) - 1) := by
    rw [abs_div, abs_of_pos hn1_pos, abs_mul, abs_two]
  rw [e1, e2, div_div_div_cancel_right₀ hn1_pos.ne']

/--
  POINTWISE LEBESGUE LOWER BOUND (the mathematical heart of `equidistant_diverges`).

  At the midpoint x* = -1 + 1/(n-1) of the first equidistant subinterval, the
  Lebesgue function already exceeds 2^(n-1)/n^2.

  The polynomial reduction is now fully discharged: `lebesgueFunction_ge_single`
  reduces the goal to producing a single index `m` whose basis term reaches the
  target, and `abs_lagrangeBasis_midPoint` rewrites that term as the integer
  ratio product `∏_{j≠m} |2j-1| / (2·|m-j|)`.

  The remaining sorry is therefore a PURE INTEGER inequality with NO analytic or
  `(n-1)` content: the existence of a central index `m ≈ ⌊(n-2)/2⌋` whose ratio
  product is `≥ 2^(n-1)/n^2`. Equivalently the factorial inequality
  `(2n-3)!! · n^2 ≥ |2m-1| · 2^(2n-2) · m! · (n-1-m)!`.
  Verified numerically for n = 2..25 (verify-equidistant-bound.py).
-/
theorem lebesgueFunction_midPoint_ge (n : ℕ) (hn : n ≥ 2) :
    lebesgueFunction (equidistantNodes n hn) (midPoint n) ≥ 2 ^ (n - 1) / (n : ℝ) ^ 2 := by
  -- Reduce to a single central index, then (via `abs_lagrangeBasis_midPoint`) to
  -- a pure integer-ratio inequality.
  obtain ⟨m, hm⟩ : ∃ m : Fin n,
      2 ^ (n - 1) / (n : ℝ) ^ 2
        ≤ |(lagrangeBasis (equidistantNodes n hn) m).eval (midPoint n)| := by
    obtain ⟨m, hm⟩ : ∃ m : Fin n,
        2 ^ (n - 1) / (n : ℝ) ^ 2 ≤
          ∏ j ∈ (Finset.univ : Finset (Fin n)).filter (fun k => k ≠ m),
            |2 * (j.val : ℝ) - 1| / (2 * |(m.val : ℝ) - (j.val : ℝ)|) := by
      sorry
    exact ⟨m, by rw [abs_lagrangeBasis_midPoint n hn m]; exact hm⟩
  exact le_trans hm (lebesgueFunction_ge_single _ _ m)

end Erdos671Orphan
