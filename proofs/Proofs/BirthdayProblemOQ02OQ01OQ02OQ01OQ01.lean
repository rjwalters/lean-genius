import Mathlib

/-
# Schur-Convexity of the Collision Probability (Birthday OQ-02-OQ-01-OQ-02-OQ-01-OQ-01)

## What This Proves

The parent entry `birthday-problem-oq-02-oq-01-oq-02-oq-01`
(`BirthdayProblemOQ02OQ01OQ02OQ01.lean`) isolated the **local** smoothing step behind the
extremal theory of the two-draw **collision probability**

  `C(p) = ∑ᵢ pᵢ²`

of a probability vector `p`: replacing the values at two coordinates by their average
weakly decreases `C` (`smoothing_sum_sq_le`).  Its open question asks to **globalize** this
local Robin-Hood transfer into the full Schur-convexity statement

  `p` majorized by `q`  ⟹  `∑ pᵢ² ≤ ∑ qᵢ²`,

recovering both the parent's minimizer (uniform) and the concentration maximizer as the two
endpoints of the majorization order.

This file supplies that globalization in the **Hardy–Littlewood–Pólya** form of majorization.
By the HLP theorem, `p` is majorized by `q` (for probability vectors of equal sum) iff
`p = D q` for some **doubly stochastic** matrix `D`.  We prove the substantive content of
Schur-convexity directly in that form:

* `sum_sq_mulVec_le_of_mem_doublyStochastic`:
    if `D` is doubly stochastic then `∑ᵢ (D q)ᵢ² ≤ ∑ᵢ qᵢ²` — passing a vector through *any*
    averaging (doubly stochastic) operator can only **decrease** its sum of squares.

The proof is the one-line conceptual argument made rigorous: each output coordinate
`(D q)ᵢ = ∑ⱼ Dᵢⱼ qⱼ` is a genuine convex combination of the `qⱼ` (row `i` of `D` has
nonnegative entries summing to `1`), so by **Jensen's inequality** for the convex function
`x ↦ x²`, `(D q)ᵢ² ≤ ∑ⱼ Dᵢⱼ qⱼ²`.  Summing over `i` and using that the **columns** of `D`
also sum to `1` collapses `∑ᵢ ∑ⱼ Dᵢⱼ qⱼ²` back to `∑ⱼ qⱼ²`.

As a corollary we recover the parent chain's sharp **lower** endpoint:

* `one_div_card_le_sum_sq`:
    every probability vector satisfies `1/d ≤ ∑ᵢ qᵢ²`, with the uniform distribution
    attaining the minimum.  This is exactly the statement that the uniform vector
    `(1/d, …, 1/d) = J q` (where `J` is the all-`1/d` doubly stochastic matrix) is majorized
    by every probability vector, so its collision probability `1/d` is the smallest possible.

## Why This Is Not the Parent

The parent proves a *local* two-coordinate transfer inequality.  This entry proves the
*global* operator inequality `∑(Dq)² ≤ ∑q²` for every doubly stochastic `D` — the full
Schur-convexity of `∑ xᵢ²` in HLP form — and derives the uniform-minimizer endpoint from it.
Mathlib has the doubly-stochastic matrix API but no Schur-convexity / majorization theory;
this monotonicity-under-averaging statement is new here.  Everything is elementary (Jensen
for `x²` plus the row/column stochasticity of `D`) and axiom-free.
-/

open Finset Matrix

namespace BirthdaySchurConvexity

variable {d : ℕ}

/-! ## The global Schur-convexity inequality (doubly-stochastic / HLP form) -/

/-- **Schur-convexity of the sum of squares (Hardy–Littlewood–Pólya form).**

If `D` is a doubly stochastic matrix then `∑ᵢ (D q)ᵢ² ≤ ∑ᵢ qᵢ²`: averaging a vector through
any doubly stochastic operator can only decrease its sum of squares.  Combined with the HLP
characterization of majorization (`p` majorized by `q` ⟺ `p = D q` for doubly stochastic
`D`), this is the global Schur-convexity statement `p ≺ q ⟹ ∑ pᵢ² ≤ ∑ qᵢ²`. -/
theorem sum_sq_mulVec_le_of_mem_doublyStochastic
    {D : Matrix (Fin d) (Fin d) ℝ} (hD : D ∈ doublyStochastic ℝ (Fin d)) (q : Fin d → ℝ) :
    ∑ i, ((D *ᵥ q) i) ^ 2 ≤ ∑ i, (q i) ^ 2 := by
  -- `x ↦ x²` is convex on all of `ℝ`.
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := Even.convexOn_pow (by norm_num)
  -- Per-row Jensen bound: each output coordinate is a convex combination of the `qⱼ`.
  have hrow : ∀ i, ((D *ᵥ q) i) ^ 2 ≤ ∑ j, D i j * (q j) ^ 2 := by
    intro i
    have hmulvec : (D *ᵥ q) i = ∑ j, D i j • q j := by
      simp [Matrix.mulVec, dotProduct, smul_eq_mul]
    rw [hmulvec]
    have hjensen := hconv.map_sum_le (t := (Finset.univ : Finset (Fin d)))
      (w := fun j => D i j) (p := q)
      (fun j _ => nonneg_of_mem_doublyStochastic hD)
      (sum_row_of_mem_doublyStochastic hD i)
      (fun j _ => Set.mem_univ _)
    simpa [smul_eq_mul] using hjensen
  -- Sum over rows, then collapse using that the columns of `D` sum to `1`.
  calc ∑ i, ((D *ᵥ q) i) ^ 2
      ≤ ∑ i, ∑ j, D i j * (q j) ^ 2 := Finset.sum_le_sum (fun i _ => hrow i)
    _ = ∑ j, (∑ i, D i j) * (q j) ^ 2 := by
        rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul]
    _ = ∑ j, (q j) ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [sum_col_of_mem_doublyStochastic hD j, one_mul]

/-! ## Recovering the uniform-minimizer endpoint -/

/-- The all-`1/d` matrix is doubly stochastic (for `d ≥ 1`). -/
theorem uniformAveraging_mem_doublyStochastic (hd : 0 < d) :
    (Matrix.of (fun _ _ : Fin d => (d : ℝ)⁻¹)) ∈ doublyStochastic ℝ (Fin d) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => inv_nonneg.mpr (Nat.cast_nonneg d), fun i => ?_, fun j => ?_⟩ <;>
    · simp only [Matrix.of_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp

/-- **Uniform distribution minimizes the collision probability.**

Every probability vector `q` on `d` outcomes satisfies `1/d ≤ ∑ᵢ qᵢ²`.  This is the
majorization endpoint: the uniform vector `(1/d, …, 1/d) = J q` (with `J` the doubly
stochastic all-`1/d` matrix) is majorized by every probability vector, so its collision
probability `1/d` is smallest.  Recovers the parent chain's sharp lower bound from the global
Schur-convexity inequality. -/
theorem one_div_card_le_sum_sq (hd : 0 < d) (q : Fin d → ℝ) (hsum : ∑ i, q i = 1) :
    1 / (d : ℝ) ≤ ∑ i, (q i) ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set J : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun _ _ : Fin d => (d : ℝ)⁻¹) with hJ
  -- `J q` is the constant uniform vector `1/d`.
  have hJq : ∀ i, (J *ᵥ q) i = (d : ℝ)⁻¹ := by
    intro i
    have : (J *ᵥ q) i = ∑ j, (d : ℝ)⁻¹ * q j := by
      simp [hJ, Matrix.mulVec, dotProduct]
    rw [this, ← Finset.mul_sum, hsum, mul_one]
  -- Apply the global inequality to `J`.
  have hmain := sum_sq_mulVec_le_of_mem_doublyStochastic
    (uniformAveraging_mem_doublyStochastic hd) q
  -- The left side equals `1/d`.
  have hlhs : ∑ i, ((J *ᵥ q) i) ^ 2 = 1 / (d : ℝ) := by
    simp only [hJq]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rwa [hlhs] at hmain

end BirthdaySchurConvexity
