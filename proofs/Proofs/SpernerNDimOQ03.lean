import Mathlib
import Proofs.SpernerNDim

/-
# Brouwer Fixed Point via Displacement Coloring (n-dimensional)

Connects the n-dimensional Sperner's lemma (SpernerNDim.lean) to the
Brouwer fixed point theorem through the displacement coloring construction.

Given f : Δ^d → Δ^d continuous with no fixed point, the displacement coloring
assigns each grid vertex the index of the most negative barycentric displacement.
This satisfies Sperner's boundary condition, so Sperner's lemma yields a
fully-colored simplex. As mesh refines, these yield approximate fixed points
converging to an exact one.

Main results:
- displacementColoring_isSperner: displacement coloring satisfies Sperner condition
- approximate_fixed_point: ε-approximate fixed points via Sperner's lemma
- brouwer_simplex: Brouwer fixed point theorem for the standard simplex

Generalizes the 2D displacement coloring in BrouwerFixedPointOQ02OQ01.lean
to arbitrary dimension d, using the SpernerNDim infrastructure.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace DisplacementBrouwer

open Finset BigOperators SpernerNDim

-- ============================================================
-- SECTION I: Simplex Geometry
-- ============================================================

/-- Map a grid vertex to real coordinates in [0,1]^d via v ↦ v/N. -/
noncomputable def gridToReal {d N : ℕ} (v : Vertex d N) : Fin d → ℝ :=
  fun i => (v.coords i : ℝ) / (N : ℝ)

/-- A point lies in the standard d-simplex: all coordinates ≥ 0, sum ≤ 1. -/
def InSimplex (d : ℕ) (x : Fin d → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1

/-- Grid vertices map into the simplex when N > 0. -/
lemma gridToReal_inSimplex {d N : ℕ} (hN : 0 < N) (v : Vertex d N) :
    InSimplex d (gridToReal v) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  refine ⟨fun i => div_nonneg (Nat.cast_nonneg _) hN_pos.le, ?_⟩
  simp only [gridToReal, ← Finset.sum_div]
  rw [div_le_one hN_pos]
  exact_mod_cast v.valid

-- ============================================================
-- SECTION II: Barycentric Displacement
-- ============================================================

/-- Barycentric displacement of f at grid point v.
    For k < d: d_k = f(v/N)_k - v_k/N  (explicit coordinates)
    For k = d: d_d = -(Σ d_k)  (from the implicit last barycentric coordinate)

    The d+1 displacements correspond to changes in barycentric coordinates:
    λ_k(f(p)) - λ_k(p) where λ_k are barycentric coordinates on Δ^d. -/
noncomputable def baryDisp {d N : ℕ} (f : (Fin d → ℝ) → (Fin d → ℝ))
    (v : Vertex d N) : Fin (d + 1) → ℝ := fun k =>
  if h : (k : ℕ) < d then
    f (gridToReal v) ⟨k, h⟩ - gridToReal v ⟨k, h⟩
  else
    -(∑ i : Fin d, (f (gridToReal v) i - gridToReal v i))

/-- Barycentric displacements sum to zero (barycentric coordinates
    sum to 1, so their increments sum to 0). -/
lemma baryDisp_sum_zero {d N : ℕ} (f : (Fin d → ℝ) → (Fin d → ℝ))
    (v : Vertex d N) :
    ∑ k : Fin (d + 1), baryDisp f v k = 0 := by
  rw [Fin.sum_univ_castSucc]
  have hcast : ∀ i : Fin d, baryDisp f v (Fin.castSucc i) =
      f (gridToReal v) i - gridToReal v i := by
    intro i; simp only [baryDisp, Fin.coe_castSucc, dif_pos i.isLt, Fin.eta]
  have hlast : baryDisp f v (Fin.last d) =
      -(∑ i : Fin d, (f (gridToReal v) i - gridToReal v i)) := by
    simp only [baryDisp, Fin.val_last, dif_neg (lt_irrefl d)]
  simp_rw [hcast]; rw [hlast, add_neg_cancel]

-- Algebra helper: ∑ (a - b) = ∑ a - ∑ b
private lemma sum_sub_eq {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    ∑ i, (a i - b i) = (∑ i, a i) - (∑ i, b i) := by
  simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

-- ============================================================
-- SECTION III: Index Minimizer
-- ============================================================

/-- Choose an index minimizing f on Fin (n+1). -/
noncomputable def minIndex {n : ℕ} (f : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  (Finset.exists_min_image Finset.univ f Finset.univ_nonempty).choose

/-- The chosen index achieves the minimum value. -/
lemma minIndex_le {n : ℕ} (f : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    f (minIndex f) ≤ f j :=
  (Finset.exists_min_image Finset.univ f Finset.univ_nonempty).choose_spec.2 j
    (Finset.mem_univ _)

-- ============================================================
-- SECTION IV: Displacement Coloring
-- ============================================================

/-- The displacement coloring: color each grid vertex with the index
    of the most negative barycentric displacement component.

    This is the standard construction connecting Sperner's lemma
    to Brouwer's fixed point theorem: on face k, d_k ≥ 0 (the k-th
    barycentric coordinate of v is 0 while f(v)'s is ≥ 0), so k
    is never the minimizer, ensuring the Sperner boundary condition. -/
noncomputable def displacementColoring {d N : ℕ} (_ : 0 < N)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) : Coloring d N :=
  fun v => minIndex (baryDisp f v)

-- ============================================================
-- SECTION V: Sperner Boundary Condition
-- ============================================================

/-- On face k (k < d): d_k ≥ 0.
    Face k means v's k-th coordinate is 0. Since f maps Δ → Δ,
    f(v/N)_k ≥ 0. So d_k = f(v/N)_k - 0 ≥ 0. -/
lemma baryDisp_nonneg_on_face_lt {d N : ℕ} (hN : 0 < N)
    (f : (Fin d → ℝ) → (Fin d → ℝ))
    (hf : ∀ x, InSimplex d x → InSimplex d (f x))
    (v : Vertex d N) {k : Fin (d + 1)} (hk : (k : ℕ) < d)
    (hface : v.coords ⟨k, hk⟩ = 0) :
    0 ≤ baryDisp f v k := by
  simp only [baryDisp, dif_pos hk]
  have : gridToReal v ⟨k, hk⟩ = 0 := by
    simp only [gridToReal, hface, Nat.cast_zero, zero_div]
  rw [this, sub_zero]
  exact (hf _ (gridToReal_inSimplex hN v)).1 ⟨k, hk⟩

/-- On face d: d_d ≥ 0.
    Face d means Σ v_i = N, so the last barycentric coordinate of v/N is 0.
    Since f maps Δ → Δ, Σ f(v/N)_i ≤ 1, so d_d = 1 - Σ f_i ≥ 0. -/
lemma baryDisp_nonneg_on_face_last {d N : ℕ} (hN : 0 < N)
    (f : (Fin d → ℝ) → (Fin d → ℝ))
    (hf : ∀ x, InSimplex d x → InSimplex d (f x))
    (v : Vertex d N) {k : Fin (d + 1)} (hk : ¬ (k : ℕ) < d)
    (hface : ∑ i, v.coords i = N) :
    0 ≤ baryDisp f v k := by
  simp only [baryDisp, dif_neg hk]
  rw [neg_nonneg, sum_sub_eq]
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hfv := hf _ (gridToReal_inSimplex hN v)
  have hsum_v : ∑ i, gridToReal v i = 1 := by
    simp only [gridToReal, ← Finset.sum_div]
    rw [show (∑ i, (v.coords i : ℝ)) = (N : ℝ) from by exact_mod_cast hface,
        div_self (ne_of_gt hN_pos)]
  linarith [hfv.2]

/-- When f(v) ≠ v, some barycentric displacement is negative.
    All displacements sum to 0 and are not all zero, so some must be < 0. -/
lemma exists_neg_baryDisp {d N : ℕ} (hN : 0 < N)
    (f : (Fin d → ℝ) → (Fin d → ℝ))
    (v : Vertex d N)
    (hne : f (gridToReal v) ≠ gridToReal v) :
    ∃ j : Fin (d + 1), baryDisp f v j < 0 := by
  by_contra hall; push_neg at hall
  -- All displacements ≥ 0 and sum to 0 → all = 0
  have hzero : ∀ j : Fin (d + 1), baryDisp f v j = 0 := by
    intro j
    exact le_antisymm
      (by linarith [Finset.single_le_sum (f := fun k => baryDisp f v k)
            (fun i _ => hall i) (Finset.mem_univ j),
          baryDisp_sum_zero f v])
      (hall j)
  -- All explicit displacements 0 → f(v/N) = v/N
  have heq : f (gridToReal v) = gridToReal v := by
    ext i
    have h := hzero (Fin.castSucc i)
    simp only [baryDisp, Fin.coe_castSucc, dif_pos i.isLt, Fin.eta] at h
    linarith
  exact hne heq

/-- **Displacement coloring satisfies the Sperner boundary condition.**

    On face k of the standard d-simplex, the k-th barycentric displacement
    d_k ≥ 0. Since f(v) ≠ v (no grid fixed point), some displacement d_j < 0.
    The minimizer therefore satisfies: d_{min} ≤ d_j < 0 ≤ d_k,
    so min ≠ k, and color k is never assigned on face k. -/
theorem displacementColoring_isSperner {d N : ℕ} (hN : 0 < N)
    (f : (Fin d → ℝ) → (Fin d → ℝ))
    (hf : ∀ x, InSimplex d x → InSimplex d (f x))
    (hno_fix : ∀ v : Vertex d N, f (gridToReal v) ≠ gridToReal v) :
    IsSperner (displacementColoring hN f) := by
  intro v k hface
  -- Step 1: d_k ≥ 0 on face k
  have hdk : 0 ≤ baryDisp f v k := by
    simp only [onFace] at hface
    split_ifs at hface with hlt
    · exact baryDisp_nonneg_on_face_lt hN f hf v hlt hface
    · exact baryDisp_nonneg_on_face_last hN f hf v hlt hface
  -- Step 2: some displacement is strictly negative (f(v) ≠ v)
  obtain ⟨j, hj⟩ := exists_neg_baryDisp hN f v (hno_fix v)
  -- Step 3: argmin ≠ k (argmin value ≤ d_j < 0 ≤ d_k)
  show minIndex (baryDisp f v) ≠ k
  intro heq
  have hmin := minIndex_le (baryDisp f v) j
  rw [heq] at hmin
  linarith

-- ============================================================
-- SECTION VI: Approximate Fixed Points
-- ============================================================

/-- Approximate fixed points via Sperner's lemma and displacement coloring.

    For any ε > 0, there exists a point in the simplex that is an
    ε-approximate fixed point of f.

    Proof sketch: Choose N with mesh 1/N < δ(ε) (from uniform continuity
    of f on the compact simplex). Either:
    (a) f fixes some grid vertex exactly → done, or
    (b) No grid fixed point → displacement coloring is Sperner →
        Sperner gives fully-colored simplex → transfer displacement
        bounds between vertices of different colors → all barycentric
        displacements at any vertex are O(1/N) → approximate fixed point.

    The full argument generalizes approximate_fixed_point_2d in
    BrouwerFixedPointOQ02OQ01.lean (lines 922-1071) from 3 to d+1
    colors/components: for each color k, vertex v_k has d_k(v_k) ≤ 0.
    By UC + mesh bounds, d_k(v_0) ≤ C/N for all k. Since Σ d_k = 0
    and each d_k ≤ C/N, we get -dC/N ≤ d_k ≤ C/N, so ‖f(v_0)-v_0‖ → 0. -/
theorem approximate_fixed_point {d : ℕ} (hd : 0 < d)
    (f : (Fin d → ℝ) → (Fin d → ℝ))
    (hcont : Continuous f)
    (hf : ∀ x, InSimplex d x → InSimplex d (f x))
    (sperner : ∀ (N : ℕ) (hN : 0 < N) (c : Coloring d N),
      IsSperner c → ∃ S : FSimplex d N, IsFC c S)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Fin d → ℝ, InSimplex d x ∧ ∀ i : Fin d, |f x i - x i| < ε := by
  sorry

-- ============================================================
-- SECTION VII: Brouwer Fixed Point Theorem
-- ============================================================

/-- **Brouwer Fixed Point Theorem for the standard d-simplex.**

    Every continuous self-map of the d-simplex has a fixed point.

    Proof: For each n, approximate_fixed_point gives x_n with
    |f(x_n)_i - (x_n)_i| < 1/n. Since the simplex is compact,
    {x_n} has a convergent subsequence x_{n_k} → x*. By continuity,
    f(x_{n_k}) → f(x*). Since |f(x_{n_k}) - x_{n_k}| → 0,
    we get f(x*) = x*. -/
theorem brouwer_simplex {d : ℕ} (hd : 0 < d)
    (f : (Fin d → ℝ) → (Fin d → ℝ))
    (hcont : Continuous f)
    (hf : ∀ x, InSimplex d x → InSimplex d (f x))
    (sperner : ∀ (N : ℕ) (hN : 0 < N) (c : Coloring d N),
      IsSperner c → ∃ S : FSimplex d N, IsFC c S) :
    ∃ x : Fin d → ℝ, InSimplex d x ∧ f x = x := by
  sorry

end DisplacementBrouwer
