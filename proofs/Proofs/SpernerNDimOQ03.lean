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
-- SECTION VI: Infrastructure for Main Theorems
-- ============================================================

/-- countPerm values are 0 or 1 (permutation is injective). -/
private lemma countPerm_le_one {d : ℕ} (σ : Equiv.Perm (Fin d)) (k : ℕ) (j : Fin d) :
    countPerm σ k j ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact σ.injective (ha.2.trans hb.2.symm)

/-- Grid vertices map into the unit cube [0,1]^d. -/
private lemma gridToReal_mem_cube {d N : ℕ} (hN : 0 < N) (v : Vertex d N) :
    gridToReal v ∈ Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
  intro i _
  have hv := gridToReal_inSimplex hN v
  exact ⟨hv.1 i, le_trans (Finset.single_le_sum (fun j _ => hv.1 j)
    (Finset.mem_univ i)) hv.2⟩

/-- FSimplex vertices have L∞ distance ≤ 1/N.
    Each coordinate differs by at most 1 (in ℕ), hence ≤ 1/N (in ℝ). -/
private lemma fsimplex_gridToReal_dist {d N : ℕ} (hN : 0 < N)
    (S : FSimplex d N) (k₁ k₂ : Fin (d + 1)) :
    dist (gridToReal (S.vertex k₁)) (gridToReal (S.vertex k₂)) ≤ 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [dist_pi_le_iff (by positivity)]
  intro i
  simp only [gridToReal, FSimplex.vertex, Real.dist_eq]
  rw [show (↑(S.base i + countPerm S.perm k₁.val i) : ℝ) / ↑N -
    ↑(S.base i + countPerm S.perm k₂.val i) / ↑N =
    ((↑(countPerm S.perm k₁.val i) : ℝ) - ↑(countPerm S.perm k₂.val i)) / ↑N
    from by push_cast; ring]
  rw [abs_div, abs_of_pos hN']
  apply div_le_div_of_nonneg_right _ hN'.le
  have h1 := countPerm_le_one S.perm k₁.val i
  have h2 := countPerm_le_one S.perm k₂.val i
  rw [abs_le]
  constructor
  · have : (↑(countPerm S.perm k₂.val i) : ℝ) ≤ 1 := by exact_mod_cast h2
    linarith [Nat.cast_nonneg (countPerm S.perm k₁.val i)]
  · have : (↑(countPerm S.perm k₁.val i) : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith [Nat.cast_nonneg (countPerm S.perm k₂.val i)]

-- ============================================================
-- SECTION VII: Approximate Fixed Points
-- ============================================================

/-- Approximate fixed points via Sperner's lemma and displacement coloring.

    For any ε > 0, there exists a point in the simplex that is an
    ε-approximate fixed point of f.

    The proof picks the color-(last d) vertex of the FC simplex, which
    has ∑(f_j - p_j) ≥ 0. Transfer from each color-(castSucc j) vertex
    gives f(p)_j - p_j ≤ C. Combined: |f(p)_j - p_j| ≤ max(C, (d-1)C) < ε. -/
theorem approximate_fixed_point {d : ℕ} (hd : 0 < d)
    (f : (Fin d → ℝ) → (Fin d → ℝ))
    (hcont : Continuous f)
    (hf : ∀ x, InSimplex d x → InSimplex d (f x))
    (sperner : ∀ (N : ℕ) (hN : 0 < N) (c : Coloring d N),
      IsSperner c → ∃ S : FSimplex d N, IsFC c S)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Fin d → ℝ, InSimplex d x ∧ ∀ i : Fin d, |f x i - x i| < ε := by
  -- Step 1: Uniform continuity of f on the compact cube [0,1]^d
  set cube := Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) with cube_def
  have hcube_compact : IsCompact cube := isCompact_univ_pi (fun _ => isCompact_Icc)
  have huc := Metric.uniformContinuousOn_iff.mp
    (hcube_compact.uniformContinuousOn_of_continuous hcont.continuousOn)
  -- Get δ for tolerance ε / (2*(d+1))
  have hε' : 0 < ε / (2 * (↑d + 1)) := by positivity
  obtain ⟨δ, hδ_pos, hδ⟩ := huc (ε / (2 * (↑d + 1))) hε'
  -- Step 2: Choose N large enough
  obtain ⟨N, hN_gt⟩ := exists_nat_gt (max ((2 * (↑d + 1)) / ε) (1 / δ))
  have hN_pos : 0 < N := by
    by_contra h; push_neg at h
    have hN0 : N = 0 := by omega
    subst hN0; simp only [Nat.cast_zero] at hN_gt
    linarith [le_max_right ((2 * (↑d + 1)) / ε) (1 / δ), div_pos one_pos hδ_pos]
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
  -- Key bounds: 1/N < ε/(2*(d+1)) and 1/N < δ
  have h_inv_N : 1 / (N : ℝ) < ε / (2 * (↑d + 1)) := by
    have h1 : (2 * (↑d + 1)) / ε < ↑N := lt_of_le_of_lt (le_max_left _ _) hN_gt
    rw [div_lt_iff hε] at h1
    rw [div_lt_div_iff hN' (by positivity : (0 : ℝ) < 2 * (↑d + 1)), one_mul]
    nlinarith [mul_comm ε (↑N : ℝ)]
  have h_inv_δ : 1 / (N : ℝ) < δ := by
    have h1 : 1 / δ < ↑N := lt_of_le_of_lt (le_max_right _ _) hN_gt
    rw [div_lt_iff hδ_pos] at h1
    rw [div_lt_iff hN']
    linarith [mul_comm δ (↑N : ℝ)]
  -- Step 3: Grid fixed point case
  by_cases hgfp : ∃ v : Vertex d N, f (gridToReal v) = gridToReal v
  · obtain ⟨v, hv⟩ := hgfp
    exact ⟨gridToReal v, gridToReal_inSimplex hN_pos v, fun i => by
      simp only [hv, sub_self, abs_zero]; exact hε⟩
  · -- Step 4: No grid fixed point → displacement coloring is Sperner
    push_neg at hgfp
    have hSp := displacementColoring_isSperner hN_pos f hf hgfp
    obtain ⟨S, hFC⟩ := sperner N hN_pos _ hSp
    -- Step 5: Extract color-(last d) vertex as approximate fixed point
    obtain ⟨i_last, hi_last⟩ := hFC (Fin.last d)
    set v₀ := S.vertex i_last with hv₀_def
    -- v₀ has color (last d), so ∑(f_j - p_j) > 0
    have hcolor : minIndex (baryDisp f v₀) = Fin.last d := by
      show displacementColoring hN_pos f v₀ = Fin.last d; exact hi_last
    have hsum_pos : 0 < ∑ j : Fin d, (f (gridToReal v₀) j - gridToReal v₀ j) := by
      obtain ⟨k, hk⟩ := exists_neg_baryDisp hN_pos f v₀ (hgfp v₀)
      have hmin := minIndex_le (baryDisp f v₀) k
      rw [hcolor] at hmin
      have : baryDisp f v₀ (Fin.last d) < 0 := lt_of_le_of_lt hmin hk
      simp only [baryDisp, Fin.val_last, dif_neg (lt_irrefl d)] at this
      linarith
    -- Step 6: Upper bound for each coordinate displacement
    -- For each j < d, color-(castSucc j) vertex has displacement_j ≤ 0
    -- Transfer gives displacement_j at v₀ < ε/(d+1)
    have hupper : ∀ j : Fin d,
        f (gridToReal v₀) j - gridToReal v₀ j < ε / (↑d + 1) := by
      intro j
      obtain ⟨i_j, hi_j⟩ := hFC (Fin.castSucc j)
      set v_j := S.vertex i_j
      -- At v_j: displacement_j ≤ 0
      have hdisp_neg : f (gridToReal v_j) j - gridToReal v_j j ≤ 0 := by
        have hne := hgfp v_j
        obtain ⟨k, hk⟩ := exists_neg_baryDisp hN_pos f v_j hne
        have hmin_j : minIndex (baryDisp f v_j) = Fin.castSucc j := by
          show displacementColoring hN_pos f v_j = Fin.castSucc j; exact hi_j
        have := minIndex_le (baryDisp f v_j) k
        rw [hmin_j] at this
        have hbd : baryDisp f v_j (Fin.castSucc j) ≤ 0 :=
          le_of_lt (lt_of_le_of_lt this hk)
        simp only [baryDisp, Fin.coe_castSucc, dif_pos j.isLt, Fin.eta] at hbd
        linarith
      -- Mesh + UC transfer
      have hmesh := fsimplex_gridToReal_dist hN_pos S i_last i_j
      have hv₀_cube := gridToReal_mem_cube hN_pos v₀
      have hvj_cube := gridToReal_mem_cube hN_pos v_j
      have hf_close : dist (f (gridToReal v₀)) (f (gridToReal v_j)) <
          ε / (2 * (↑d + 1)) :=
        hδ _ hv₀_cube _ hvj_cube (lt_of_le_of_lt hmesh h_inv_δ)
      -- Component bounds from L∞ distance
      have hf_j : |f (gridToReal v₀) j - f (gridToReal v_j) j| <
          ε / (2 * (↑d + 1)) :=
        lt_of_le_of_lt ((Real.dist_eq _ _) ▸ dist_le_pi_dist _ _ j) hf_close
      have hp_j : |gridToReal v_j j - gridToReal v₀ j| ≤ 1 / (↑N : ℝ) :=
        (Real.dist_eq _ _) ▸ dist_le_pi_dist _ _ j |>.trans
          (fsimplex_gridToReal_dist hN_pos S i_j i_last)
      -- Transfer: f(p₀)_j - p₀_j < UC_bound + mesh_bound ≤ ε/(d+1)
      calc f (gridToReal v₀) j - gridToReal v₀ j
          = (f (gridToReal v₀) j - f (gridToReal v_j) j) +
            (f (gridToReal v_j) j - gridToReal v_j j) +
            (gridToReal v_j j - gridToReal v₀ j) := by ring
        _ ≤ |f (gridToReal v₀) j - f (gridToReal v_j) j| + 0 +
            |gridToReal v_j j - gridToReal v₀ j| := by
          gcongr
          · exact le_abs_self _
          · exact hdisp_neg
          · exact le_abs_self _
        _ < ε / (2 * (↑d + 1)) + 0 + ε / (2 * (↑d + 1)) := by
          linarith [lt_of_le_of_lt hp_j h_inv_N]
        _ = ε / (↑d + 1) := by ring
    -- Step 7: Lower bound from sum condition
    -- ∑(f_j - p_j) > 0 and each < ε/(d+1) → each > -ε
    have hlower : ∀ j : Fin d, -(ε : ℝ) < f (gridToReal v₀) j - gridToReal v₀ j := by
      intro j
      have hsub : f (gridToReal v₀) j - gridToReal v₀ j =
        (∑ k, (f (gridToReal v₀) k - gridToReal v₀ k)) -
        ∑ k in Finset.univ.erase j, (f (gridToReal v₀) k - gridToReal v₀ k) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]; ring
      rw [hsub]
      -- ∑_others ≤ d * ε/(d+1) < ε, and ∑_all > 0, so f_j - p_j > 0 - ε = -ε
      have hother : ∑ k in Finset.univ.erase j,
          (f (gridToReal v₀) k - gridToReal v₀ k) ≤
          ↑d * (ε / (↑d + 1)) := by
        calc ∑ k in Finset.univ.erase j,
              (f (gridToReal v₀) k - gridToReal v₀ k)
            ≤ ∑ k in Finset.univ.erase j, (ε / (↑d + 1)) :=
              Finset.sum_le_sum (fun k _ => le_of_lt (hupper k))
          _ ≤ ∑ _ in (Finset.univ : Finset (Fin d)), (ε / (↑d + 1)) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                (fun _ _ _ => div_nonneg hε.le
                  (by linarith [Nat.cast_nonneg d]))
          _ = ↑d * (ε / (↑d + 1)) := by
              simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
      have hd_bound : ↑d * (ε / (↑d + 1)) < ε := by
        rw [mul_div_assoc, div_lt_iff (by linarith [Nat.cast_nonneg d] : (0:ℝ) < ↑d + 1)]
        linarith
      linarith
    -- Step 8: Combine upper and lower bounds
    exact ⟨gridToReal v₀, gridToReal_inSimplex hN_pos v₀, fun j => by
      rw [abs_lt]; exact ⟨hlower j, lt_of_lt_of_le (hupper j)
        (div_le_self hε.le (by linarith [Nat.cast_nonneg d]))⟩⟩

-- ============================================================
-- SECTION VIII: Brouwer Fixed Point Theorem
-- ============================================================

/-- **Brouwer Fixed Point Theorem for the standard d-simplex.**

    Every continuous self-map of the d-simplex has a fixed point.

    Proof: The displacement function g(x) = dist(f(x), x) is continuous
    and achieves its minimum m on the compact simplex. If m > 0, then
    approximate_fixed_point with ε = m gives a point with g(y) < m,
    contradicting minimality. So m = 0 and the minimizer is a fixed point. -/
theorem brouwer_simplex {d : ℕ} (hd : 0 < d)
    (f : (Fin d → ℝ) → (Fin d → ℝ))
    (hcont : Continuous f)
    (hf : ∀ x, InSimplex d x → InSimplex d (f x))
    (sperner : ∀ (N : ℕ) (hN : 0 < N) (c : Coloring d N),
      IsSperner c → ∃ S : FSimplex d N, IsFC c S) :
    ∃ x : Fin d → ℝ, InSimplex d x ∧ f x = x := by
  -- The simplex is compact and nonempty
  have hK : IsCompact {x : Fin d → ℝ | InSimplex d x} := by
    apply IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ => isCompact_Icc))
    · have heq : {x : Fin d → ℝ | InSimplex d x} =
          (⋂ i, {x | (0 : ℝ) ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
        ext x; simp [InSimplex, Set.mem_iInter]
      rw [heq]
      exact (isClosed_iInter fun i =>
        isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i)
          continuous_const)
    · intro x ⟨hnn, hsum⟩
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
      exact fun i => ⟨hnn i, le_trans
        (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)) hsum⟩
  have hKne : Set.Nonempty {x : Fin d → ℝ | InSimplex d x} :=
    ⟨0, fun _ => le_refl 0, by simp⟩
  -- dist(f(·), ·) achieves its minimum on the compact simplex
  obtain ⟨x₀, hx₀_mem, hx₀_min⟩ :=
    hK.exists_forall_le hKne (hcont.dist continuous_id).continuousOn
  -- The minimum is 0 (otherwise approximate_fixed_point contradicts)
  suffices h : dist (f x₀) x₀ = 0 from
    ⟨x₀, hx₀_mem, dist_eq_zero.mp h⟩
  by_contra h
  have hpos : 0 < dist (f x₀) x₀ :=
    lt_of_le_of_ne dist_nonneg (Ne.symm h)
  obtain ⟨y, hy_mem, hy_bound⟩ :=
    approximate_fixed_point hd f hcont hf sperner (dist (f x₀) x₀) hpos
  have hlt : dist (f y) y < dist (f x₀) x₀ := by
    rw [dist_pi_lt_iff hpos]
    exact fun i => by rw [Real.dist_eq]; exact hy_bound i
  linarith [hx₀_min hy_mem]

end DisplacementBrouwer
