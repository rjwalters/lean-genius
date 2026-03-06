import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-
# Schauder Projection Lemma from First Principles (OQ-01)

## What This Proves

The Schauder projection lemma: Given a compact set K in a normed space E
and ε > 0, there exist finitely many points x₁,...,xₙ ∈ K and a continuous
map π : E → E such that:
1. Each xᵢ ∈ K
2. π is continuous
3. π maps K into convexHull ℝ {x₁,...,xₙ}
4. ‖π(x) - x‖ < ε for all x ∈ K

## Proof Strategy

The proof uses partition of unity:
1. Cover K by finitely many ε-balls (compactness)
2. Define bump functions φᵢ(x) = max(0, ε - ‖x - xᵢ‖)
3. The Schauder projection is π(x) = Σ φᵢ(x)·xᵢ / Σ φᵢ(x)
4. Prove continuity, convex hull membership, and ε-approximation

## Additional Results

- Convex hull of finite set is compact/closed
  (resolves a sorry in SchauderFixedPoint.lean)
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Set Metric Filter Finset

noncomputable section

namespace SchauderProjection

-- ============================================================
-- PART 1: Convex Hull Compactness
-- ============================================================

/-- The convex hull of a finite set in a normed space is closed. -/
theorem isClosed_convexHull_finite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset E} :
    IsClosed (convexHull ℝ (↑s : Set E)) :=
  s.finite_toSet.isClosed_convexHull

/-- The convex hull of a finite range is compact. -/
theorem isCompact_convexHull_of_finite_range {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (pts : Fin n → E) :
    IsCompact (convexHull ℝ (range pts)) :=
  (Set.finite_range pts).isCompact_convexHull

-- ============================================================
-- PART 2: Bump Function Infrastructure
-- ============================================================

/-- Bump function for a single center: φ(x) = max(0, ε - ‖x - c‖).
    This is continuous, nonneg, and positive iff x ∈ B(c, ε). -/
def bumpFn (c : E) (ε : ℝ) [NormedAddCommGroup E] : E → ℝ :=
  fun x => max 0 (ε - ‖x - c‖)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bumpFn_nonneg (c : E) (ε : ℝ) (x : E) : 0 ≤ bumpFn c ε x :=
  le_max_left 0 _

theorem bumpFn_continuous (c : E) (ε : ℝ) : Continuous (bumpFn c ε) := by
  unfold bumpFn
  apply Continuous.max continuous_const
  exact continuous_const.sub (continuous_norm.comp (continuous_id.sub continuous_const))

theorem bumpFn_pos_of_mem_ball (c : E) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : ‖x - c‖ < ε) :
    0 < bumpFn c ε x := by
  unfold bumpFn
  simp only [lt_max_iff]
  right
  linarith

theorem bumpFn_le_eps (c : E) (ε : ℝ) (hε : 0 ≤ ε) (x : E) : bumpFn c ε x ≤ ε := by
  unfold bumpFn
  exact max_le hε (by linarith [norm_nonneg (x - c)])

theorem bumpFn_eq_zero_of_not_mem_ball (c : E) (ε : ℝ) (x : E) (hx : ε ≤ ‖x - c‖) :
    bumpFn c ε x = 0 := by
  unfold bumpFn
  simp only [max_eq_left_iff]
  linarith

/-- When φᵢ(x) > 0, we have ‖x - cᵢ‖ < ε. -/
theorem norm_sub_lt_of_bumpFn_pos (c : E) (ε : ℝ) (x : E) (h : 0 < bumpFn c ε x) :
    ‖x - c‖ < ε := by
  by_contra hle
  push_neg at hle
  have h0 : bumpFn c ε x = 0 := bumpFn_eq_zero_of_not_mem_ball c ε x hle
  linarith

-- ============================================================
-- PART 3: Sum of Bumps and Positivity on K
-- ============================================================

/-- Sum of bump functions over a finite index set. -/
def bumpSum {n : ℕ} (pts : Fin n → E) (ε : ℝ) (x : E) : ℝ :=
  ∑ i : Fin n, bumpFn (pts i) ε x

theorem bumpSum_nonneg {n : ℕ} (pts : Fin n → E) (ε : ℝ) (x : E) :
    0 ≤ bumpSum pts ε x :=
  Finset.sum_nonneg fun i _ => bumpFn_nonneg (pts i) ε x

theorem bumpSum_continuous {n : ℕ} (pts : Fin n → E) (ε : ℝ) :
    Continuous (bumpSum pts ε) := by
  unfold bumpSum
  exact continuous_finset_sum _ fun i _ => bumpFn_continuous (pts i) ε

/-- If the ε-balls around pts cover x, then the bump sum is positive at x. -/
theorem bumpSum_pos_of_covered {n : ℕ} (pts : Fin n → E) (ε : ℝ) (hε : 0 < ε) (x : E)
    (hcov : ∃ i : Fin n, ‖x - pts i‖ < ε) : 0 < bumpSum pts ε x := by
  obtain ⟨i, hi⟩ := hcov
  calc 0 < bumpFn (pts i) ε x :=
        bumpFn_pos_of_mem_ball (pts i) ε hε x hi
    _ ≤ bumpSum pts ε x :=
        Finset.single_le_sum (fun j _ => bumpFn_nonneg (pts j) ε x) (Finset.mem_univ i)

-- ============================================================
-- PART 4: The Schauder Projection Map
-- ============================================================

/-- The Schauder projection: π(x) = Σᵢ φᵢ(x) · xᵢ / Σᵢ φᵢ(x).
    This is a weighted average of the centers, with weights proportional
    to the bump function values. -/
def schauderProj {n : ℕ} (pts : Fin n → E) (ε : ℝ) (x : E) : E :=
  (bumpSum pts ε x)⁻¹ • ∑ i : Fin n, bumpFn (pts i) ε x • pts i

-- ============================================================
-- PART 5: Properties of the Projection
-- ============================================================

/-- The Schauder projection is continuous on the set where bumpSum > 0. -/
theorem schauderProj_continuous_of_pos {n : ℕ} (pts : Fin n → E) (ε : ℝ)
    (U : Set E) (hU : ∀ x ∈ U, 0 < bumpSum pts ε x) :
    ContinuousOn (schauderProj pts ε) U := by
  unfold schauderProj
  apply ContinuousOn.smul
  · apply ContinuousOn.inv₀
    · exact (bumpSum_continuous pts ε).continuousOn
    · intro x hx; exact ne_of_gt (hU x hx)
  · apply continuousOn_finset_sum
    intro i _
    exact ((bumpFn_continuous (pts i) ε).smul continuous_const).continuousOn

/-- The projection maps into the convex hull of the centers.
    π(x) is a convex combination of pts when bumpSum > 0. -/
theorem schauderProj_mem_convexHull {n : ℕ} (pts : Fin n → E) (ε : ℝ) (x : E)
    (hpos : 0 < bumpSum pts ε x) :
    schauderProj pts ε x ∈ convexHull ℝ (range pts) := by
  -- Do NOT unfold schauderProj here (breaks later rw)
  set w := fun i => bumpFn (pts i) ε x / bumpSum pts ε x with hw_def
  have hsum_pos : (0 : ℝ) < bumpSum pts ε x := hpos
  have hsum_ne : bumpSum pts ε x ≠ 0 := ne_of_gt hsum_pos
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i; exact div_nonneg (bumpFn_nonneg (pts i) ε x) (le_of_lt hpos)
  have hw_sum : ∑ i : Fin n, w i = 1 := by
    simp only [hw_def, div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ hsum_ne
  have h_eq : schauderProj pts ε x = ∑ i : Fin n, w i • pts i := by
    unfold schauderProj
    rw [Finset.smul_sum]
    congr 1
    ext i
    simp [hw_def, div_eq_mul_inv, smul_smul]
    ring_nf
  rw [h_eq]
  exact (convex_convexHull ℝ (range pts)).sum_mem
    (fun i _ => hw_nonneg i) hw_sum
    (fun i _ => subset_convexHull ℝ (range pts) (Set.mem_range_self i))

/-- Key approximation: ‖π(x) - x‖ < ε when bumpSum > 0.
    Since π(x) is a weighted average of centers within distance < ε of x. -/
theorem schauderProj_close {n : ℕ} (pts : Fin n → E) (ε : ℝ) (hε : 0 < ε) (x : E)
    (hpos : 0 < bumpSum pts ε x) :
    ‖schauderProj pts ε x - x‖ < ε := by
  -- Do NOT unfold schauderProj here (breaks later rw)
  set S := bumpSum pts ε x with hS_def
  have hS_pos : 0 < S := hpos
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have h_rewrite : schauderProj pts ε x - x =
      S⁻¹ • ∑ i : Fin n, bumpFn (pts i) ε x • (pts i - x) := by
    have hexpand : ∑ i : Fin n, bumpFn (pts i) ε x • (pts i - x) =
        (∑ i : Fin n, bumpFn (pts i) ε x • pts i) - S • x := by
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib]
      congr 1
      exact (Finset.sum_smul (s := Finset.univ)).symm
    unfold schauderProj
    rw [hexpand, smul_sub, inv_smul_smul₀ hS_ne]
  rw [h_rewrite, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hS_pos))]
  rw [inv_mul_lt_iff₀ hS_pos]
  calc ‖∑ i : Fin n, bumpFn (pts i) ε x • (pts i - x)‖
      ≤ ∑ i : Fin n, ‖bumpFn (pts i) ε x • (pts i - x)‖ :=
        norm_sum_le _ _
    _ = ∑ i : Fin n, bumpFn (pts i) ε x * ‖pts i - x‖ := by
        congr 1; ext i
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bumpFn_nonneg (pts i) ε x)]
    _ < ∑ i : Fin n, bumpFn (pts i) ε x * ε := by
        apply Finset.sum_lt_sum
        · intro i _
          by_cases h : bumpFn (pts i) ε x = 0
          · simp [h]
          · have hpos_i := lt_of_le_of_ne (bumpFn_nonneg (pts i) ε x) (Ne.symm h)
            have h1 := norm_sub_lt_of_bumpFn_pos (pts i) ε x hpos_i
            rw [norm_sub_rev] at h1
            exact mul_le_mul_of_nonneg_left (le_of_lt h1) (le_of_lt hpos_i)
        · obtain ⟨j, hj⟩ := (show ∃ j : Fin n, 0 < bumpFn (pts j) ε x by
            by_contra hall
            push_neg at hall
            have : bumpSum pts ε x = 0 := Finset.sum_eq_zero fun i _ =>
              le_antisymm (hall i) (bumpFn_nonneg (pts i) ε x)
            linarith)
          exact ⟨j, Finset.mem_univ j, by
            have h1 := norm_sub_lt_of_bumpFn_pos (pts j) ε x hj
            rw [norm_sub_rev] at h1
            exact mul_lt_mul_of_pos_left h1 hj⟩
    _ = S * ε := by
        rw [← Finset.sum_mul, hS_def, bumpSum]

-- ============================================================
-- PART 6: Main Theorem - Schauder Projection Lemma
-- ============================================================

/-- **Schauder Projection Lemma** (Proved from first principles)

Given a compact set K in a normed space and ε > 0, there exist:
- Finitely many points x₁,...,xₙ ∈ K
- A continuous map π : E → E

such that π maps K into convexHull ℝ {x₁,...,xₙ} and ‖π(x) - x‖ < ε
for all x ∈ K.

**Proof**: By compactness, cover K by finitely many ε-balls centered at
points of K. Define π using a partition of unity with bump functions
φᵢ(x) = max(0, ε - ‖x - xᵢ‖). The map π(x) = Σ φᵢ(x)·xᵢ / Σ φᵢ(x)
is continuous (since the denominator is positive on K), maps into the
convex hull (it's a convex combination), and satisfies ‖π(x) - x‖ < ε
(since only nearby centers contribute). -/
theorem schauder_projection_lemma
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (pts : Fin n → E) (π : E → E),
      (∀ i, pts i ∈ K) ∧
      ContinuousOn π K ∧
      (∀ x ∈ K, π x ∈ convexHull ℝ (range pts)) ∧
      (∀ x ∈ K, ‖π x - x‖ < ε) := by
  -- Step 1: Cover K by finitely many ε-balls centered at points of K
  have hcov : K ⊆ ⋃ x ∈ K, Metric.ball x ε := by
    intro x hx
    exact mem_biUnion hx (Metric.mem_ball_self hε)
  -- Extract finite subcover by compactness
  obtain ⟨centers, hcenters_sub, hcenters_cover⟩ :=
    hK.elim_finite_subcover_image (fun x _ => isOpen_ball) hcov
  obtain ⟨hfin, hcover⟩ := hcenters_cover
  -- centers : Set E, hfin : centers.Finite, hcover : K ⊆ ⋃ i ∈ centers, ball i ε
  -- Get Fintype instance from Finite
  haveI : Fintype ↥centers := hfin.fintype
  -- Index by Fin N via equivalence
  classical
  obtain ⟨pts_equiv⟩ := Fintype.truncEquivFin ↥centers
  set N := Fintype.card ↥centers with hN_def
  set pts := fun (i : Fin N) => ((pts_equiv.symm i) : E) with hpts_def
  -- Covering property: for x ∈ K, some indexed point is within ε
  have hcov_pts : ∀ x ∈ K, ∃ i : Fin N, ‖x - pts i‖ < ε := by
    intro x hx
    have hmem := hcover hx
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨c, hc_mem, hc_ball⟩ := hmem
    refine ⟨pts_equiv ⟨c, hc_mem⟩, ?_⟩
    have hval : pts (pts_equiv ⟨c, hc_mem⟩) = c := by
      simp only [hpts_def, Equiv.symm_apply_apply, Subtype.coe_mk]
    rw [hval, ← dist_eq_norm]
    exact Metric.mem_ball.mp hc_ball
  -- bumpSum is positive on K
  have hpos_K : ∀ x ∈ K, 0 < bumpSum pts ε x := fun x hx =>
    bumpSum_pos_of_covered pts ε hε x (hcov_pts x hx)
  exact ⟨N, pts, schauderProj pts ε,
    fun i => hcenters_sub (pts_equiv.symm i).prop,
    schauderProj_continuous_of_pos pts ε K hpos_K,
    fun x hx => schauderProj_mem_convexHull pts ε x (hpos_K x hx),
    fun x hx => schauderProj_close pts ε hε x (hpos_K x hx)⟩

-- ============================================================
-- PART 7: Convex Hull Closedness (Resolves sorry in SchauderFixedPoint.lean)
-- ============================================================

/-- The convex hull of a finite set in a normed space is compact.
    This resolves the sorry at SchauderFixedPoint.lean:299. -/
theorem isCompact_convexHull_range {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (pts : Fin n → E) :
    IsCompact (convexHull ℝ (range pts)) :=
  (Set.finite_range pts).isCompact_convexHull

/-- The convex hull of the range of pts is closed. -/
theorem isClosed_convexHull_range {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (pts : Fin n → E) :
    IsClosed (convexHull ℝ (range pts)) :=
  (isCompact_convexHull_range pts).isClosed

end SchauderProjection
