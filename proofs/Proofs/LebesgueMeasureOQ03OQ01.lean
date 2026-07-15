import Mathlib
import Proofs.LebesgueMeasureOQ03

/-!
# Lebesgue Measure OQ-03-OQ-01: Impossibility of Translation-Invariant Measures

Formalizes the impossibility theorem: there is no nonzero, translation-invariant,
locally finite Borel measure on an infinite-dimensional Hilbert space.

## Proof Strategy

Let H be an infinite-dimensional Hilbert space with orthonormal sequence {eₙ}.
Suppose μ is translation-invariant with μ(B(0, 4/3)) < ∞.

1. Balls B(eₙ, 1/3) are pairwise disjoint — distance ‖eₙ - eₘ‖ = √2 > 2/3
2. Each B(eₙ, 1/3) ⊆ B(0, 4/3) — since ‖eₙ‖ = 1
3. Translation invariance: μ(B(eₙ, 1/3)) = μ(B(0, 1/3)) for all n
4. Countable additivity: N · μ(B(0, 1/3)) ≤ μ(B(0, 4/3)) < ∞ for all N
5. Archimedean property in ℝ≥0∞ → μ(B(0, 1/3)) = 0

## Key Results

1. `ennreal_const_le_finite_imp_zero` — Archimedean property for ℝ≥0∞
2. `zero_measure_of_infinite_disjoint` — core measure theory lemma
3. `no_invariant_locally_finite_ball` — main impossibility theorem
4. `no_invariant_locally_finite_any_center` — corollary for any center

## References

- Parent file: `LebesgueMeasureOQ03.lean` (orthonormal_dist, orthonormal_balls_disjoint)
-/

namespace LebesgueMeasureOQ03OQ01

open MeasureTheory Set Metric Real LebesgueMeasureOQ03
open scoped InnerProductSpace ENNReal

-- ============================================================
-- Part I: ENNReal Archimedean Lemma
-- ============================================================

/-- If N * c ≤ M for all N : ℕ and M < ⊤, then c = 0.
    This is the ENNReal Archimedean property: no positive constant
    can be bounded above by a finite value under repeated addition. -/
lemma ennreal_const_le_finite_imp_zero (c M : ℝ≥0∞) (hM : M < ⊤) (hbdd : ∀ N : ℕ, ↑N * c ≤ M) :
    c = 0 := by
  by_contra hc
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hc hM.ne
  exact absurd (hbdd n) (not_le.mpr hn)

-- ============================================================
-- Part II: Core Measure Theory Lemma
-- ============================================================

/-- If {f n} are pairwise disjoint measurable sets of equal measure,
    all contained in a set S of finite measure, then μ(f 0) = 0.

    Proof: For each N, N · μ(f 0) = μ(⋃_{n<N} f n) ≤ μ(S) < ⊤.
    The ENNReal Archimedean property then forces μ(f 0) = 0. -/
lemma zero_measure_of_infinite_disjoint {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → Set α) (S : Set α)
    (hf : ∀ n, MeasurableSet (f n))
    (hdisj : Pairwise (fun m n => Disjoint (f m) (f n)))
    (hSub : ∀ n, f n ⊆ S)
    (hSfin : μ S < ⊤)
    (heq : ∀ n, μ (f n) = μ (f 0)) :
    μ (f 0) = 0 :=
  ennreal_const_le_finite_imp_zero (μ (f 0)) (μ S) hSfin fun N => by
    have hpd : PairwiseDisjoint (↑(Finset.range N) : Set ℕ) f :=
      fun m _ n _ hmn => hdisj hmn
    have hbiunion : μ (⋃ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range N, μ (f n) :=
      measure_biUnion_finset hpd (fun n _ => hf n)
    have h1 : ↑N * μ (f 0) = ∑ _ ∈ Finset.range N, μ (f 0) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 : ∑ _ ∈ Finset.range N, μ (f 0) = ∑ n ∈ Finset.range N, μ (f n) :=
      Finset.sum_congr rfl (fun n _ => (heq n).symm)
    have h3 : ∑ n ∈ Finset.range N, μ (f n) = μ (⋃ n ∈ Finset.range N, f n) :=
      hbiunion.symm
    have h4 : μ (⋃ n ∈ Finset.range N, f n) ≤ μ S :=
      measure_mono (Set.iUnion₂_subset (fun n _ => hSub n))
    rw [h1, h2, h3]
    exact h4

-- ============================================================
-- Part III: Translation Invariance
-- ============================================================

/-- A Borel measure μ is translation-invariant if shifting any set by any
    vector v preserves its measure: μ.map (· + v) = μ for all v. -/
def IsTransInvariant {H : Type*} [AddCommGroup H] [TopologicalSpace H]
    [MeasurableSpace H] (μ : Measure H) : Prop :=
  ∀ (v : H), μ.map (fun x => x + v) = μ

/-- Translation-invariant measures assign equal measure to all balls of
    the same radius, regardless of center.

    Proof: Translate by -x. The preimage of B(0, r) under (· + -x) is B(x, r). -/
lemma trans_inv_ball_eq {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) (hμ : IsTransInvariant μ) (x : H) (r : ℝ) :
    μ (Metric.ball x r) = μ (Metric.ball 0 r) := by
  -- Apply translation invariance with v = -x
  have key : (μ.map (fun y => y + -x)) (Metric.ball 0 r) = μ (Metric.ball 0 r) :=
    congr_arg (fun m : Measure H => m (Metric.ball 0 r)) (hμ (-x))
  -- Expand the map via preimage
  rw [Measure.map_apply (by fun_prop) measurableSet_ball] at key
  -- Show: μ(ball x r) = μ((· + -x)⁻¹' ball 0 r) = μ(ball 0 r)
  rw [show Metric.ball x r = (fun y => y + -x) ⁻¹' Metric.ball 0 r from by
    ext y
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, dist_eq_norm,
               sub_zero]
    constructor <;> intro h <;> (convert h using 2; abel)]
  exact key

-- ============================================================
-- Part IV: Orthonormal Sequence Infrastructure
-- ============================================================

/-- An infinite orthonormal sequence in a Hilbert space: unit vectors,
    pairwise orthogonal. -/
structure OrthoSeq (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The sequence of unit vectors -/
  seq : ℕ → H
  /-- Each vector has norm 1 -/
  norm_one : ∀ n, ‖seq n‖ = 1
  /-- Distinct vectors are orthogonal -/
  inner_zero : ∀ m n, m ≠ n → ⟪seq m, seq n⟫_ℝ = 0

/-- Each ball B(eₙ, 1/3) is contained in B(0, 4/3).
    Proof: dist x 0 ≤ dist x eₙ + dist eₙ 0 = dist x eₙ + 1 < 1/3 + 1 = 4/3. -/
lemma ortho_ball_subset {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (os : OrthoSeq H) (n : ℕ) :
    Metric.ball (os.seq n) (1/3 : ℝ) ⊆ Metric.ball (0 : H) (4/3 : ℝ) := by
  intro x hx
  rw [Metric.mem_ball] at *
  calc dist x 0
      ≤ dist x (os.seq n) + dist (os.seq n) 0 := dist_triangle x (os.seq n) 0
    _ = dist x (os.seq n) + ‖os.seq n‖ := by rw [dist_zero_right]
    _ = dist x (os.seq n) + 1 := by rw [os.norm_one]
    _ < 1/3 + 1 := by linarith
    _ = 4/3 := by norm_num

/-- The balls B(eₙ, 1/3) are pairwise disjoint.

    Proof: If x ∈ B(eₙ, 1/3) ∩ B(eₘ, 1/3) for n ≠ m, then by the triangle inequality
    dist(eₙ, eₘ) < 2/3. But dist(eₙ, eₘ) = ‖eₙ - eₘ‖ = √2 > 2/3. Contradiction. -/
lemma ortho_balls_disjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (os : OrthoSeq H) :
    Pairwise (fun m n => Disjoint (Metric.ball (os.seq m) (1/3 : ℝ)) (Metric.ball (os.seq n) (1/3 : ℝ))) := by
  intro m n hmn
  rw [disjoint_left]
  intro x hxm hxn
  rw [Metric.mem_ball] at hxm hxn
  -- Triangle inequality gives dist(eₘ, eₙ) < 2/3
  have hd : dist (os.seq m) (os.seq n) < 2/3 :=
    calc dist (os.seq m) (os.seq n)
        ≤ dist (os.seq m) x + dist x (os.seq n) := dist_triangle _ _ _
      _ = dist x (os.seq m) + dist x (os.seq n) := by rw [dist_comm (os.seq m) x]
      _ < 1/3 + 1/3 := by linarith
      _ = 2/3 := by norm_num
  -- But orthonormal_dist gives ‖eₘ - eₙ‖ = √2
  have heq : ‖os.seq m - os.seq n‖ = Real.sqrt 2 :=
    orthonormal_dist (os.seq m) (os.seq n) (os.norm_one m) (os.norm_one n) (os.inner_zero m n hmn)
  -- And orthonormal_balls_disjoint gives √2 > 2/3
  rw [dist_eq_norm] at hd
  linarith [orthonormal_balls_disjoint, heq ▸ hd]

-- ============================================================
-- Part V: Main Theorem
-- ============================================================

/-- **Main Result**: If H is a Hilbert space with an orthonormal sequence and
    μ is translation-invariant with μ(B(0, 4/3)) < ∞, then μ(B(0, 1/3)) = 0.

    The key steps:
    1. B(eₙ, 1/3) are infinitely many disjoint sets, all in B(0, 4/3)
    2. Each has equal measure μ(B(0, 1/3)) by translation invariance
    3. Finitely-bounded infinite equal-measure family → measure = 0 -/
theorem no_invariant_locally_finite_ball {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) (hμ : IsTransInvariant μ)
    (os : OrthoSeq H)
    (hfin : μ (Metric.ball (0 : H) (4/3 : ℝ)) < ⊤) :
    μ (Metric.ball (0 : H) (1/3 : ℝ)) = 0 := by
  have h0 : μ (Metric.ball (os.seq 0) (1/3 : ℝ)) = 0 :=
    zero_measure_of_infinite_disjoint μ
      (fun n => Metric.ball (os.seq n) (1/3 : ℝ))
      (Metric.ball (0 : H) (4/3 : ℝ))
      (fun _ => measurableSet_ball)
      (ortho_balls_disjoint os)
      (fun n => ortho_ball_subset os n)
      hfin
      (fun n => (trans_inv_ball_eq μ hμ (os.seq n) (1/3)).trans
        (trans_inv_ball_eq μ hμ (os.seq 0) (1/3)).symm)
  rw [← trans_inv_ball_eq μ hμ (os.seq 0) (1/3)]
  exact h0

/-- **Corollary**: Under the same hypotheses, every ball of radius 1/3 has measure 0,
    regardless of its center. -/
theorem no_invariant_locally_finite_any_center {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) (hμ : IsTransInvariant μ)
    (os : OrthoSeq H)
    (hfin : μ (Metric.ball (0 : H) (4/3 : ℝ)) < ⊤)
    (y : H) :
    μ (Metric.ball y (1/3 : ℝ)) = 0 := by
  rw [trans_inv_ball_eq μ hμ y (1/3)]
  exact no_invariant_locally_finite_ball μ hμ os hfin

-- ============================================================
-- Part VI: Small Balls Corollary
-- ============================================================

/-- All balls of radius ≤ 1/3 have measure 0.
    Proof: B(y, r) ⊆ B(y, 1/3) and μ(B(y, 1/3)) = 0 by translation. -/
theorem no_invariant_locally_finite_small_ball {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) (hμ : IsTransInvariant μ)
    (os : OrthoSeq H)
    (hfin : μ (Metric.ball (0 : H) (4/3 : ℝ)) < ⊤)
    (y : H) (r : ℝ) (hr : r ≤ 1/3) :
    μ (Metric.ball y r) = 0 := by
  refine le_antisymm ?_ zero_le
  calc μ (Metric.ball y r)
      ≤ μ (Metric.ball y (1/3)) := measure_mono (Metric.ball_subset_ball hr)
    _ = 0 := no_invariant_locally_finite_any_center μ hμ os hfin y

-- ============================================================
-- Part VII: Parametric Version (arbitrary small radius)
-- ============================================================

/-- **Parametric impossibility**: For any 0 < δ < √2/2, translation-invariant
    locally finite measures assign μ(B(0, δ)) = 0.

    Uses that ‖eₙ - eₘ‖ = √2 > 2δ ensures disjoint balls of radius δ,
    each contained in B(0, 1 + δ).

    This generalizes the main theorem from δ = 1/3 to any δ < √2/2 ≈ 0.707. -/
theorem no_invariant_parametric {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) (hμ : IsTransInvariant μ)
    (os : OrthoSeq H)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_small : 2 * δ < Real.sqrt 2)
    (hfin : μ (Metric.ball (0 : H) (1 + δ)) < ⊤) :
    μ (Metric.ball (0 : H) δ) = 0 := by
  -- The balls B(eₙ, δ) are pairwise disjoint (dist(eₙ, eₘ) = √2 > 2δ)
  have hdisj : Pairwise (fun m n => Disjoint (Metric.ball (os.seq m) δ) (Metric.ball (os.seq n) δ)) := by
    intro m n hmn
    rw [disjoint_left]
    intro x hxm hxn
    rw [Metric.mem_ball] at hxm hxn
    have hd : dist (os.seq m) (os.seq n) < 2 * δ :=
      calc dist (os.seq m) (os.seq n)
          ≤ dist (os.seq m) x + dist x (os.seq n) := dist_triangle _ _ _
        _ = dist x (os.seq m) + dist x (os.seq n) := by rw [dist_comm (os.seq m) x]
        _ < δ + δ := by linarith
        _ = 2 * δ := by ring
    have heq : ‖os.seq m - os.seq n‖ = Real.sqrt 2 :=
      orthonormal_dist (os.seq m) (os.seq n) (os.norm_one m) (os.norm_one n) (os.inner_zero m n hmn)
    rw [dist_eq_norm] at hd
    linarith
  -- Each B(eₙ, δ) ⊆ B(0, 1 + δ)
  have hsub : ∀ n, Metric.ball (os.seq n) δ ⊆ Metric.ball (0 : H) (1 + δ) := by
    intro n x hx
    rw [Metric.mem_ball] at *
    calc dist x 0
        ≤ dist x (os.seq n) + dist (os.seq n) 0 := dist_triangle _ _ _
      _ = dist x (os.seq n) + ‖os.seq n‖ := by rw [dist_zero_right]
      _ = dist x (os.seq n) + 1 := by rw [os.norm_one]
      _ < δ + 1 := by linarith
      _ = 1 + δ := by ring
  -- Translation invariance gives equal measure
  have heq : ∀ n, μ (Metric.ball (os.seq n) δ) = μ (Metric.ball (0 : H) δ) := by
    intro n; exact trans_inv_ball_eq μ hμ (os.seq n) δ
  have heq0 : ∀ n, μ (Metric.ball (os.seq n) δ) = μ (Metric.ball (os.seq 0) δ) :=
    fun n => (heq n).trans (heq 0).symm
  -- Apply the core lemma
  have h0 : μ (Metric.ball (os.seq 0) δ) = 0 :=
    zero_measure_of_infinite_disjoint μ (fun n => Metric.ball (os.seq n) δ)
      (Metric.ball (0 : H) (1 + δ)) (fun _ => measurableSet_ball)
      hdisj hsub hfin heq0
  rw [← heq 0]
  exact h0

end LebesgueMeasureOQ03OQ01
