/-
# Kakutani from Brouwer via Approximate Selections

This file outlines the proof of Kakutani's fixed point theorem from
Brouwer's fixed point theorem using approximate continuous selections.

**Proof Strategy**:
1. For each n, construct a continuous 1/n-approximate selection f_n of F
2. Apply Brouwer's FPT: ∃ x_n with f_n(x_n) = x_n
3. By compactness of S: extract convergent subsequence x_{n_k} → x*
4. Use upper hemicontinuity to show x* ∈ F(x*)

**Status**: AXIOMATIZED (2 axioms)
- Axiom 1: Brouwer's FPT in Euclidean space
- Axiom 2: Approximate selections exist for UHC maps with convex values
- Proved: Sequential compactness (from Mathlib's IsCompact.isSeqCompact)
- Proved: The combination argument (Kakutani from the two axioms via the helper)
- Proved: The limit-argument helper (approx_fixedpoint_implies_fixedpoint)

**Why approximate selections instead of simplicial approximation?**
Both approaches work, but approximate selections avoid the need for
triangulation infrastructure (which is not in Mathlib). The key lemma
(existence of continuous ε-approximate selections for UHC maps with
nonempty convex values) can be proved using partitions of unity.

**References**:
- Kakutani, S. (1941). A generalization of Brouwer's fixed point theorem.
  Duke Math. J. 8, 457-459.
- Cellina, A. (1969). Approximation of set valued functions and fixed
  point theorems. Ann. Mat. Pura Appl. 82, 17-24.

Parent: SchauderFixedPointOQ03.lean (Kakutani framework)
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sequences
import Mathlib.Tactic

noncomputable section

open Set Filter Topology Metric

namespace KakutaniFromBrouwer

-- ============================================================
-- Part I: Definitions (imported from parent)
-- ============================================================

/-- A set-valued map (correspondence). -/
def SetValuedMap (X Y : Type*) := X → Set Y

/-- Fixed point of a set-valued map: x ∈ F(x). -/
def IsFixedPoint {X : Type*} (F : SetValuedMap X X) (x : X) : Prop :=
  x ∈ F x

/-- Upper hemicontinuity: {x | F(x) ⊆ V} is open for every open V. -/
def IsUpperHemicontinuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (F : SetValuedMap X Y) : Prop :=
  ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V}

-- ============================================================
-- Part II: Key Axioms
-- ============================================================

/-- **Axiom 1: Brouwer's Fixed Point Theorem**

    Every continuous function from a nonempty compact convex subset
    of Euclidean space to itself has a fixed point.

    This is proved in Mathlib for the unit ball via degree theory.
    We state it here for general compact convex subsets. -/
axiom brouwer_fpt {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (f : ↥S → ↥S) (hf : Continuous f) :
    ∃ x : ↥S, f x = x

/-- A continuous function f : S → S is an ε-approximate selection of F
    if d(f(x), F(x)) < ε for all x ∈ S. -/
def IsApproxSelection {X : Type*} [PseudoMetricSpace X]
    (F : SetValuedMap X X) (f : X → X) (ε : ℝ) : Prop :=
  ∀ x, ∃ y ∈ F x, dist (f x) y < ε

/-- **Axiom 2: Approximate Continuous Selections**

    For a compact convex S, an UHC map F : S → 2^S with nonempty convex
    values, and any ε > 0, there exists a continuous ε-approximate
    selection f : S → S.

    The proof uses:
    1. For each x, pick y_x ∈ F(x) and use UHC to get a neighborhood U_x
       where F(U_x) ⊆ B(F(x), ε)
    2. By compactness, extract a finite subcover U_{x_1}, ..., U_{x_k}
    3. Take a subordinate partition of unity {φ_i}
    4. Define f(x) = Σ φ_i(x) · y_{x_i}
    5. By convexity of S, f maps into S
    6. By construction, f(x) is within ε of F(x) -/
axiom approx_selection_exists {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ↥S → ↥S, Continuous f ∧ IsApproxSelection F (fun x => (f x : ↥S)) ε

/-- **Sequential Compactness in Metric Spaces**

    In a compact metric space, every sequence has a convergent subsequence.
    Proved from Mathlib's `IsCompact.isSeqCompact` (PseudoMetricSpace is
    first-countable). Was previously stated as an axiom; now derived. -/
theorem seq_compact_of_compact {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (hS : IsCompact S) (x : ℕ → X) (hx : ∀ n, x n ∈ S) :
    ∃ (a : X) (φ : ℕ → ℕ), a ∈ S ∧ StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (𝓝 a) := by
  obtain ⟨a, ha, φ, hφ_mono, hφ_tend⟩ := hS.isSeqCompact hx
  exact ⟨a, φ, ha, hφ_mono, hφ_tend⟩

-- ============================================================
-- Part III: Limit Argument (Helper Lemma)
-- ============================================================

/-- A continuous function with ε-approximate fixed point property
    for all ε > 0 has a true fixed point (when the target is closed).

    This captures the limit argument: if we can get "almost" fixed points
    for any precision, compactness gives a real one.

    **Proof outline**:
    1. Build sequences `xₙ ∈ S`, `yₙ ∈ F(xₙ)` with `dist(xₙ, yₙ) < 1/(n+1)`
       via choice on `happrox`.
    2. Compactness of `S` yields a subsequence `x_{φ(n)} → x*` with `x* ∈ S`.
    3. Since `dist(x_{φ(n)}, y_{φ(n)}) → 0`, the subsequence
       `y_{φ(n)} → x*` as well (triangle inequality).
    4. Suppose `x* ∉ F(x*)`. Case split on `(F x*).Nonempty`:
       - **Empty case**: take `V := ∅` (open superset of empty F(x*));
         UHC gives an open `U ∋ x*` with `F(U) ⊆ ∅`, hence eventually
         `F(x_{φ(n)}) = ∅`, contradicting `y_{φ(n)} ∈ F(x_{φ(n)})`.
       - **Nonempty case**: `δ := infDist x* (F x*) > 0` since `F(x*)` is
         closed and `x* ∉ F(x*)`. Take `V := Metric.thickening (δ/2) (F x*)`,
         an open superset of `F(x*)`. UHC gives an open `U ∋ x*` with
         `F(U) ⊆ V`. Eventually `x_{φ(n)} ∈ U`, hence `y_{φ(n)} ∈ V`, so
         `infDist y_{φ(n)} (F x*) < δ/2`. Triangle inequality:
         `infDist x* (F x*) ≤ dist x* y_{φ(n)} + infDist y_{φ(n)} (F x*) < δ`
         for `n` large, contradicting `δ = infDist x* (F x*)`. -/
theorem approx_fixedpoint_implies_fixedpoint
    {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (hS : IsCompact S)
    (F : SetValuedMap X X) (hF_closed : ∀ x ∈ S, IsClosed (F x))
    (hF_uhc : IsUpperHemicontinuous F)
    (happrox : ∀ ε > 0, ∃ x ∈ S, ∃ y ∈ F x, dist x y < ε) :
    ∃ x ∈ S, IsFixedPoint F x := by
  -- Step 1: build sequences via choice
  choose xseq hxseq_S yseq hyseq_F hxy_dist using
    fun n : ℕ => happrox (1 / ((n : ℝ) + 1)) (by positivity)
  -- Step 2: extract convergent subsequence
  obtain ⟨x_star, φ, hx_star_S, hφ_mono, hφ_tend⟩ :=
    seq_compact_of_compact S hS xseq hxseq_S
  refine ⟨x_star, hx_star_S, ?_⟩
  -- Step 3: yseq ∘ φ → x_star
  have h_one_div_to_zero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h_xy_to_zero :
      Tendsto (fun n => dist (xseq n) (yseq n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg)
      (fun n => le_of_lt (hxy_dist n)) h_one_div_to_zero
  have h_xy_phi_to_zero :
      Tendsto (fun n => dist (xseq (φ n)) (yseq (φ n))) atTop (𝓝 0) :=
    h_xy_to_zero.comp hφ_mono.tendsto_atTop
  have h_x_phi_dist_to_zero :
      Tendsto (fun n => dist (xseq (φ n)) x_star) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hφ_tend
  have hyφ_tend : Tendsto (fun n => yseq (φ n)) atTop (𝓝 x_star) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h_yx_phi : Tendsto (fun n => dist (yseq (φ n)) (xseq (φ n)))
        atTop (𝓝 0) := by
      simpa [dist_comm] using h_xy_phi_to_zero
    have h_sum :
        Tendsto (fun n => dist (yseq (φ n)) (xseq (φ n)) +
            dist (xseq (φ n)) x_star) atTop (𝓝 0) := by
      simpa using h_yx_phi.add h_x_phi_dist_to_zero
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => dist_triangle (yseq (φ n)) (xseq (φ n)) x_star) h_sum
  -- Step 4: derive contradiction from x_star ∉ F x_star
  by_contra hne
  have hF_closed_xstar : IsClosed (F x_star) := hF_closed _ hx_star_S
  by_cases hF_xstar_ne : (F x_star).Nonempty
  · -- Nonempty case: thickening contradiction
    set δ : ℝ := Metric.infDist x_star (F x_star) with hδ_def
    have hδ_pos : 0 < δ := by
      have h_not_mem_closure : x_star ∉ closure (F x_star) := by
        rwa [hF_closed_xstar.closure_eq]
      have h_ne_zero : Metric.infDist x_star (F x_star) ≠ 0 := by
        intro h
        exact h_not_mem_closure
          ((Metric.mem_closure_iff_infDist_zero hF_xstar_ne).mpr h)
      exact lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm h_ne_zero)
    have hδ_half_pos : 0 < δ / 2 := by linarith
    -- Define V as the union of (δ/2)-balls around F x_star (open neighborhood of F x_star)
    let V : Set X := ⋃ y ∈ F x_star, Metric.ball y (δ / 2)
    have hV_open : IsOpen V := isOpen_biUnion (fun _ _ => Metric.isOpen_ball)
    have hF_in_V : F x_star ⊆ V := by
      intro y hy
      exact Set.mem_biUnion hy (Metric.mem_ball_self hδ_half_pos)
    let U : Set X := {z | F z ⊆ V}
    have hU_open : IsOpen U := hF_uhc V hV_open
    have hxstar_U : x_star ∈ U := hF_in_V
    -- Eventually xseq (φ n) ∈ U
    have h_eventually_U : ∀ᶠ n in atTop, xseq (φ n) ∈ U :=
      hφ_tend.eventually (hU_open.mem_nhds hxstar_U)
    -- Eventually dist x_star (yseq (φ n)) < δ/2
    have h_dist_yφ : Tendsto (fun n => dist x_star (yseq (φ n)))
        atTop (𝓝 0) := by
      have h := tendsto_iff_dist_tendsto_zero.mp hyφ_tend
      simpa [dist_comm] using h
    have h_eventually_dist :
        ∀ᶠ n in atTop, dist x_star (yseq (φ n)) < δ / 2 :=
      h_dist_yφ.eventually (Iio_mem_nhds hδ_half_pos)
    -- Combine to get the contradiction
    obtain ⟨n, hn_U, hn_dist⟩ :=
      (h_eventually_U.and h_eventually_dist).exists
    -- yseq (φ n) ∈ V, so ∃ z ∈ F x_star, dist (yseq (φ n)) z < δ/2
    have h_yseq_in_V : yseq (φ n) ∈ V := hn_U (hyseq_F (φ n))
    obtain ⟨z, hz_F, hz_ball⟩ := Set.mem_iUnion₂.mp h_yseq_in_V
    rw [Metric.mem_ball] at hz_ball
    -- δ = infDist x_star (F x_star) ≤ dist x_star z (since z ∈ F x_star)
    have h_delta_le_dist : δ ≤ dist x_star z := by
      have hi := Metric.infDist_le_dist_of_mem (x := x_star) hz_F
      linarith [hδ_def]
    -- triangle inequality on dist x_star z
    have h_tri : dist x_star z ≤ dist x_star (yseq (φ n)) + dist (yseq (φ n)) z :=
      dist_triangle _ _ _
    have hcontra : δ < δ := by
      calc δ ≤ dist x_star z := h_delta_le_dist
        _ ≤ dist x_star (yseq (φ n)) + dist (yseq (φ n)) z := h_tri
        _ < δ / 2 + δ / 2 := by linarith
        _ = δ := by ring
    exact lt_irrefl _ hcontra
  · -- Empty case
    rw [Set.not_nonempty_iff_eq_empty] at hF_xstar_ne
    let U : Set X := {z | F z ⊆ (∅ : Set X)}
    have hU_open : IsOpen U := hF_uhc ∅ isOpen_empty
    have hxstar_U : x_star ∈ U := by
      show F x_star ⊆ ∅
      rw [hF_xstar_ne]
    have h_eventually_U : ∀ᶠ n in atTop, xseq (φ n) ∈ U :=
      hφ_tend.eventually (hU_open.mem_nhds hxstar_U)
    obtain ⟨n, hn⟩ := h_eventually_U.exists
    -- F (xseq (φ n)) ⊆ ∅, but yseq (φ n) ∈ F (xseq (φ n))
    exact (hn (hyseq_F (φ n))).elim

-- ============================================================
-- Part IV: The Proof of Kakutani from Brouwer
-- ============================================================

/-- **Kakutani's FPT from Brouwer + Approximate Selections**

    Proof sketch (filled body below):
    1. For each ε > 0, get a continuous ε-approximate selection f_ε of F
       via `approx_selection_exists`.
    2. Apply `brouwer_fpt` to f_ε on S to get x₀ with f_ε(x₀) = x₀.
    3. The approximate-selection property at x₀ gives y ∈ F(x₀) with
       `dist(f_ε(x₀), y) < ε`. Since f_ε(x₀) = x₀, `dist(x₀, y) < ε`.
    4. Hand the family of ε-witnesses to `approx_fixedpoint_implies_fixedpoint`,
       which uses sequential compactness + closedness + UHC of F to extract
       a genuine fixed point. -/
theorem kakutani_from_brouwer {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_closed : ∀ x, IsClosed (F x))
    (hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (hF_uhc : IsUpperHemicontinuous F) :
    ∃ x : ↥S, IsFixedPoint F x := by
  -- The subtype ↥S inherits a PseudoMetricSpace from EuclideanSpace.
  -- Compactness of ↥S follows from compactness of S in the ambient space.
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  have hUniv : IsCompact (Set.univ : Set ↥S) := isCompact_univ
  have hF_closed' : ∀ x ∈ (Set.univ : Set ↥S), IsClosed (F x) :=
    fun x _ => hF_closed x
  have happrox_total :
      ∀ ε > 0, ∃ x ∈ (Set.univ : Set ↥S), ∃ y ∈ F x, dist x y < ε := by
    intro ε hε
    obtain ⟨f, hf_cont, hf_approx⟩ :=
      approx_selection_exists S hS_ne hS_compact hS_convex F
        hF_ne hF_convex hF_uhc ε hε
    obtain ⟨x0, hx0⟩ := brouwer_fpt S hS_ne hS_compact hS_convex f hf_cont
    obtain ⟨y, hy_F, hy_dist⟩ := hf_approx x0
    refine ⟨x0, Set.mem_univ _, y, hy_F, ?_⟩
    -- dist (f x0) y < ε with f x0 = x0 ⇒ dist x0 y < ε
    rw [← hx0]
    exact hy_dist
  obtain ⟨x_star, _, hfp⟩ :=
    approx_fixedpoint_implies_fixedpoint (Set.univ : Set ↥S) hUniv F
      hF_closed' hF_uhc happrox_total
  exact ⟨x_star, hfp⟩

/-
## Part V: Why This Matters

The proof of Kakutani from Brouwer via approximate selections demonstrates
the power of three fundamental principles:
1. **Brouwer's FPT** (topological): continuous self-maps of compact convex sets have fixed points
2. **Approximate selections** (geometric): UHC maps with convex values can be approximated
3. **Compactness** (analytical): bounded sequences have convergent subsequences

The combination yields fixed points for set-valued maps — the cornerstone
of Nash equilibrium existence in game theory.

### Infrastructure Needed in Mathlib
- Brouwer's FPT for general compact convex sets (currently only for closed balls)
- Partition of unity construction for finite open covers in Euclidean space

### Alternative Proof Paths
1. **Simplicial approximation**: Triangulate S, define PL approximations. Avoids
   partition of unity but needs triangulation machinery.
2. **Michael's selection theorem**: Stronger than needed here (gives exact continuous
   selections for lower hemicontinuous maps with convex values).

## Summary

### Axioms (2)
1. `brouwer_fpt` - Brouwer's FPT for compact convex subsets of ℝⁿ
2. `approx_selection_exists` - UHC + convex values → continuous ε-selections exist

### Theorems (proved)
- `seq_compact_of_compact` - Sequential compactness in compact metric spaces
  (was an axiom; now derived from Mathlib)
- `approx_fixedpoint_implies_fixedpoint` - Limit argument for approximate fixed points
- `kakutani_from_brouwer` - The main reduction: Kakutani from the two axioms

### Path to Full Verification
1. Prove `approx_selection_exists` using partition of unity (main infrastructure gap)
2. Verify `brouwer_fpt` against Mathlib's existing Brouwer formalization
-/

#check @brouwer_fpt
#check @approx_selection_exists
#check @approx_fixedpoint_implies_fixedpoint
#check @kakutani_from_brouwer

end KakutaniFromBrouwer
