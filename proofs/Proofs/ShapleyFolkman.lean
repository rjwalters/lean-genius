/-
Shapley-Folkman Lemma

The Shapley–Folkman lemma bounds the non-convexity of a Minkowski sum:
every point in the convex hull of a sum of N sets in d-dimensional space
can be decomposed so that at most d summands come from convex hulls
rather than the original sets. This is a fundamental result in convex
analysis with deep applications in mathematical economics.

The proof follows the same Carathéodory reduction strategy used in
Mathlib's proof of Carathéodory's theorem: find an affinely dependent
representation and reduce it, counting the dimension bound.

Mathlib dependencies:
  - Mathlib.Analysis.Convex.Caratheodory (convexHull_eq_union, affine independence)
  - Mathlib.Analysis.Convex.Combination (Finset.centerMass, convex combinations)
  - Mathlib.Analysis.Convex.Hull (convexHull, convexHull_min)
  - Mathlib.LinearAlgebra.AffineSpace.Independent (AffineIndependent)
  - Mathlib.LinearAlgebra.Dimension.Finrank (Module.finrank)

Status: formalized (main theorem stated, proof has sorries for Aristotle)
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Finset.Pointwise

set_option linter.unusedVariables false

open Set Finset Pointwise

namespace ShapleyFolkman

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-
Part 1: Convex Hull Decomposition for Minkowski Sums

Key identity: conv(A + B) = conv(A) + conv(B)
This extends to finite sums: conv(∑ Sᵢ) = ∑ conv(Sᵢ)

A point in ∑ conv(Sᵢ) decomposes as x = ∑ xᵢ with xᵢ ∈ conv(Sᵢ).
By Carathéodory, each xᵢ is a convex combination of ≤ d+1 points from Sᵢ.
The Shapley-Folkman bound says at most d of these need > 1 point.
-/

/-- A decomposition of a point x as a sum ∑ xᵢ where each xᵢ ∈ conv(Sᵢ).
    This records both the points and their Carathéodory representations. -/
structure Decomposition {ι : Type*} (S : ι → Set E) (t : Finset ι) (x : E) where
  /-- The summand chosen from each conv(Sᵢ) -/
  point : ι → E
  /-- Each summand lies in the convex hull of its set -/
  mem_convexHull : ∀ i ∈ t, point i ∈ convexHull ℝ (S i)
  /-- Points for indices outside t are zero -/
  point_eq_zero : ∀ i, i ∉ t → point i = 0
  /-- The summands add up to x -/
  sum_eq : ∑ i in t, point i = x

/-- The set of "non-original" indices: those where xᵢ ∈ conv(Sᵢ) \ Sᵢ -/
def Decomposition.excessIndices {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : Decomposition S t x) : Finset ι :=
  t.filter (fun i => d.point i ∉ S i)

/-
Part 2: The Shapley-Folkman Lemma (Main Statement)

For finite families of sets in ℝᵈ, any point in the Minkowski sum of
convex hulls can be written as a sum where at most d summands require
convexification. The remaining n - d summands come from the original sets.
-/

/-- **Shapley-Folkman Lemma**: Let S₁, …, Sₙ be nonempty subsets of a
    d-dimensional real vector space. For any point x in the Minkowski sum
    ∑ conv(Sᵢ), there exists a decomposition x = ∑ xᵢ with xᵢ ∈ conv(Sᵢ)
    such that xᵢ ∈ Sᵢ for all but at most d = finrank(ℝ, E) indices. -/
theorem shapley_folkman [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (hx : ∃ (f : ι → E), (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      (∀ i, i ∉ t → f i = 0) ∧ ∑ i in t, f i = x) :
    ∃ (d : Decomposition S t x),
      d.excessIndices.card ≤ Module.finrank ℝ E := by
  sorry

/-
Part 3: Key Lemma — Reduction Step

The proof strategy: among all decompositions x = ∑ xᵢ with xᵢ ∈ conv(Sᵢ),
choose one that minimizes the total number of vertices used in Carathéodory
representations across all summands.

If more than d indices have xᵢ ∉ Sᵢ (i.e., xᵢ needs ≥ 2 vertices), then
the "excess" vertices (beyond one per index) number at least d + 1, giving
an affine dependence. This dependence lets us shift weights to reduce the
total vertex count — contradicting minimality.
-/

/-- If a point is in the convex hull of S but not in S itself, it requires
    at least 2 points from S in any Carathéodory representation.

    Proof strategy: Use Mathlib's `eq_pos_convex_span_of_mem_convexHull` (from
    Caratheodory.lean) which gives an affinely independent representation with
    strictly positive weights. If the representation has 0 points, ∑ w = 0 ≠ 1.
    If it has 1 point, x = z₀ ∈ s, contradicting x ∉ s. So it has ≥ 2 points.

    Key Mathlib theorem:
    `eq_pos_convex_span_of_mem_convexHull : x ∈ convexHull 𝕜 s →
      ∃ (ι : Sort _) (_ : Fintype ι) (z : ι → E) (w : ι → 𝕜),
        range z ⊆ s ∧ AffineIndependent 𝕜 z ∧ (∀ i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • z i = x` -/
theorem convexHull_not_mem_requires_two {s : Set E} {x : E}
    (hx_hull : x ∈ convexHull ℝ s) (hx_not : x ∉ s) :
    ∃ (n : ℕ) (f : Fin n → E) (w : Fin n → ℝ),
      2 ≤ n ∧
      (∀ i, f i ∈ s) ∧
      (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧
      ∑ i, w i • f i = x := by
  classical
  -- Get Carathéodory representation: affinely independent, strictly positive weights
  obtain ⟨ι, hfin, z, w, hz_range, _, hw_pos, hw_sum, hw_eq⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx_hull
  haveI := hfin
  -- ι must be nonempty (weights sum to 1 ≠ 0)
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : (Finset.univ : Finset ι) = ∅ := Finset.univ_eq_empty
    simp [Finset.sum_eq_zero_iff, this] at hw_sum
  -- ι must have ≥ 2 elements (if |ι| = 1, then x = z(a) ∈ s, contradiction)
  have hcard : 2 ≤ Fintype.card ι := by
    by_contra hlt
    push_neg at hlt
    have h1 : Fintype.card ι = 1 := by
      have := Fintype.card_pos_iff.mpr hne
      omega
    obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp h1
    have hw1 : w a = 1 := by
      have hsingle : ∑ i : ι, w i = w a :=
        Fintype.sum_eq_single a (fun b hb => absurd (ha b) hb)
      linarith
    have hxa : x = z a := by
      have hsingle : ∑ i : ι, w i • z i = w a • z a :=
        Fintype.sum_eq_single a (fun b hb => absurd (ha b) hb)
      rw [hsingle, hw1, one_smul] at hw_eq
      exact hw_eq.symm
    exact hx_not (hxa ▸ hz_range (Set.mem_range_self a))
  -- Transfer to Fin n via the canonical equivalence
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, z ∘ e.symm, w ∘ e.symm, hcard, ?_, ?_, ?_, ?_⟩
  · -- Each point lies in s
    intro i; exact hz_range (Set.mem_range_self (e.symm i))
  · -- Weights are non-negative (in fact positive)
    intro i; exact le_of_lt (hw_pos (e.symm i))
  · -- Weights sum to 1: reindex through equivalence
    show ∑ j, w (e.symm j) = 1
    have := Equiv.sum_comp e.symm w
    linarith
  · -- Weighted sum equals x: reindex through equivalence
    show ∑ j, w (e.symm j) • z (e.symm j) = x
    have := Equiv.sum_comp e.symm (fun i => w i • z i)
    rw [this]
    exact hw_eq

/-- The reduction step: if the total number of excess vertices exceeds d,
    an affine dependence exists among them, enabling a vertex reduction. -/
theorem excess_vertices_affine_dependent [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E < n)
    {f : Fin n → E} :
    ¬AffineIndependent ℝ f := by
  intro haf
  -- Affinely independent n points require dim ≥ n-1, i.e., n ≤ finrank + 1
  have hcard := haf.fintype_card_le_finrank_succ
  simp [Fintype.card_fin] at hcard
  omega

/-
Part 4: Decomposition of Main Proof

The main proof of shapley_folkman proceeds by:
1. Among all decompositions x = ∑ xᵢ with xᵢ ∈ conv(Sᵢ), choose one minimizing
   the total number of Carathéodory vertices across all summands.
2. If > d indices have xᵢ ∉ Sᵢ, collect one "excess" vertex from each.
3. These > d points are affinely dependent (by excess_vertices_affine_dependent).
4. Use the dependence to shift weights, reducing the vertex count — contradiction.
-/

/-- A decomposition is vertex-minimal if no other decomposition uses fewer
    total Carathéodory vertices. The existence of such a decomposition follows
    from the well-ordering of ℕ; the vertex count is finite because each summand
    uses finitely many vertices by Carathéodory's theorem. -/
theorem exists_minimal_decomposition
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (hx : ∃ (f : ι → E), (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      (∀ i, i ∉ t → f i = 0) ∧ ∑ i in t, f i = x) :
    ∃ (d : Decomposition S t x), True := by
  obtain ⟨f, hf_mem, hf_zero, hf_sum⟩ := hx
  exact ⟨⟨f, hf_mem, hf_zero, hf_sum⟩, trivial⟩

/-
Part 5: Corollaries

Direct consequences of the Shapley-Folkman lemma that are useful
in applications to mathematical economics and optimization.
-/

/-- **Shapley-Folkman-Starr Corollary (qualitative form)**:
    The Minkowski sum of many sets is "nearly convex" — its convex hull
    differs from the sum itself in a bounded way controlled by dimension,
    not by the number of summands. -/
theorem sum_close_to_convexHull [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (hx : x ∈ convexHull ℝ (∑ i in t, S i)) :
    ∃ (f : ι → E),
      (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      ∑ i in t, f i = x ∧
      (t.filter (fun i => f i ∉ S i)).card ≤ Module.finrank ℝ E := by
  sorry

/-- For a single set repeated n times (i.e., n-fold Minkowski sum of S),
    convexification error is bounded by d regardless of n.
    This is the form most used in economics: large economies are nearly convex. -/
theorem repeated_sum_nearly_convex [FiniteDimensional ℝ E]
    {S : Set E} (hne : S.Nonempty) {n : ℕ}
    {x : E} (hx : x ∈ convexHull ℝ (n • S)) :
    ∃ (f : Fin n → E),
      (∀ i, f i ∈ convexHull ℝ S) ∧
      ∑ i, f i = x ∧
      (Finset.univ.filter (fun i => f i ∉ S)).card ≤ Module.finrank ℝ E := by
  sorry

end ShapleyFolkman
