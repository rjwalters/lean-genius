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

Status: formalized — 0 sorries remain.
-/
import Mathlib

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Set Finset Pointwise

namespace ShapleyFolkman

-- Classical.propDecidable as local instance enables Finset.filter on arbitrary Set predicates.
-- Decomposition.excessIndices must be marked noncomputable explicitly when this is active.
attribute [local instance] Classical.propDecidable

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
  sum_eq : ∑ i ∈ t, point i = x

/-- The set of "non-original" indices: those where xᵢ ∈ conv(Sᵢ) \ Sᵢ -/
noncomputable def Decomposition.excessIndices {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : Decomposition S t x) : Finset ι :=
  t.filter (fun i => d.point i ∉ S i)

/-
Part 2: The Shapley-Folkman Lemma (Main Statement)

For finite families of sets in ℝᵈ, any point in the Minkowski sum of
convex hulls can be written as a sum where at most d summands require
convexification. The remaining n - d summands come from the original sets.
-/

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
        ∑ i, w i = 1 ∧ ∑ i, w i • z i = x`

    Note: weights are strictly positive (0 < w i), not just non-negative.
    This is inherited from eq_pos_convex_span and is needed for the
    perturbation argument in reduce_excess_by_one. -/
theorem convexHull_not_mem_requires_two {s : Set E} {x : E}
    (hx_hull : x ∈ convexHull ℝ s) (hx_not : x ∉ s) :
    ∃ (n : ℕ) (f : Fin n → E) (w : Fin n → ℝ),
      2 ≤ n ∧
      (∀ i, f i ∈ s) ∧
      (∀ i, 0 < w i) ∧
      ∑ i, w i = 1 ∧
      ∑ i, w i • f i = x := by
  -- Strategy: apply eq_pos_convex_span_of_mem_convexHull to get an affinely independent
  -- representation with strictly positive weights, then show it needs ≥ 2 vertices.
  obtain ⟨ι, hFin, z, w, hz_range, _, hw_pos, hw_sum, hx_eq⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx_hull
  letI : Fintype ι := hFin
  -- Show the index type has ≥ 2 elements
  have hn : 2 ≤ Fintype.card ι := by
    by_contra h_lt
    push_neg at h_lt
    -- card = 0 or 1
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · -- card = 0: sum over empty type = 0 ≠ 1
      haveI hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
      simp [Fintype.sum_empty] at hw_sum
    · -- card = 1: unique element → x ∈ s, contradiction
      have h1 : Fintype.card ι = 1 := Nat.le_antisymm (by omega) hpos
      obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp h1
      -- hi₀ : ∀ a : ι, a = i₀; so Finset.univ = {i₀}
      -- hi₀ : ∀ a : ι, a = i₀
      have huniv : (Finset.univ : Finset ι) = {i₀} := by ext i; simp [hi₀ i]
      have hw_one : ∑ i : ι, w i = w i₀ := by conv_lhs => rw [huniv]; simp
      have hwi₀ : w i₀ = 1 := by linarith [hw_sum, hw_one]
      have hzsum : ∑ i : ι, w i • z i = w i₀ • z i₀ := by conv_lhs => rw [huniv]; simp
      have hxi₀ : x = z i₀ := by
        have heq : w i₀ • z i₀ = x := hzsum.symm.trans hx_eq
        rw [hwi₀, one_smul] at heq; exact heq.symm
      exact hx_not (hxi₀ ▸ hz_range (Set.mem_range.mpr ⟨i₀, rfl⟩))
  -- Convert from the abstract index type ι to Fin n via Fintype.equivFin
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, z ∘ e, w ∘ e, hn, ?_, ?_, ?_, ?_⟩
  · intro i; exact hz_range (Set.mem_range.mpr ⟨e i, rfl⟩)
  · intro i; exact hw_pos (e i)
  · -- ∑ i : Fin n, (w ∘ e) i = ∑ i : ι, w i = 1
    exact (Equiv.sum_comp e w).trans hw_sum
  · -- ∑ i : Fin n, (w ∘ e) i • (z ∘ e) i = ∑ i : ι, w i • z i = x
    exact (Equiv.sum_comp e (fun j => w j • z j)).trans hx_eq

/-- The reduction step: if the total number of excess vertices exceeds d,
    an affine dependence exists among them, enabling a vertex reduction. -/
theorem excess_vertices_affine_dependent [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E + 1 < n)
    {f : Fin n → E} :
    ¬AffineIndependent ℝ f := by
  intro haf
  -- Affinely independent n points require dim ≥ n-1, i.e., n ≤ finrank(span) + 1 ≤ finrank(E) + 1
  have hcard := haf.card_le_finrank_succ
  simp [Fintype.card_fin] at hcard
  have hdim_le := Submodule.finrank_le (vectorSpan ℝ (Set.range f))
  omega

/-
Part 4: Proof Architecture for the Main Theorem

The proof of shapley_folkman uses a reduction argument:
1. Start with any decomposition x = ∑ xᵢ with xᵢ ∈ conv(Sᵢ)
2. If > d indices have xᵢ ∉ Sᵢ, reduce the excess count by 1
3. Iterate until ≤ d excess indices remain

The reduction step (reduce_excess_by_one) works as follows:
  a. For each excess index i, xᵢ ∈ conv(Sᵢ) \ Sᵢ, so by convexHull_not_mem_requires_two,
     xᵢ has a binary representation xᵢ = tᵢ·aᵢ + (1-tᵢ)·bᵢ with aᵢ,bᵢ ∈ Sᵢ, 0 < tᵢ < 1
  b. Define δᵢ = bᵢ - aᵢ for each excess index
  c. Since there are d+1 excess indices and dim E = d, the δᵢ are linearly dependent:
     ∃ cᵢ not all zero with ∑ cᵢ·δᵢ = 0
  d. Perturb: xᵢ' = xᵢ + ε·cᵢ·δᵢ for a scalar ε chosen so that one index
     hits a boundary (xᵢ' = aᵢ or bᵢ ∈ Sᵢ)
  e. Since ∑ cᵢ·δᵢ = 0, the perturbation preserves ∑ xᵢ = x
  f. The result has one fewer excess index
-/

/-- **Linear dependence extraction**: d+1 vectors in d-dimensional space are
    linearly dependent, and we can extract explicit coefficients.
    This is the key algebraic input for the perturbation argument. -/
theorem linearDependent_coefficients [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E < n) (f : Fin n → E) :
    ∃ (c : Fin n → ℝ), (∃ i, c i ≠ 0) ∧ ∑ i, c i • f i = 0 := by
  have hli : ¬LinearIndependent ℝ f := by
    intro h
    have := h.fintype_card_le_finrank
    simp [Fintype.card_fin] at this
    omega
  rw [Fintype.linearIndependent_iff] at hli
  push_neg at hli
  obtain ⟨g, hg_sum, i, hi_ne⟩ := hli
  exact ⟨g, ⟨i, hi_ne⟩, hg_sum⟩

/-- A decomposition can always be constructed from the hypothesis. -/
theorem exists_decomposition
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    {x : E} (hx : ∃ (f : ι → E), (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      (∀ i, i ∉ t → f i = 0) ∧ ∑ i ∈ t, f i = x) :
    ∃ (d : Decomposition S t x), True := by
  obtain ⟨f, hf_mem, hf_zero, hf_sum⟩ := hx
  exact ⟨⟨f, hf_mem, hf_zero, hf_sum⟩, trivial⟩

/-- If x ∈ convexHull(s) \ s, write x = t • a + (1-t) • b with a ∈ s,
    b ∈ convexHull(s), t ∈ (0,1).
    Proof: take a = first Carathéodory vertex (in s), t = its weight (∈ (0,1) since n ≥ 2),
    b = renormalized convex combination of remaining vertices (in convexHull s). -/
private lemma binary_repr_of_mem_convexHull_not_mem {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ s) (hxs : x ∉ s) :
    ∃ (a b : E) (t : ℝ), a ∈ s ∧ b ∈ convexHull ℝ s ∧ 0 < t ∧ t < 1 ∧
      x = t • a + (1 - t) • b := by
  -- Get Carathéodory decomposition with ≥ 2 vertices and strictly positive weights
  obtain ⟨n, f, w, hn, hf_mem, hw_pos, hw_sum, hx_eq⟩ :=
    convexHull_not_mem_requires_two hx hxs
  -- Write n = m + 2 so Fin.sum_univ_succ splits off the first term
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  -- Split: ∑ i : Fin (m+2) = first + rest
  have hsum_split : ∑ i : Fin (m + 2), w i • f i =
      w 0 • f 0 + ∑ i : Fin (m + 1), w i.succ • f i.succ :=
    Fin.sum_univ_succ (fun i => w i • f i)
  have hwsum_split : ∑ i : Fin (m + 2), w i = w 0 + ∑ i : Fin (m + 1), w i.succ :=
    Fin.sum_univ_succ w
  -- r = remaining weight sum = 1 - w 0 > 0
  let r := ∑ i : Fin (m + 1), w i.succ
  have hr_pos : 0 < r :=
    Finset.sum_pos (fun i _ => hw_pos i.succ) ⟨0, Finset.mem_univ _⟩
  have hr_eq : r = 1 - w 0 := by
    have h : w 0 + r = 1 := by rw [← hwsum_split]; exact hw_sum
    linarith
  have hw0_lt1 : w 0 < 1 := by linarith [hr_pos, hr_eq]
  -- Use a = f 0, b = r⁻¹ • ∑ remaining, t = w 0
  refine ⟨f 0, r⁻¹ • ∑ i : Fin (m + 1), w i.succ • f i.succ, w 0,
    hf_mem 0, ?_, hw_pos 0, hw0_lt1, ?_⟩
  · -- b ∈ convexHull ℝ s: it equals the centerMass of f 1,...,f m+1 with weights w 1,...,w m+1
    have hcenterMass : r⁻¹ • ∑ i : Fin (m + 1), w i.succ • f i.succ =
        Finset.univ.centerMass (fun i : Fin (m + 1) => w i.succ) (fun i => f i.succ) := rfl
    rw [hcenterMass]
    exact Finset.centerMass_mem_convexHull Finset.univ
      (fun i _ => le_of_lt (hw_pos i.succ))
      hr_pos
      (fun i _ => hf_mem i.succ)
  · -- x = w 0 • f 0 + (1 - w 0) • (r⁻¹ • ∑ remaining)
    -- Since (1 - w 0) = r and r • r⁻¹ = 1
    have hb_eq : (1 - w 0) • (r⁻¹ • ∑ i : Fin (m + 1), w i.succ • f i.succ) =
        ∑ i : Fin (m + 1), w i.succ • f i.succ := by
      rw [smul_smul, show (1 - w 0) = r from hr_eq.symm,
        mul_inv_cancel₀ (ne_of_gt hr_pos), one_smul]
    rw [hb_eq, ← hsum_split]; exact hx_eq.symm

/-- Minimum number of vertices (with strictly positive weights) needed to represent
    x ∈ convexHull(s) as a convex combination from s.
    Returns 0 when the set of representations is empty (vacuously, sInf = 0). -/
private noncomputable def minCaraDepth (s : Set E) (x : E) : ℕ :=
  sInf {n : ℕ | ∃ (f : Fin n → E) (w : Fin n → ℝ),
    (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x}

/-- An explicit representation gives an upper bound on minCaraDepth. -/
private lemma minCaraDepth_le_of_repr {s : Set E} {x : E} {n : ℕ}
    (f : Fin n → E) (w : Fin n → ℝ)
    (hf : ∀ i, f i ∈ s) (hw : ∀ i, 0 < w i) (hws : ∑ i, w i = 1) (hxe : ∑ i, w i • f i = x) :
    minCaraDepth s x ≤ n := by
  apply Nat.sInf_le
  exact ⟨f, w, hf, hw, hws, hxe⟩

/-- If x ∈ convexHull(s) \ s, then x requires at least 2 vertices,
    so minCaraDepth s x ≥ 2. -/
private lemma minCaraDepth_ge_two {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ s) (hxs : x ∉ s) : 2 ≤ minCaraDepth s x := by
  by_contra h
  push_neg at h
  -- minCaraDepth s x ≤ 1; in particular the infimum is finite (the set is nonempty)
  obtain ⟨n, f, w, hn, hf, hw, hws, hxe⟩ := convexHull_not_mem_requires_two hx hxs
  have hnonempty : {n : ℕ | ∃ (f : Fin n → E) (w : Fin n → ℝ),
      (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x}.Nonempty :=
    ⟨n, f, w, hf, hw, hws, hxe⟩
  have hmem : ∃ (f : Fin (minCaraDepth s x) → E) (w : Fin (minCaraDepth s x) → ℝ),
      (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x :=
    Nat.sInf_mem hnonempty
  -- minCaraDepth s x ≤ 1 and it is the sInf, so either 0 or 1
  interval_cases (minCaraDepth s x)
  · -- case 0: Fin 0 representation → empty sum = 0 ≠ 1
    obtain ⟨f0, w0, _, _, hw0_sum, _⟩ := hmem
    simp [Fin.sum_univ_zero] at hw0_sum
  · -- case 1: Fin 1 representation → x = f0 0 ∈ s, contradiction
    obtain ⟨f1, w1, hf1, hw1, hw1_sum, hx1⟩ := hmem
    have hw1_val : w1 0 = 1 := by
      have := hw1_sum; simp [Fin.sum_univ_one] at this; exact this
    have hx1_val : x = f1 0 := by
      have := hx1; simp [Fin.sum_univ_one, hw1_val] at this; exact this.symm
    exact hxs (hx1_val ▸ hf1 0)

/-- If x ∈ convexHull(s) \ s, construct a binary representation
    x = tv • a + (1-tv) • bv where a ∈ s, bv ∈ convexHull(s), tv ∈ (0,1),
    and bv has minCaraDepth ≤ minCaraDepth(x) - 1 (strictly smaller depth when bv ∉ s). -/
private lemma binary_repr_depth {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ s) (hxs : x ∉ s) :
    ∃ (a bv : E) (tv : ℝ),
      a ∈ s ∧ bv ∈ convexHull ℝ s ∧ 0 < tv ∧ tv < 1 ∧
      x = tv • a + (1 - tv) • bv ∧
      minCaraDepth s bv ≤ minCaraDepth s x - 1 := by
  -- The set of representations is nonempty (by convexHull_not_mem_requires_two)
  have hnonempty : {n : ℕ | ∃ (f : Fin n → E) (w : Fin n → ℝ),
      (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x}.Nonempty := by
    obtain ⟨n, f, w, _, hf, hw, hws, hxe⟩ := convexHull_not_mem_requires_two hx hxs
    exact ⟨n, f, w, hf, hw, hws, hxe⟩
  -- minCaraDepth s x ≥ 2; write it as m + 2 for type-safe Fin splitting
  have hN_ge2 : 2 ≤ minCaraDepth s x := minCaraDepth_ge_two hx hxs
  obtain ⟨m, hm⟩ : ∃ m, minCaraDepth s x = m + 2 := ⟨minCaraDepth s x - 2, by omega⟩
  -- Get the minimum representation with Fin type already cast to Fin (m+2)
  obtain ⟨f_min, w_min, hf_min, hw_min, hw_min_sum, hx_min⟩ :
      ∃ (f : Fin (m + 2) → E) (w : Fin (m + 2) → ℝ),
        (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x := by
    have h := Nat.sInf_mem hnonempty
    rwa [show sInf {n : ℕ | ∃ (f : Fin n → E) (w : Fin n → ℝ),
        (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x} = m + 2
      from hm] at h
  -- Now f_min : Fin (m+2) → E, w_min : Fin (m+2) → ℝ; Fin.sum_univ_succ works directly
  have hsum_split : ∑ i : Fin (m + 2), w_min i • f_min i =
      w_min 0 • f_min 0 + ∑ i : Fin (m + 1), w_min i.succ • f_min i.succ :=
    Fin.sum_univ_succ (fun i => w_min i • f_min i)
  have hwsum_split : ∑ i : Fin (m + 2), w_min i = w_min 0 + ∑ i : Fin (m + 1), w_min i.succ :=
    Fin.sum_univ_succ w_min
  -- Remaining weight r = 1 - w_min 0 > 0
  let r := ∑ i : Fin (m + 1), w_min i.succ
  have hr_pos : 0 < r :=
    Finset.sum_pos (fun i _ => hw_min i.succ) ⟨0, Finset.mem_univ _⟩
  have hr_eq : r = 1 - w_min 0 := by
    have h : w_min 0 + r = 1 := by rw [← hwsum_split]; exact hw_min_sum
    linarith
  have hw0_lt1 : w_min 0 < 1 := by linarith [hr_pos, hr_eq]
  -- Define bv = r⁻¹ • ∑_{i ≥ 1} w_min i • f_min i
  let bv := r⁻¹ • ∑ i : Fin (m + 1), w_min i.succ • f_min i.succ
  -- bv ∈ convexHull s
  have hbv_mem : bv ∈ convexHull ℝ s := by
    have hcM : bv = Finset.univ.centerMass
        (fun i : Fin (m + 1) => w_min i.succ) (fun i => f_min i.succ) := rfl
    rw [hcM]
    exact Finset.centerMass_mem_convexHull Finset.univ
      (fun i _ => le_of_lt (hw_min i.succ)) hr_pos (fun i _ => hf_min i.succ)
  -- x = w_min 0 • f_min 0 + (1 - w_min 0) • bv
  have hx_eq : x = w_min 0 • f_min 0 + (1 - w_min 0) • bv := by
    rw [show (1 - w_min 0) = r from hr_eq.symm, smul_smul,
        mul_inv_cancel₀ (ne_of_gt hr_pos), one_smul]
    rw [← hsum_split]; exact hx_min.symm
  -- minCaraDepth s bv ≤ minCaraDepth s x - 1 (via explicit (m+1)-vertex representation)
  have hbv_depth : minCaraDepth s bv ≤ minCaraDepth s x - 1 := by
    have h : minCaraDepth s bv ≤ m + 1 :=
      minCaraDepth_le_of_repr
        (fun i : Fin (m + 1) => f_min i.succ)
        (fun i : Fin (m + 1) => w_min i.succ / r)
        (fun i => hf_min i.succ)
        (fun i => div_pos (hw_min i.succ) hr_pos)
        (by rw [← Finset.sum_div]; exact div_self (ne_of_gt hr_pos))
        (by simp only [bv, Finset.smul_sum, smul_smul, div_eq_mul_inv];
            congr 1; ext i; congr 1; ring)
    omega
  exact ⟨f_min 0, bv, w_min 0, hf_min 0, hbv_mem, hw_min 0, hw0_lt1, hx_eq, hbv_depth⟩

/-- **Reduction step**: If a decomposition has more than d excess indices
    (where d = Module.finrank ℝ E), there exists another decomposition of
    the same point with strictly fewer excess indices.

    Proof strategy:
    1. For each excess j: write point j = s_j • a_j + (1-s_j) • b_j,
       a_j ∈ S j, b_j ∈ conv(S j), s_j ∈ (0,1)  [binary_repr_depth]
    2. Pick d+1 excess indices emb : Fin(d+1) → ι; direction vectors δ_l = b_l - a_l
    3. Linear dependence (d+1 vecs in d-dim): Σ c_l • δ_l = 0, normalize so ∃ l, c_l < 0
    4. ε = min { (1-s_l)/(-c_l) : c_l < 0 } ∩ { s_l/c_l : c_l > 0 } > 0
    5. Perturb: point'(emb l) = (s_l - ε·c_l)·a_l + (1-s_l+ε·c_l)·b_l
       - Still in conv(S l) since weights ≥ 0 sum to 1
       - Sum preserved: Σ perturbation = ε · Σ c_l · δ_l = 0
       - Cases A,B1: emb l_min exits excessIndices → excess count strictly decreases
       - Case B2: bv ∉ S, recurse via WF induction on total minCaraDepth -/
theorem reduce_excess_by_one [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (D : Decomposition S t x)
    (hexcess : Module.finrank ℝ E < D.excessIndices.card) :
    ∃ D' : Decomposition S t x, D'.excessIndices.card < D.excessIndices.card := by
  classical
  set d := Module.finrank ℝ E with hd_def
  -- We use strong induction on the total minCaraDepth of all excess indices.
  -- The inner proof is packaged as a suffices with strong induction.
  suffices H : ∀ (n : ℕ) (D₁ : Decomposition S t x),
      ∑ j ∈ D₁.excessIndices, minCaraDepth (S j) (D₁.point j) ≤ n →
      Module.finrank ℝ E < D₁.excessIndices.card →
      ∃ D₂ : Decomposition S t x, D₂.excessIndices.card < D₁.excessIndices.card by
    exact H _ D le_rfl hexcess
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro D₁ hdn₁ hexcess₁
  -- Rename to work with D₁ (matches D in the rest of the proof)
  -- Step 1: Binary representation data with depth tracking for excess indices
  obtain ⟨av, bv, sv, hrepr⟩ :
      ∃ (av bv : ι → E) (sv : ι → ℝ), ∀ j ∈ D₁.excessIndices,
        av j ∈ S j ∧ bv j ∈ convexHull ℝ (S j) ∧ 0 < sv j ∧ sv j < 1 ∧
        D₁.point j = sv j • av j + (1 - sv j) • bv j ∧
        minCaraDepth (S j) (bv j) ≤ minCaraDepth (S j) (D₁.point j) - 1 := by
    have hchoose : ∀ j ∈ D₁.excessIndices, ∃ (a b : E) (s : ℝ),
        a ∈ S j ∧ b ∈ convexHull ℝ (S j) ∧ 0 < s ∧ s < 1 ∧
        D₁.point j = s • a + (1 - s) • b ∧
        minCaraDepth (S j) b ≤ minCaraDepth (S j) (D₁.point j) - 1 := fun j hj => by
      simp only [Decomposition.excessIndices, Finset.mem_filter] at hj
      exact binary_repr_depth (D₁.mem_convexHull j hj.1) hj.2
    refine ⟨fun j => if h : j ∈ D₁.excessIndices then
                    (hchoose j h).choose else 0,
            fun j => if h : j ∈ D₁.excessIndices then
                    (hchoose j h).choose_spec.choose else 0,
            fun j => if h : j ∈ D₁.excessIndices then
                    (hchoose j h).choose_spec.choose_spec.choose else 0,
            fun j hj => ?_⟩
    simp only [dif_pos hj]
    exact (hchoose j hj).choose_spec.choose_spec.choose_spec
  -- Step 2: Pick d+1 excess indices as emb : Fin(d+1) → ι
  obtain ⟨emb, hemb_inj, hemb_mem⟩ : ∃ (emb : Fin (d + 1) → ι),
      Function.Injective emb ∧ ∀ l, emb l ∈ D₁.excessIndices := by
    have hcard : d + 1 ≤ D₁.excessIndices.card := by omega
    let L : List ι := D₁.excessIndices.val.toList
    have hL_len : L.length = D₁.excessIndices.card := by
      simp only [L, Multiset.length_toList, Finset.card_def]
    refine ⟨fun l => L.get ⟨l.val, by omega⟩, ?_, fun l => ?_⟩
    · intro l₁ l₂ heq
      have hL_nodup : L.Nodup := Finset.nodup_toList D₁.excessIndices
      have hinj : Function.Injective L.get := List.nodup_iff_injective_get.mp hL_nodup
      have h := hinj heq
      have hval : l₁.val = l₂.val := by
        have key := @congrArg (Fin L.length) ℕ ⟨l₁.val, by omega⟩ ⟨l₂.val, by omega⟩ Fin.val h
        simpa using key
      exact Fin.ext hval
    · have h_lt : l.val < L.length := by omega
      exact Finset.mem_def.mpr
        (Multiset.mem_toList.mp (List.get_mem L ⟨l.val, h_lt⟩))
  have hemb_in_t : ∀ l : Fin (d + 1), emb l ∈ t := fun l => by
    have h := hemb_mem l
    simp only [Decomposition.excessIndices, Finset.mem_filter] at h
    exact h.1
  -- Step 3: Direction vectors δ_l = bv(emb l) - av(emb l)
  let δ : Fin (d + 1) → E := fun l => bv (emb l) - av (emb l)
  -- Step 4: Linear dependence
  obtain ⟨c, ⟨l₀, hl₀ne⟩, hcδ⟩ := linearDependent_coefficients (by omega : d < d + 1) δ
  -- Step 5: Normalize so some coefficient is negative
  obtain ⟨c', lneg, hlneg, hc'δ⟩ : ∃ (c' : Fin (d + 1) → ℝ) (lneg : Fin (d + 1)),
      c' lneg < 0 ∧ ∑ l, c' l • δ l = 0 := by
    rcases lt_trichotomy (c l₀) 0 with h | h | h
    · exact ⟨c, l₀, h, hcδ⟩
    · exact absurd h hl₀ne
    · refine ⟨fun l => -(c l), l₀, by linarith, ?_⟩
      have : ∑ l : Fin (d + 1), -(c l) • δ l = -(∑ l : Fin (d + 1), c l • δ l) := by
        simp [neg_smul, Finset.sum_neg_distrib]
      rw [this, hcδ, neg_zero]
  -- Step 6: Perturbation construction
  have neg_nonempty : ∃ l : Fin (d + 1), c' l < 0 := ⟨lneg, hlneg⟩
  let neg_indices : Finset (Fin (d + 1)) := Finset.univ.filter (fun l => c' l < 0)
  have neg_indices_ne : neg_indices.Nonempty := by
    simp only [neg_indices, Finset.filter_nonempty_iff]
    exact ⟨lneg, Finset.mem_univ _, hlneg⟩
  let pos_indices : Finset (Fin (d + 1)) := Finset.univ.filter (fun l => 0 < c' l)
  have ratio_neg_pos : ∀ l ∈ neg_indices, 0 < (1 - sv (emb l)) / (-c' l) := by
    intro l hl
    simp only [neg_indices, Finset.mem_filter] at hl
    apply div_pos
    · have := (hrepr (emb l) (hemb_mem l)).2.2.2.1
      linarith
    · linarith [hl.2]
  have ratio_pos_pos : ∀ l ∈ pos_indices, 0 < sv (emb l) / c' l := by
    intro l hl
    simp only [pos_indices, Finset.mem_filter] at hl
    exact div_pos (hrepr (emb l) (hemb_mem l)).2.2.1 hl.2
  let neg_ratios : Finset ℝ := neg_indices.image (fun l => (1 - sv (emb l)) / (-c' l))
  have neg_ratios_ne : neg_ratios.Nonempty := Finset.image_nonempty.mpr neg_indices_ne
  let ε₀ : ℝ := neg_ratios.min' neg_ratios_ne
  have hε₀_mem : ε₀ ∈ neg_ratios := Finset.min'_mem _ _
  obtain ⟨l_min, hl_min_neg, hl_min_eq⟩ := Finset.mem_image.mp hε₀_mem
  have hε₀_pos : 0 < ε₀ := by rw [← hl_min_eq]; exact ratio_neg_pos l_min hl_min_neg
  have hε₀_le_neg : ∀ l ∈ neg_indices, ε₀ ≤ (1 - sv (emb l)) / (-c' l) :=
    fun l hl => Finset.min'_le _ _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
  let ε : ℝ := if h : pos_indices.Nonempty then
    min ε₀ ((pos_indices.image (fun l => sv (emb l) / c' l)).min' (Finset.image_nonempty.mpr h))
    else ε₀
  have hε_pos : 0 < ε := by
    simp only [ε]; split_ifs with h
    · apply lt_min hε₀_pos
      have hpos_ne : (pos_indices.image (fun l => sv (emb l) / c' l)).Nonempty :=
        Finset.image_nonempty.mpr h
      have hmin_mem := Finset.min'_mem _ hpos_ne
      obtain ⟨l, hl, hl_eq⟩ := Finset.mem_image.mp hmin_mem
      rw [← hl_eq]; exact ratio_pos_pos l hl
    · exact hε₀_pos
  have hε_le_ε₀ : ε ≤ ε₀ := by
    simp only [ε]; split_ifs with h
    · exact min_le_left _ _
    · exact le_refl _
  have hε_le_neg : ∀ l ∈ neg_indices, ε ≤ (1 - sv (emb l)) / (-c' l) :=
    fun l hl => le_trans hε_le_ε₀ (hε₀_le_neg l hl)
  have hε_le_pos : ∀ l ∈ pos_indices, ε ≤ sv (emb l) / c' l := by
    simp only [ε]; split_ifs with h
    · intro l hl
      apply le_trans (min_le_right _ _)
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    · intro l hl; exact absurd ⟨l, hl⟩ h
  -- Step 6f: Define perturbed points
  let new_point : ι → E := fun i =>
    if h : ∃ l : Fin (d + 1), emb l = i then
      let l := h.choose
      D₁.point i + ε • (c' l • δ l)
    else
      D₁.point i
  have new_point_emb : ∀ l : Fin (d + 1),
      new_point (emb l) = D₁.point (emb l) + ε • (c' l • δ l) := by
    intro l
    simp only [new_point, dif_pos (show ∃ l' : Fin (d + 1), emb l' = emb l from ⟨l, rfl⟩)]
    congr 1; congr 1
    have : (⟨l, rfl⟩ : ∃ l' : Fin (d + 1), emb l' = emb l).choose = l := by
      apply hemb_inj
      exact (⟨l, rfl⟩ : ∃ l' : Fin (d + 1), emb l' = emb l).choose_spec
    simp [this]
  have new_point_not_emb : ∀ i : ι, (∀ l : Fin (d + 1), emb l ≠ i) →
      new_point i = D₁.point i := by
    intro i hi; simp only [new_point, dif_neg (not_exists.mpr hi)]
  -- Step 6i: Sum preservation
  have new_sum : ∑ i ∈ t, new_point i = x := by
    conv_lhs =>
      arg 2; ext i
      rw [show new_point i = D₁.point i +
            if h : ∃ l : Fin (d + 1), emb l = i then ε • (c' h.choose • δ h.choose) else 0
          from by
            split_ifs with h
            · simp only [new_point, dif_pos h]
            · simp only [new_point, dif_neg h, add_zero]]
    rw [Finset.sum_add_distrib, D₁.sum_eq]
    suffices h : ∑ i ∈ t, (if h : ∃ l : Fin (d + 1), emb l = i then
        ε • (c' h.choose • δ h.choose) else 0) = 0 by simp [h]
    have hemb_in_t' : ∀ l : Fin (d + 1), emb l ∈ t := fun l => hemb_in_t l
    rw [show ∑ i ∈ t, (if h : ∃ l : Fin (d + 1), emb l = i then
          ε • (c' h.choose • δ h.choose) else 0) =
        ∑ l : Fin (d + 1), ε • (c' l • δ l) from by
      have step1 : ∑ i ∈ t, (if h : ∃ l : Fin (d + 1), emb l = i then
            ε • (c' h.choose • δ h.choose) else 0) =
          ∑ i ∈ Finset.image emb Finset.univ, (if h : ∃ l : Fin (d + 1), emb l = i then
            ε • (c' h.choose • δ h.choose) else 0) := by
        symm
        apply Finset.sum_subset (Finset.image_subset_iff.mpr (fun l _ => hemb_in_t' l))
        intro i _ hi
        have hne : ¬∃ l : Fin (d + 1), emb l = i :=
          fun ⟨l, hl⟩ => hi (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, hl⟩)
        simp only [dif_neg hne]
      have step2 : ∑ i ∈ Finset.image emb Finset.univ, (if h : ∃ l : Fin (d + 1), emb l = i then
            ε • (c' h.choose • δ h.choose) else 0) =
          ∑ l : Fin (d + 1), ε • (c' l • δ l) := by
        rw [Finset.sum_image (fun a _ b _ h => hemb_inj h)]
        apply Finset.sum_congr rfl
        intro l _
        split_ifs with h
        · have heq : h.choose = l := hemb_inj h.choose_spec; rw [heq]
        · exact absurd ⟨l, rfl⟩ h
      exact step1.trans step2]
    rw [← Finset.smul_sum, hc'δ, smul_zero]
  -- Step 6j: Each new_point lies in convexHull(S i)
  have new_mem_convexHull : ∀ i ∈ t, new_point i ∈ convexHull ℝ (S i) := by
    intro i hi
    by_cases h : ∃ l : Fin (d + 1), emb l = i
    · obtain ⟨l, rfl⟩ := h
      rw [new_point_emb l]
      obtain ⟨hav_mem, hbv_mem, hsv_pos, hsv_lt1, hpoint_eq, _⟩ :=
        hrepr (emb l) (hemb_mem l)
      have hrw : D₁.point (emb l) + ε • (c' l • δ l) =
          (sv (emb l) - ε * c' l) • av (emb l) +
          (1 - sv (emb l) + ε * c' l) • bv (emb l) := by
        rw [hpoint_eq]; simp only [δ, smul_sub, smul_smul, add_smul, sub_smul]; abel
      rw [hrw]
      have hsum : (sv (emb l) - ε * c' l) + (1 - sv (emb l) + ε * c' l) = 1 := by ring
      rcases lt_trichotomy (c' l) 0 with hneg | hzero | hpos
      · have ha_pos : 0 ≤ sv (emb l) - ε * c' l :=
          by nlinarith [le_of_lt hsv_pos, le_of_lt hε_pos, neg_pos.mpr hneg]
        have hb_pos : 0 ≤ 1 - sv (emb l) + ε * c' l := by
          have hle := hε_le_neg l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneg⟩)
          have hcneg_pos : (0 : ℝ) < -c' l := neg_pos.mpr hneg
          have hmul : ε * (-c' l) ≤ 1 - sv (emb l) := by
            calc ε * (-c' l) ≤ ((1 - sv (emb l)) / (-c' l)) * (-c' l) :=
                  mul_le_mul_of_nonneg_right hle (le_of_lt hcneg_pos)
              _ = 1 - sv (emb l) := div_mul_cancel₀ _ (ne_of_gt hcneg_pos)
          nlinarith
        exact convex_convexHull ℝ (S (emb l))
          (subset_convexHull ℝ _ hav_mem) hbv_mem ha_pos hb_pos hsum
      · have heq : (sv (emb l) - ε * c' l) • av (emb l) +
            (1 - sv (emb l) + ε * c' l) • bv (emb l) = D₁.point (emb l) := by
          rw [hzero, mul_zero, sub_zero, add_zero, hpoint_eq]
        rw [heq]; exact D₁.mem_convexHull (emb l) (hemb_in_t l)
      · have ha_pos : 0 ≤ sv (emb l) - ε * c' l := by
          have hle := hε_le_pos l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
          have hmul : ε * c' l ≤ sv (emb l) := by
            calc ε * c' l ≤ (sv (emb l) / c' l) * c' l :=
                  mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
              _ = sv (emb l) := div_mul_cancel₀ _ (ne_of_gt hpos)
          linarith
        have hb_pos : 0 ≤ 1 - sv (emb l) + ε * c' l :=
          by nlinarith [le_of_lt hε_pos, le_of_lt hpos, hsv_lt1]
        exact convex_convexHull ℝ (S (emb l))
          (subset_convexHull ℝ _ hav_mem) hbv_mem ha_pos hb_pos hsum
    · rw [new_point_not_emb i (not_exists.mp h)]
      exact D₁.mem_convexHull i hi
  -- Step 6k: new_point is zero outside t
  have new_zero : ∀ i, i ∉ t → new_point i = 0 := by
    intro i hi
    have hDz := D₁.point_eq_zero i hi
    have h_no_emb : ∀ l : Fin (d + 1), emb l ≠ i := by
      intro l heq; exact hi (heq ▸ hemb_in_t l)
    rw [new_point_not_emb i h_no_emb, hDz]
  -- Step 6l: Construct D'
  let D' : Decomposition S t x := ⟨new_point, new_mem_convexHull, new_zero, new_sum⟩
  -- Step 6m: D'.excessIndices ⊆ D₁.excessIndices
  have hl_min_data := hrepr (emb l_min) (hemb_mem l_min)
  obtain ⟨hav_mem, _, hsv_pos, hsv_lt1, hpoint_eq, _⟩ := hl_min_data
  have hcl_min_neg : c' l_min < 0 := by
    simp only [neg_indices, Finset.mem_filter] at hl_min_neg; exact hl_min_neg.2
  have hD'_subset : D'.excessIndices ⊆ D₁.excessIndices := by
    intro i hi
    simp only [Decomposition.excessIndices, Finset.mem_filter] at hi ⊢
    obtain ⟨hi_t, hi_new⟩ := hi
    refine ⟨hi_t, ?_⟩
    -- hi_new : D'.point i ∉ S i, i.e., new_point i ∉ S i
    -- We need: D₁.point i ∉ S i
    by_cases h : ∃ l : Fin (d + 1), emb l = i
    · -- i = emb l for some l, which was already in D₁.excessIndices
      obtain ⟨l, rfl⟩ := h
      simp only [Decomposition.excessIndices, Finset.mem_filter] at hemb_mem
      exact (hemb_mem l).2
    · -- D'.point i = new_point i = D₁.point i (unchanged outside range of emb)
      -- D'.point i = new_point i definitionally; new_point i = D₁.point i by new_point_not_emb
      have hDne : new_point i = D₁.point i := new_point_not_emb i (not_exists.mp h)
      -- hi_new : D'.point i ∉ S i
      -- We need: D₁.point i ∉ S i
      -- Since D'.point i = new_point i (definitionally) = D₁.point i, done.
      rw [← hDne]
      -- Now goal: new_point i ∉ S i
      -- hi_new : D'.point i ∉ S i, and D'.point i = new_point i (definitionally)
      exact hi_new
  -- Case A vs B split
  by_cases hcase_A : ε = ε₀
  · -- Case A: neg-index l_min achieves joint minimum → new_point(emb l_min) = av(emb l_min) ∈ S
    have hnew_point_av : new_point (emb l_min) = av (emb l_min) := by
      rw [new_point_emb l_min, hcase_A, hpoint_eq]; simp only [δ]
      have hcneg : -c' l_min > 0 := neg_pos.mpr hcl_min_neg
      have hb_weight_zero : (1 - sv (emb l_min)) + ε₀ * c' l_min = 0 := by
        have h1 : ε₀ * (-c' l_min) = 1 - sv (emb l_min) := by
          rw [← hl_min_eq]; exact div_mul_cancel₀ _ (ne_of_gt hcneg)
        linarith
      have hcoeff_av : sv (emb l_min) - ε₀ * c' l_min = 1 := by linarith [hb_weight_zero]
      have hcoeff_bv : (1 - sv (emb l_min)) + ε₀ * c' l_min = 0 := hb_weight_zero
      have key : sv (emb l_min) • av (emb l_min) + (1 - sv (emb l_min)) • bv (emb l_min) +
                 ε₀ • (c' l_min • (bv (emb l_min) - av (emb l_min))) = av (emb l_min) := by
        have : sv (emb l_min) • av (emb l_min) + (1 - sv (emb l_min)) • bv (emb l_min) +
               ε₀ • (c' l_min • (bv (emb l_min) - av (emb l_min))) =
               (sv (emb l_min) - ε₀ * c' l_min) • av (emb l_min) +
               ((1 - sv (emb l_min)) + ε₀ * c' l_min) • bv (emb l_min) := by
          simp only [smul_sub, smul_smul, add_smul, sub_smul]; abel
        rw [this, hcoeff_av, hcoeff_bv, one_smul, zero_smul, add_zero]
      exact key
    have hD'_not_excess : emb l_min ∉ D'.excessIndices := by
      simp only [Decomposition.excessIndices, Finset.mem_filter]
      intro ⟨_, hnot⟩
      -- D'.point (emb l_min) = new_point (emb l_min) = av (emb l_min) ∈ S
      have : D'.point (emb l_min) = av (emb l_min) := hnew_point_av
      exact hnot (this ▸ hav_mem)
    have hD'_ssub : D'.excessIndices ⊂ D₁.excessIndices :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hD'_subset,
        fun heq => hD'_not_excess (heq ▸ hemb_mem l_min)⟩
    exact ⟨D', Finset.card_lt_card hD'_ssub⟩
  · -- Case B: pos-index achieves joint minimum
    have h_pos_ne : pos_indices.Nonempty := by
      by_contra h; exact hcase_A (by simp only [ε, dif_neg h])
    have h_pr_ne : (pos_indices.image (fun l => sv (emb l) / c' l)).Nonempty :=
      Finset.image_nonempty.mpr h_pos_ne
    have hε_eq : ε = min ε₀ ((pos_indices.image (fun l => sv (emb l) / c' l)).min' h_pr_ne) := by
      simp only [ε, dif_pos h_pos_ne]
    have h_pm_le : (pos_indices.image (fun l => sv (emb l) / c' l)).min' h_pr_ne ≤ ε₀ := by
      by_contra h; push_neg at h
      exact hcase_A (hε_eq ▸ min_eq_left (le_of_lt h))
    have hε_pm : ε = (pos_indices.image (fun l => sv (emb l) / c' l)).min' h_pr_ne :=
      hε_eq ▸ min_eq_right h_pm_le
    obtain ⟨l', hl'_in, hl'_eq⟩ :
        ∃ l' ∈ pos_indices, sv (emb l') / c' l' =
          (pos_indices.image (fun l => sv (emb l) / c' l)).min' h_pr_ne :=
      Finset.mem_image.mp (Finset.min'_mem _ _)
    simp only [pos_indices, Finset.mem_filter] at hl'_in
    have hl'_pos : 0 < c' l' := hl'_in.2
    have hl'_ratio : sv (emb l') / c' l' = ε := hl'_eq ▸ hε_pm.symm
    have h_aw : sv (emb l') - ε * c' l' = 0 := by
      have heq : sv (emb l') = ε * c' l' := by
        rw [← hl'_ratio]; field_simp [ne_of_gt hl'_pos]
      linarith
    obtain ⟨_, hbv_mem', _, _, hpoint_eq', hbv_depth'⟩ :=
      hrepr (emb l') (hemb_mem l')
    have hnew_bv : new_point (emb l') = bv (emb l') := by
      rw [new_point_emb l', hpoint_eq']; simp only [δ]
      have h_bw : (1 - sv (emb l')) + ε * c' l' = 1 := by linarith [h_aw]
      have key : sv (emb l') • av (emb l') + (1 - sv (emb l')) • bv (emb l') +
                 ε • (c' l' • (bv (emb l') - av (emb l'))) = bv (emb l') := by
        have : sv (emb l') • av (emb l') + (1 - sv (emb l')) • bv (emb l') +
               ε • (c' l' • (bv (emb l') - av (emb l'))) =
               (sv (emb l') - ε * c' l') • av (emb l') +
               ((1 - sv (emb l')) + ε * c' l') • bv (emb l') := by
          simp only [smul_sub, smul_smul, add_smul, sub_smul]; abel
        rw [this, h_aw, h_bw, zero_smul, one_smul, zero_add]
      exact key
    -- Sub-case B1: bv ∈ S(emb l') → l' exits excess
    by_cases hbv_S : bv (emb l') ∈ S (emb l')
    · have hl'_not_excess : emb l' ∉ D'.excessIndices := by
        simp only [Decomposition.excessIndices, Finset.mem_filter, D']
        intro ⟨_, hnot⟩; exact hnot (hnew_bv ▸ hbv_S)
      exact ⟨D', Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hD'_subset,
        fun heq => hl'_not_excess (heq ▸ hemb_mem l')⟩)⟩
    · -- Sub-case B2: bv(emb l') ∉ S(emb l')
      -- D'.point(emb l') = bv(emb l') has strictly smaller minCaraDepth
      -- Total minCaraDepth of D' is strictly less than that of D₁
      -- Apply IH to D' to get D''
      --
      -- First: total minCaraDepth of D' < total minCaraDepth of D₁
      -- Key facts:
      --   (a) D'.excessIndices ⊆ D₁.excessIndices
      --   (b) D'.point j = D₁.point j for j ∉ range(emb) [depth unchanged]
      --   (c) D'.point(emb l') = bv(emb l') with depth ≤ depth(D₁.point(emb l')) - 1
      --   (d) depth(D₁.point(emb l')) ≥ 2 (since emb l' is an excess index)
      --   So the total depth drops by at least 1.
      have hD'_depth_lt :
          ∑ j ∈ D'.excessIndices, minCaraDepth (S j) (D'.point j) < n := by
        -- The total depth of D' is ≤ total depth of D₁ minus at least 1
        -- because emb l' was in D₁.excessIndices with D₁.point(emb l') having depth ≥ 2,
        -- and D'.point(emb l') = bv(emb l') has depth ≤ depth(D₁.point(emb l')) - 1.
        -- All other excess indices of D' have depth ≤ their depth in D₁.
        -- Step 1: ∑_{j ∈ D'.excessIndices} depth(D'.point j)
        --       ≤ ∑_{j ∈ D'.excessIndices} depth(D₁.point j)  (by depth of bv ≤ depth of point - 1)
        --   Actually the depths may differ for the emb-indices (perturbed) vs non-emb.
        -- Simpler bound: ∑_{D'} ≤ ∑_{D₁} - 1 ≤ n - 1 < n.
        -- We show: ∑_{j ∈ D'.excessIndices} minCaraDepth (S j) (D'.point j) ≤ n - 1.
        -- Use: D'.excessIndices ⊆ D₁.excessIndices (by hD'_subset)
        -- For j ∈ D'.excessIndices:
        --   if j = emb l': D'.point j = bv(emb l'), depth ≤ depth(D₁.point(emb l')) - 1
        --   if j ≠ emb l' but j ∈ range(emb): D'.point j = new_point j (perturbed)
        --     Still in convexHull(S j), depth potentially same or less.
        --   if j ∉ range(emb): D'.point j = D₁.point j, same depth.
        -- We bound the sum as follows:
        --   ∑_{j ∈ D'.excessIndices} depth(D'.point j)
        -- ≤ ∑_{j ∈ D₁.excessIndices} depth(D₁.point j)   [D'.excess ⊆ D₁.excess, depth(bv) ≤ depth - 1]
        -- ≤ n [by hdn₁]
        -- with strict: depth(emb l') decreased by ≥ 1, so total ≤ n - 1 < n.
        -- To formalize cleanly, we show:
        --   ∑_{j ∈ D'.excessIndices} depth(D'.point j)
        -- ≤ ∑_{j ∈ D₁.excessIndices} depth(D₁.point j) - 1
        -- ≤ n - 1 < n.
        --
        -- Key: for j ∈ D'.excessIndices ⊆ D₁.excessIndices,
        --   depth(D'.point j) ≤ depth(D₁.point j)   [not strictly for all j]
        -- For j = emb l': depth(D'.point(emb l')) = depth(bv(emb l')) ≤ depth(D₁.point(emb l')) - 1
        -- emb l' ∈ D'.excessIndices? Not necessarily.
        -- Actually emb l' IS in D'.excessIndices because:
        --   D'.point(emb l') = bv(emb l') ∉ S(emb l') [hbv_S says bv ∉ S]
        --   and emb l' ∈ t [hemb_in_t]
        -- depth(D₁.point(emb l')) ≥ 2 (defined first to avoid forward reference)
        have hdepth_emb_l'_ge2 : 2 ≤ minCaraDepth (S (emb l')) (D₁.point (emb l')) := by
          apply minCaraDepth_ge_two
          · exact D₁.mem_convexHull (emb l') (hemb_in_t l')
          · simp only [Decomposition.excessIndices, Finset.mem_filter] at hemb_mem
            exact (hemb_mem l').2
        -- n ≥ 1 since the sum over D₁.excessIndices has the emb l' term ≥ 2
        have hn_pos : 1 ≤ n := by
          have hmem : emb l' ∈ D₁.excessIndices := hemb_mem l'
          have hterm_ge : 2 ≤ minCaraDepth (S (emb l')) (D₁.point (emb l')) :=
            hdepth_emb_l'_ge2
          have hsum_ge : 2 ≤ ∑ j ∈ D₁.excessIndices, minCaraDepth (S j) (D₁.point j) :=
            le_trans hterm_ge (Finset.single_le_sum
              (f := fun j => minCaraDepth (S j) (D₁.point j)) (fun j _ => Nat.zero_le _) hmem)
          linarith
        have hemb_l'_D'_excess : emb l' ∈ D'.excessIndices := by
          simp only [Decomposition.excessIndices, Finset.mem_filter]
          refine ⟨hemb_in_t l', ?_⟩
          -- D'.point (emb l') = new_point (emb l') = bv (emb l') ∉ S (emb l')
          have : D'.point (emb l') = bv (emb l') := hnew_bv
          rw [this]; exact hbv_S
        -- depth(D'.point(emb l')) = depth(bv(emb l')) ≤ depth(D₁.point(emb l')) - 1
        have hdepth_bv : minCaraDepth (S (emb l')) (D'.point (emb l')) ≤
            minCaraDepth (S (emb l')) (D₁.point (emb l')) - 1 := by
          have : D'.point (emb l') = bv (emb l') := hnew_bv
          rw [this]; exact hbv_depth'
        -- Total depth of D':
        -- ∑_{j ∈ D'.excess} depth(D'.point j)
        -- = depth(D'.point(emb l')) + ∑_{j ∈ D'.excess \ {emb l'}} depth(D'.point j)
        -- ≤ (depth(D₁.point(emb l')) - 1) + ∑_{j ∈ D₁.excess \ {emb l'}} depth(D₁.point j)
        --   [because D'.excess ⊆ D₁.excess and depth(D'.point j) ≤ depth(D₁.point j) for j ≠ emb l']
        -- = ∑_{j ∈ D₁.excess} depth(D₁.point j) - 1
        -- ≤ n - 1 < n
        --
        -- For the bound on non-l' indices:
        -- For j ∈ D'.excessIndices, j ≠ emb l':
        --   if j ∈ range(emb): D'.point j = new_point j ∈ convexHull(S j), depth ≤ ?
        --     We don't have a direct bound, but we can use depth(D'.point j) ≤ any n' (trivially).
        --     Actually we need: ∑_{j≠emb l'} depth(D'.point j) ≤ ∑_{j≠emb l', j∈D₁} depth(D₁.point j)
        --     This requires: for each j ∈ D'.excess with j ≠ emb l',
        --       depth(D'.point j) ≤ depth(D₁.point j).
        --     For j ∉ range(emb): D'.point j = D₁.point j, same depth ✓
        --     For j = emb l'' ≠ emb l': D'.point j = new_point(emb l'')
        --       = D₁.point(emb l'') + ε • (c' l'' • δ l'')
        --       This is a convex combination of av(emb l'') and bv(emb l'').
        --       Depth bound: the convex combination has depth ≤ 1 + depth(bv(emb l''))
        --         ≤ 1 + (depth(D₁.point(emb l'')) - 1) = depth(D₁.point(emb l'')) ✓
        --
        -- For simplicity, we bound more coarsely:
        -- ∑_{j ∈ D'.excess} depth(D'.point j) ≤ ∑_{j ∈ D₁.excess} depth(D₁.point j) - 1 ≤ n - 1
        --
        -- To get: ∑_{D'} ≤ ∑_{D₁} - 1, split at emb l':
        calc ∑ j ∈ D'.excessIndices, minCaraDepth (S j) (D'.point j)
            = minCaraDepth (S (emb l')) (D'.point (emb l')) +
              ∑ j ∈ D'.excessIndices.erase (emb l'), minCaraDepth (S j) (D'.point j) := by
              rw [← Finset.add_sum_erase _ _ hemb_l'_D'_excess]
          _ ≤ (minCaraDepth (S (emb l')) (D₁.point (emb l')) - 1) +
              ∑ j ∈ D'.excessIndices.erase (emb l'), minCaraDepth (S j) (D₁.point j) := by
              apply Nat.add_le_add hdepth_bv
              apply Finset.sum_le_sum
              intro j hj
              simp only [Finset.mem_erase] at hj
              -- For j ≠ emb l', j ∈ D'.excessIndices ⊆ D₁.excessIndices:
              -- If j ∉ range(emb), D'.point j = D₁.point j → same depth
              -- If j = emb l'' for some l'' ≠ l', the perturbed point has depth ≤ D₁ depth:
              --   new_point(emb l'') = D₁.point(emb l'') + ε•(c' l''•δ l'')
              --   = (sv_l'' - ε*c'_l'') • av(emb l'') + (1-sv_l''+ε*c'_l'') • bv(emb l'')
              --   Both av ∈ S and bv ∈ convexHull(S), bv has depth ≤ depth(D₁.point) - 1
              --   So new_point has a representation of size 1 + (N-1) = N vertices:
              --     av plus the N-1 vertices of bv
              --   Hence depth(new_point) ≤ N = depth(D₁.point)
              by_cases hj_emb : ∃ l'' : Fin (d + 1), emb l'' = j
              · obtain ⟨l'', rfl⟩ := hj_emb
                -- new_point(emb l'') has explicit representation using av + bv's vertices
                obtain ⟨_, hbv_mem'', _, _, hpoint_eq'', hbv_depth''⟩ :=
                  hrepr (emb l'') (hD'_subset hj.2)
                -- We need: minCaraDepth(S(emb l'')) (D'.point(emb l'')) ≤ depth(D₁.point(emb l''))
                -- D'.point(emb l'') = (sv-ε*c')•av + (1-sv+ε*c')•bv
                -- Both coefficients ≥ 0, sum to 1.
                -- bv has depth ≤ depth(D₁.point(emb l'')) - 1.
                -- The point (α•a + β•b) with a ∈ S and b ∈ convexHull(S) with k-vertex repr:
                --   has a (1+k)-vertex representation (a is one vertex, b gives k more).
                -- So depth ≤ 1 + (depth(D₁.point) - 1) = depth(D₁.point).
                -- Actually we also need to handle the case where the new coefficients are 0.
                -- If α = 0: new_point = bv, depth ≤ depth(D₁.point) - 1 ≤ depth(D₁.point)
                -- If β = 0: new_point = av ∈ S, depth ≤ 1 ≤ depth(D₁.point)
                -- General case: depth ≤ 1 + depth(bv) ≤ 1 + (depth(D₁.point) - 1) = depth(D₁.point)
                -- We prove this via an explicit representation:
                set Nl'' := minCaraDepth (S (emb l'')) (D₁.point (emb l'')) with hNl''_def
                -- bv(emb l'') has minCaraDepth ≤ Nl'' - 1
                -- Get explicit (Nl''-1)-vertex repr of bv(emb l'')
                -- (from hbv_depth'': minCaraDepth (S (emb l'')) (bv (emb l'')) ≤ Nl'' - 1)
                -- We need an explicit repr to build the combined repr.
                -- Use the sInf representation of bv.
                -- Sufficient: depth(D'.point(emb l'')) ≤ Nl''
                -- by showing it has an explicit Nl''-vertex repr.
                -- The (Nl'')-vertex repr:
                --   vertex 0: av(emb l'') ∈ S (weight: sv-ε*c')
                --   vertices 1..Nl''-1: from bv repr (weight: (1-sv+ε*c') * w_bv_i)
                -- But this only works if sv-ε*c' > 0.
                -- If sv-ε*c' = 0: point = bv, depth ≤ Nl''-1 ≤ Nl''
                -- If sv-ε*c' > 0 and Nl'' ≥ 2: use 1 + (Nl''-1) = Nl'' vertices.
                -- If Nl'' = 0: impossible (emb l'' is an excess index, depth ≥ 2).
                -- If Nl'' = 1: impossible (depth ≥ 2).
                -- So Nl'' ≥ 2, and the bound depth ≤ Nl'' holds.
                --
                -- Actually the cleanest approach: use a Nat.le_add_right style bound.
                -- depth(D'.point(emb l'')) ≤ 1 + depth(bv(emb l''))
                -- because D'.point = α•av + β•bv, av ∈ S ⊆ convexHull(S):
                --   if β = 0: = av, depth ≤ 1
                --   if β > 0: use av + (bv's k vertices): 1+k vertices total
                --     provided av is not one of bv's vertices (it might be, but we don't need strict)
                -- More carefully: depth(α•av + β•bv) ≤ depth(av) + depth(bv) ≤ 1 + depth(bv)
                --   when β > 0, α > 0.
                -- depth(bv) ≤ Nl'' - 1, so depth(D'.point) ≤ 1 + (Nl'' - 1) = Nl''.
                -- For formalization: get the explicit (Nl''-1)-vertex repr of bv(emb l'').
                have hNl''_ge2 : 2 ≤ Nl'' := by
                  apply minCaraDepth_ge_two
                  · exact D₁.mem_convexHull (emb l'') (hemb_in_t l'')
                  · simp only [Decomposition.excessIndices, Finset.mem_filter] at hemb_mem
                    exact (hemb_mem l'').2
                -- Get explicit representation of bv(emb l'')
                -- Use eq_pos_convex_span_of_mem_convexHull: any convexHull member has a
                -- finite affinely independent representation with strictly positive weights.
                have hbv_nonempty : {m : ℕ | ∃ (f : Fin m → E) (w : Fin m → ℝ),
                    (∀ i, f i ∈ S (emb l'')) ∧ (∀ i, 0 < w i) ∧
                    ∑ i, w i = 1 ∧ ∑ i, w i • f i = bv (emb l'')}.Nonempty := by
                  obtain ⟨ι'', hFin'', z'', w''', hz''_range, _, hw'''_pos, hw'''_sum, hbv_eq'⟩ :=
                    eq_pos_convex_span_of_mem_convexHull hbv_mem''
                  letI : Fintype ι'' := hFin''
                  let e'' : Fin (Fintype.card ι'') ≃ ι'' := (Fintype.equivFin ι'').symm
                  refine ⟨Fintype.card ι'', z'' ∘ e'', w''' ∘ e'', ?_, ?_, ?_, ?_⟩
                  · intro i; exact hz''_range (Set.mem_range.mpr ⟨e'' i, rfl⟩)
                  · intro i; exact hw'''_pos (e'' i)
                  · exact (Equiv.sum_comp e'' w''').trans hw'''_sum
                  · exact (Equiv.sum_comp e'' (fun j => w''' j • z'' j)).trans hbv_eq'
                -- Now: minCaraDepth(S(emb l'')) (bv(emb l'')) ≤ Nl'' - 1
                -- The new point D'.point(emb l'') = (sv-ε*c'_l'')•av + (1-sv+ε*c'_l'')•bv
                -- Get the explicit repr of bv of size minCaraDepth(bv) ≤ Nl'' - 1
                obtain ⟨f_bv, w_bv, hf_bv, hw_bv, hw_bv_sum, hbv_repr⟩ :=
                  Nat.sInf_mem hbv_nonempty
                -- minCaraDepth of D'.point(emb l'') using:
                -- The point new_point(emb l'') ∈ convexHull(S(emb l''))
                -- Bound via: 1 + minCaraDepth(bv) vertices suffice
                have hD'_point_bound : minCaraDepth (S (emb l'')) (D'.point (emb l'')) ≤ Nl'' := by
                  -- D'.point(emb l'') has the following convex combination representation:
                  -- Case: a-weight α = sv(emb l'') - ε*c'(l'')
                  --       b-weight β = 1 - sv(emb l'') + ε*c'(l'')
                  -- Both ≥ 0, α + β = 1.
                  -- If we already know D'.point ∈ convexHull(S(emb l'')):
                  --   Use eq_pos_convex_span and bound card ≤ finrank+1 ≤ Nl''?
                  --   This is circular.
                  -- More direct: give an explicit ≤ Nl''-vertex representation.
                  -- minCaraDepth(bv(emb l'')) ≤ Nl'' - 1 (by hbv_depth'')
                  -- The set {m | ∃ repr of bv of size m} has sInf = minCaraDepth bv ≤ Nl'' - 1.
                  -- Get the min repr of bv:
                  have hbv_min_nonempty : {m : ℕ | ∃ (f : Fin m → E) (w : Fin m → ℝ),
                      (∀ i, f i ∈ S (emb l'')) ∧ (∀ i, 0 < w i) ∧
                      ∑ i, w i = 1 ∧ ∑ i, w i • f i = bv (emb l'')}.Nonempty :=
                    hbv_nonempty
                  set K := minCaraDepth (S (emb l'')) (bv (emb l'')) with hK_def
                  have hK_le : K ≤ Nl'' - 1 := hbv_depth''
                  -- Get the minimum representation of bv with Fin type cast to Fin K
                  obtain ⟨f_bvK, w_bvK, hf_bvK, hw_bvK, hw_bvK_sum, hbv_reprK⟩ :
                      ∃ (f : Fin K → E) (w : Fin K → ℝ),
                        (∀ i, f i ∈ S (emb l'')) ∧ (∀ i, 0 < w i) ∧
                        ∑ i, w i = 1 ∧ ∑ i, w i • f i = bv (emb l'') := by
                    have h := Nat.sInf_mem hbv_min_nonempty
                    rwa [show sInf {m : ℕ | ∃ (f : Fin m → E) (w : Fin m → ℝ),
                        (∀ i, f i ∈ S (emb l'')) ∧ (∀ i, 0 < w i) ∧
                        ∑ i, w i = 1 ∧ ∑ i, w i • f i = bv (emb l'')} = K
                      from hK_def.symm] at h
                  -- D'.point(emb l'') = α•av + β•bv ∈ convexHull
                  -- where α = sv(emb l'') - ε*c'(l''), β = 1-sv(emb l'')+ε*c'(l'')
                  -- Explicitly construct a (1 + K)-vertex representation IF α > 0
                  -- or a K-vertex representation if α = 0.
                  -- In either case, 1 + K ≤ 1 + (Nl'' - 1) = Nl''.
                  -- (When K = 0, bv is represented by 0 vertices... impossible since
                  --  bv ∈ convexHull(S) means weight sum = 1 > 0, so we need ≥ 1 vertex.)
                  -- Actually K could be 0 if bv ∈ S (depth 1 via Carathéodory).
                  -- Wait: our minCaraDepth requires strictly positive weights.
                  -- If bv ∈ S: the 1-vertex repr (bv itself, weight 1) works, so K ≤ 1.
                  -- But we're in Case B2: bv(emb l') ∉ S(emb l'), not l''.
                  -- So bv(emb l'') might or might not be in S(emb l'').
                  -- Either way, 1 + K ≤ 1 + Nl'' - 1 = Nl'' (when K ≤ Nl'' - 1).
                  -- We build an explicit representation:
                  -- Obtain (sv(emb l'') - ε*c'(l'')) > 0 or = 0.
                  -- The new_point_emb l'' gives us the perturbed point.
                  have hrw_l'' : D'.point (emb l'') =
                      (sv (emb l'') - ε * c' l'') • av (emb l'') +
                      (1 - sv (emb l'') + ε * c' l'') • bv (emb l'') := by
                    have : D'.point (emb l'') = new_point (emb l'') := rfl
                    rw [this, new_point_emb l'', hpoint_eq'']
                    simp only [δ, smul_sub, smul_smul, add_smul, sub_smul]; abel
                  -- The a-weight α = sv(emb l'') - ε*c'(l'') ≥ 0 [from new_mem_convexHull proof]
                  -- The b-weight β = 1-sv(emb l'')+ε*c'(l'') ≥ 0
                  -- α + β = 1.
                  -- Explicit repr: av + (w_bvK i)-scaled vertices of bv
                  -- = (α•av + β•bv) uses 1 + K ≤ Nl'' vertices.
                  --
                  -- Case 1: K = 0. But K = minCaraDepth bv ≥ 0. If K = 0, the set
                  --   {m | ∃ repr of bv} has sInf = 0, meaning the empty repr works... but
                  --   the empty sum = 0 ≠ bv unless bv = 0. This is problematic.
                  --   If K = 0: min of set is 0, meaning the set contains 0.
                  --   But a 0-vertex repr requires ∑_{i : Fin 0} w i = 1, which is 0 = 1, false.
                  --   So actually K ≥ 1 always when bv ∈ convexHull(S) (it has at least 1 vertex).
                  --   Wait: if convexHull(S) is empty, bv can't be in it. So bv has ≥ 1 vertex.
                  --   And if bv ∈ S, the 1-vertex repr gives K ≤ 1.
                  --   If bv ∉ S, K ≥ 2.
                  --   Either way, K ≥ 1.
                  --
                  -- Provided K ≥ 1 and α ≥ 0, β ≥ 0:
                  -- We need to build a (1+K)-vertex repr if α > 0, or K-vertex if α = 0.
                  -- Both give ≤ 1 + K ≤ 1 + (Nl'' - 1) = Nl'' vertices.
                  --
                  -- To avoid casing on α, we simply bound:
                  --   minCaraDepth(D'.point(emb l'')) ≤ 1 + K ≤ Nl''
                  -- via an explicit (1 + K)-vertex repr [concatenating av with bv's vertices].
                  -- The weights must be strictly positive — this fails if α = 0.
                  --
                  -- Alternative: use minCaraDepth_le_of_repr with K vertices (just bv's repr)
                  -- when α = 0 (point = bv), and 1+K when α > 0.
                  rcases le_or_lt (sv (emb l'') - ε * c' l'') 0 with hα | hα
                  · -- α ≤ 0; since α ≥ 0 (from new_mem_convexHull), α = 0, point = bv
                    have hα_zero : sv (emb l'') - ε * c' l'' = 0 := by
                      have : 0 ≤ sv (emb l'') - ε * c' l'' := by
                        rcases lt_trichotomy (c' l'') 0 with hneg | hzero | hpos
                        · nlinarith [le_of_lt (hrepr (emb l'') (hemb_mem l'')).2.2.1,
                            le_of_lt hε_pos, neg_pos.mpr hneg]
                        · rw [hzero, mul_zero, sub_zero]
                          exact le_of_lt (hrepr (emb l'') (hemb_mem l'')).2.2.1
                        · have hle := hε_le_pos l'' (Finset.mem_filter.mpr
                              ⟨Finset.mem_univ _, hpos⟩)
                          have : ε * c' l'' ≤ sv (emb l'') := by
                            calc ε * c' l'' ≤ (sv (emb l'') / c' l'') * c' l'' :=
                                  mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
                              _ = sv (emb l'') := div_mul_cancel₀ _ (ne_of_gt hpos)
                          linarith
                      linarith
                    have hβ_one : 1 - sv (emb l'') + ε * c' l'' = 1 := by linarith
                    -- D'.point(emb l'') = bv(emb l'')
                    have : D'.point (emb l'') = bv (emb l'') := by
                      rw [hrw_l'', hα_zero, hβ_one, zero_smul, one_smul, zero_add]
                    rw [this]
                    calc minCaraDepth (S (emb l'')) (bv (emb l'')) ≤ Nl'' - 1 := hbv_depth''
                      _ ≤ Nl'' := Nat.sub_le _ _
                  · -- α > 0; build 1+K vertex repr
                    -- β = 1 - α ∈ [0,1); point = α•av + β•bv
                    -- β = 1 - sv(emb l'') + ε*c'(l'') ≥ 0 (from new_mem_convexHull)
                    have hβ_nn : 0 ≤ 1 - sv (emb l'') + ε * c' l'' := by
                      rcases lt_trichotomy (c' l'') 0 with hneg | hzero | hpos
                      · have hle := hε_le_neg l'' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneg⟩)
                        have hcneg_pos : (0 : ℝ) < -c' l'' := neg_pos.mpr hneg
                        have hmul : ε * (-c' l'') ≤ 1 - sv (emb l'') := by
                          calc ε * (-c' l'') ≤ ((1 - sv (emb l'')) / (-c' l'')) * (-c' l'') :=
                                mul_le_mul_of_nonneg_right hle (le_of_lt hcneg_pos)
                            _ = 1 - sv (emb l'') := div_mul_cancel₀ _ (ne_of_gt hcneg_pos)
                        nlinarith
                      · rw [hzero, mul_zero, add_zero]
                        linarith [(hrepr (emb l'') (hemb_mem l'')).2.2.2.1]
                      · nlinarith [le_of_lt hε_pos, le_of_lt hpos,
                            (hrepr (emb l'') (hemb_mem l'')).2.2.2.1]
                    -- Build a (1 + K)-vertex representation of D'.point(emb l'')
                    -- using av as vertex 0 (weight α) and f_bvK as vertices 1..K (weights β*w_bvK)
                    -- But we need strictly positive weights, so β must be > 0.
                    -- Actually the weights are: α for av, β*w_bvK i for the K bv-vertices.
                    -- α > 0 ✓; β*w_bvK i > 0 iff β > 0.
                    -- We need β > 0, but β = 1-α where α < 1 (since sv < 1 and ε*c'>0 increases α?)
                    -- Wait: α = sv - ε*c'(l''). If c'(l'') > 0, α < sv < 1, so β = 1-α > 0.
                    -- If c'(l'') < 0, α = sv + ε*(-c') > sv > 0, and α ≤ sv + ε₀*(-c'_min) ≤ 1?
                    --   We bounded b-weight ≥ 0 in new_mem_convexHull, so β ≥ 0.
                    --   β = 0 means α = 1, which is a boundary case.
                    -- In the subcase α > 0, β could still be 0 (i.e., α = 1, point = av ∈ S).
                    -- If β = 0: point = av ∈ S, depth ≤ 1 ≤ Nl'' (since Nl'' ≥ 2) ✓.
                    -- If β > 0 and α > 0: build 1+K vertex repr.
                    rcases le_or_lt (1 - sv (emb l'') + ε * c' l'') 0 with hβ | hβ
                    · have hβ_zero : 1 - sv (emb l'') + ε * c' l'' = 0 := le_antisymm hβ hβ_nn
                      have hα_one : sv (emb l'') - ε * c' l'' = 1 := by linarith
                      have : D'.point (emb l'') = av (emb l'') := by
                        rw [hrw_l'', hβ_zero, hα_one, one_smul, zero_smul, add_zero]
                      rw [this]
                      -- av(emb l'') ∈ S(emb l''), so it has a 1-vertex repr
                      have : minCaraDepth (S (emb l'')) (av (emb l'')) ≤ 1 := by
                        apply minCaraDepth_le_of_repr
                          (fun _ : Fin 1 => av (emb l''))
                          (fun _ : Fin 1 => 1)
                        · intro _; exact (hrepr (emb l'') (hemb_mem l'')).1
                        · intro _; exact one_pos
                        · simp
                        · simp
                      linarith [hNl''_ge2]
                    · -- α > 0, β > 0: build explicit (1 + K)-vertex repr
                      -- But wait: 1 + K might be 0 if K = 0? K = minCaraDepth bv.
                      -- K ≥ 1 because bv ∈ convexHull(S(emb l'')) requires ≥ 1 vertex
                      -- (the sum ∑ w i = 1 > 0 means at least one term).
                      -- Actually K = sInf, and we showed that K ≤ Nl'' - 1.
                      -- The Nat.sInf_mem gives a K-vertex repr with ∑ w i = 1.
                      -- If K = 0: Fin 0 repr has ∑ w i = 0 ≠ 1, contradiction.
                      -- So K ≥ 1.
                      have hK_pos : 0 < K := by
                        by_contra h; push_neg at h
                        have hK_zero : K = 0 := Nat.le_zero.mp h
                        -- K = 0 means w_bvK : Fin 0 → ℝ, so ∑ i : Fin 0, w_bvK i = 0 ≠ 1
                        have : ∑ i : Fin K, w_bvK i = 0 :=
                          Finset.sum_eq_zero (fun i _ =>
                            False.elim (Nat.not_lt_zero i.val (hK_zero ▸ i.isLt)))
                        linarith [hw_bvK_sum]
                      -- Build 1+K vertex repr:
                      -- Vertices: av (weight α / (α + β * 1) = α, since α + β = 1)
                      --           f_bvK i for i : Fin K (weight β * w_bvK i)
                      -- Total weight: α + β * ∑ w_bvK i = α + β * 1 = 1 ✓
                      -- D'.point(emb l'') = α•av + β•bv = α•av + β•(∑ w_bvK i • f_bvK i)
                      --                   = α•av + ∑ (β*w_bvK i)•f_bvK i
                      -- Use Fin.castSucc for av at position 0, f_bvK i at succ positions.
                      have h_le_1K : minCaraDepth (S (emb l'')) (D'.point (emb l'')) ≤ K + 1 := by
                        apply minCaraDepth_le_of_repr
                          (Fin.cons (av (emb l'')) (fun i => f_bvK i))
                          (Fin.cons (sv (emb l'') - ε * c' l'')
                            (fun i => (1 - sv (emb l'') + ε * c' l'') * w_bvK i))
                        · intro i
                          refine Fin.cases ?_ ?_ i
                          · simp [Fin.cons_zero]; exact (hrepr (emb l'') (hemb_mem l'')).1
                          · intro j; simp [Fin.cons_succ]; exact hf_bvK j
                        · intro i
                          refine Fin.cases ?_ ?_ i
                          · simp [Fin.cons_zero]; linarith
                          · intro j; simp [Fin.cons_succ]
                            exact mul_pos hβ (hw_bvK j)
                        · simp [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
                          rw [← Finset.mul_sum, hw_bvK_sum, mul_one]
                          ring
                        · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_smul,
                                     ← Finset.smul_sum, hbv_reprK]
                          rw [hrw_l'']
                      omega
                exact hD'_point_bound
              · -- j ∉ range(emb): D'.point j = D₁.point j
                rw [show D'.point j = D₁.point j from
                    new_point_not_emb j (fun l => hj_emb ∘ (⟨l, ·⟩))]
          _ ≤ minCaraDepth (S (emb l')) (D₁.point (emb l')) - 1 +
              ∑ j ∈ D₁.excessIndices.erase (emb l'), minCaraDepth (S j) (D₁.point j) := by
              apply Nat.add_le_add_left
              apply Finset.sum_le_sum_of_subset
              apply Finset.erase_subset_erase
              apply hD'_subset
          _ = ∑ j ∈ D₁.excessIndices, minCaraDepth (S j) (D₁.point j) - 1 := by
              rw [← Finset.add_sum_erase _ _ (hD'_subset hemb_l'_D'_excess)]
              have h_ge2 := hdepth_emb_l'_ge2
              omega
          _ ≤ n - 1 := by
              have := hdn₁
              omega
          _ < n := by omega
      -- Apply IH or direct conclusion for Case B2
      -- Two sub-cases: D' already has fewer excess indices, or same count (apply IH).
      by_cases h_D'_done : D'.excessIndices.card < D₁.excessIndices.card
      · -- Direct: D' itself witnesses the decrease
        exact ⟨D', h_D'_done⟩
      · -- D'.excessIndices.card = D₁.excessIndices.card (since D'.excess ⊆ D₁.excess)
        -- Apply IH to D': it has strictly smaller total minCaraDepth
        have h_D'_ge : Module.finrank ℝ E < D'.excessIndices.card := by
          have hle := Finset.card_le_card hD'_subset
          omega
        obtain ⟨D'', hD''lt⟩ := ih _ hD'_depth_lt D' le_rfl h_D'_ge
        exact ⟨D'', by
          have := Finset.card_le_card hD'_subset
          omega⟩

/-
Part 5: Main Theorem Proof (from reduction step)
-/

/-- **Shapley-Folkman Lemma** (proved from the reduction step).

    By induction on the excess count: start with any decomposition
    (from the hypothesis), then repeatedly apply reduce_excess_by_one until
    the excess count drops to ≤ d = finrank(ℝ, E). -/
theorem shapley_folkman [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (hx : ∃ (f : ι → E), (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      (∀ i, i ∉ t → f i = 0) ∧ ∑ i ∈ t, f i = x) :
    ∃ (d : Decomposition S t x),
      d.excessIndices.card ≤ Module.finrank ℝ E := by
  -- Construct initial decomposition from the hypothesis
  obtain ⟨f, hf_mem, hf_zero, hf_sum⟩ := hx
  let D₀ : Decomposition S t x := ⟨f, hf_mem, hf_zero, hf_sum⟩
  -- Induction on the excess count: for any bound n, any decomposition with
  -- excessIndices.card ≤ n can be reduced to one with ≤ d excess indices.
  suffices ∀ n : ℕ, ∀ D : Decomposition S t x, D.excessIndices.card ≤ n →
      ∃ D' : Decomposition S t x, D'.excessIndices.card ≤ Module.finrank ℝ E by
    exact this D₀.excessIndices.card D₀ le_rfl
  intro n
  induction n with
  | zero =>
    -- Base case: 0 excess indices ≤ d (trivially)
    intro D hD
    exact ⟨D, by omega⟩
  | succ n ih =>
    intro D hD
    -- If already ≤ d, done
    by_cases hle : D.excessIndices.card ≤ Module.finrank ℝ E
    · exact ⟨D, hle⟩
    -- Otherwise excess > d, so reduce by one and apply IH
    · push_neg at hle
      obtain ⟨D', hD'lt⟩ := reduce_excess_by_one hne D hle
      exact ih D' (by omega)

/-
Part 6: Corollaries

Direct consequences of the Shapley-Folkman lemma that are useful
in applications to mathematical economics and optimization.
-/

/-- **Shapley-Folkman-Starr Corollary (qualitative form)**:
    The Minkowski sum of many sets is "nearly convex" — its convex hull
    differs from the sum itself in a bounded way controlled by dimension,
    not by the number of summands.

    Requires: convexHull(∑ Sᵢ) ⊆ ∑ convexHull(Sᵢ) (Minkowski sum identity). -/
theorem sum_close_to_convexHull [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    ∃ (f : ι → E),
      (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      ∑ i ∈ t, f i = x ∧
      (t.filter (fun i => f i ∉ S i)).card ≤ Module.finrank ℝ E := by
  -- Step 1: convexHull(∑ Sᵢ) ⊆ ∑ convexHull(Sᵢ)
  -- Proof: ∑ Sᵢ ⊆ ∑ conv(Sᵢ) (monotonicity) and ∑ conv(Sᵢ) is convex,
  -- so convexHull(∑ Sᵢ) ⊆ ∑ conv(Sᵢ) by convexHull_min.
  have h_sub : ∑ i ∈ t, S i ⊆ ∑ i ∈ t, convexHull ℝ (S i) :=
    Set.finset_sum_subset_finset_sum t S (fun i => convexHull ℝ (S i))
      (fun i _ => subset_convexHull ℝ (S i))
  have h_conv : Convex ℝ (∑ i ∈ t, convexHull ℝ (S i)) :=
    convex_sum (fun i => convexHull ℝ (S i)) (fun i _ => convex_convexHull ℝ (S i))
  have hx' : x ∈ ∑ i ∈ t, convexHull ℝ (S i) :=
    convexHull_min h_sub h_conv hx
  -- Step 2: Extract pointwise decomposition from membership in the sum
  rw [Set.mem_finset_sum] at hx'
  obtain ⟨g, hg_mem, hg_sum⟩ := hx'
  -- Step 3: Modify g to be zero outside t (doesn't affect sum over t)
  let g' : ι → E := fun i => if i ∈ t then g i else 0
  have hg'_mem : ∀ i ∈ t, g' i ∈ convexHull ℝ (S i) := by
    intro i hi; simp only [g', if_pos hi]; exact hg_mem hi
  have hg'_zero : ∀ i, i ∉ t → g' i = 0 := by
    intro i hi; simp only [g', if_neg hi]
  have hg'_sum : ∑ i ∈ t, g' i = x := by
    have : ∑ i ∈ t, g' i = ∑ i ∈ t, g i :=
      Finset.sum_congr rfl (fun i hi => by simp [g', if_pos hi])
    rw [this]; exact hg_sum
  -- Step 4: Apply Shapley-Folkman
  obtain ⟨D, hD⟩ := shapley_folkman hne ⟨g', hg'_mem, hg'_zero, hg'_sum⟩
  exact ⟨D.point, D.mem_convexHull, D.sum_eq, hD⟩

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
  -- n • S = ∑ i ∈ Finset.univ, (fun _ => S) i for ι = Fin n
  -- Apply sum_close_to_convexHull with constant family
  have hS_eq : n • S = ∑ i ∈ (Finset.univ : Finset (Fin n)), (fun _ : Fin n => S) i := by
    rw [Finset.sum_const]; simp [Fintype.card_fin]
  rw [hS_eq] at hx
  obtain ⟨f, hf_mem, hf_sum, hf_excess⟩ :=
    sum_close_to_convexHull (fun i _ => hne) hx
  exact ⟨f, fun i => hf_mem i (Finset.mem_univ i), hf_sum, hf_excess⟩

end ShapleyFolkman
