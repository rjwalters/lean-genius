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

Status: formalized — 1 sorry remains:
  (1) convexHull_not_mem_requires_two: PROVED via eq_pos_convex_span_of_mem_convexHull + card analysis
  (2) binary_repr_of_mem_convexHull_not_mem: PROVED via Fin.sum_univ_succ + centerMass_mem_convexHull
  (3) Sub-case B2 of reduce_excess_by_one: bv ∉ S; needs WF descent on Carathéodory depth [OPEN]
  new_sum indicator sum rearrangement: proved (Finset.sum_image + Finset.sum_subset)
-/
import Mathlib

set_option linter.unusedVariables false

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
  haveI : Fintype ι := hFin
  -- Show the index type has ≥ 2 elements
  have hn : 2 ≤ Fintype.card ι := by
    by_contra h_lt
    push_neg at h_lt
    -- card = 0 or 1
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · -- card = 0: sum over empty type = 0 ≠ 1
      haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
      linarith [Fintype.sum_empty w, hw_sum]
    · -- card = 1: unique element → x ∈ s, contradiction
      have h1 : Fintype.card ι = 1 := Nat.le_antisymm (by omega) hpos
      obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp h1
      -- Since ∀ i, i = i₀, the sums reduce to single terms
      have hw_single : ∑ i : ι, w i = w i₀ :=
        Finset.sum_eq_single i₀ (fun b _ hb => (absurd (hi₀ b) hb).elim)
          (fun h => (absurd (Finset.mem_univ i₀) h).elim)
      have hz_single : ∑ i : ι, w i • z i = w i₀ • z i₀ :=
        Finset.sum_eq_single i₀ (fun b _ hb => (absurd (hi₀ b) hb).elim)
          (fun h => (absurd (Finset.mem_univ i₀) h).elim)
      have hwi₀ : w i₀ = 1 := hw_single ▸ hw_sum
      have hxi₀ : x = z i₀ := by
        have := hx_eq; rw [hz_single, hwi₀, one_smul] at this; exact this.symm
      exact hx_not (hxi₀ ▸ hz_range (Set.mem_range.mpr ⟨i₀, rfl⟩))
  -- Convert from the abstract index type ι to Fin n via Fintype.equivFin
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, z ∘ e, w ∘ e, hn, ?_, ?_, ?_, ?_⟩
  · intro i; exact hz_range (Set.mem_range.mpr ⟨e i, rfl⟩)
  · intro i; exact hw_pos (e i)
  · -- ∑ i : Fin n, (w ∘ e) i = ∑ i : ι, w i = 1
    have heq := Fintype.sum_equiv e (w ∘ e) w (fun i => rfl)
    rw [heq]; exact hw_sum
  · -- ∑ i : Fin n, (w ∘ e) i • (z ∘ e) i = ∑ i : ι, w i • z i = x
    have heq := Fintype.sum_equiv e (fun i => (w ∘ e) i • (z ∘ e) i)
      (fun i => w i • z i) (fun i => rfl)
    rw [heq]; exact hx_eq

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

/-- **Reduction step**: If a decomposition has more than d excess indices
    (where d = Module.finrank ℝ E), there exists another decomposition of
    the same point with strictly fewer excess indices.

    Proof strategy:
    1. For each excess j: write point j = s_j • a_j + (1-s_j) • b_j,
       a_j ∈ S j, b_j ∈ conv(S j), s_j ∈ (0,1)  [binary_repr_of_mem_convexHull_not_mem]
    2. Pick d+1 excess indices emb : Fin(d+1) → ι; direction vectors δ_l = b_l - a_l
    3. Linear dependence (d+1 vecs in d-dim): Σ c_l • δ_l = 0, normalize so ∃ l, c_l < 0
    4. ε = min { (1-s_l)/(-c_l) : c_l < 0 } ∩ { s_l/c_l : c_l > 0 } > 0
    5. Perturb: point'(emb l) = (s_l - ε·c_l)·a_l + (1-s_l+ε·c_l)·b_l
       - Still in conv(S l) since weights ≥ 0 sum to 1
       - Sum preserved: Σ perturbation = ε · Σ c_l · δ_l = 0
       - At minimizing lmin (c_lmin < 0): b-weight = 0, point' = a_lmin ∈ S(emb lmin)
       - excessIndices strictly decreases -/
theorem reduce_excess_by_one [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (D : Decomposition S t x)
    (hexcess : Module.finrank ℝ E < D.excessIndices.card) :
    ∃ D' : Decomposition S t x, D'.excessIndices.card < D.excessIndices.card := by
  classical
  set d := Module.finrank ℝ E with hd_def
  -- Step 1: Binary representation data for excess indices
  -- For each j ∈ excessIndices: av j ∈ S j, bv j ∈ conv(S j), sv j ∈ (0,1),
  --   D.point j = sv j • av j + (1 - sv j) • bv j
  obtain ⟨av, bv, sv, hrepr⟩ :
      ∃ (av bv : ι → E) (sv : ι → ℝ), ∀ j ∈ D.excessIndices,
        av j ∈ S j ∧ bv j ∈ convexHull ℝ (S j) ∧ 0 < sv j ∧ sv j < 1 ∧
        D.point j = sv j • av j + (1 - sv j) • bv j := by
    have hchoose : ∀ j ∈ D.excessIndices, ∃ (a b : E) (s : ℝ),
        a ∈ S j ∧ b ∈ convexHull ℝ (S j) ∧ 0 < s ∧ s < 1 ∧
        D.point j = s • a + (1 - s) • b := fun j hj => by
      simp only [Decomposition.excessIndices, Finset.mem_filter] at hj
      exact binary_repr_of_mem_convexHull_not_mem (D.mem_convexHull j hj.1) hj.2
    -- Use Classical.choice to get the functions
    refine ⟨fun j => if h : j ∈ D.excessIndices then
                      (hchoose j h).choose else 0,
            fun j => if h : j ∈ D.excessIndices then
                      (hchoose j h).choose_spec.choose else 0,
            fun j => if h : j ∈ D.excessIndices then
                      (hchoose j h).choose_spec.choose_spec.choose else 0,
            fun j hj => ?_⟩
    simp only [dif_pos hj]
    exact (hchoose j hj).choose_spec.choose_spec.choose_spec
  -- Step 2: Pick d+1 excess indices as emb : Fin(d+1) → ι
  -- Strategy: convert D.excessIndices to a list and index into it.
  -- D.excessIndices has card ≥ d+1, so the list has enough elements.
  obtain ⟨emb, hemb_inj, hemb_mem⟩ : ∃ (emb : Fin (d + 1) → ι),
      Function.Injective emb ∧ ∀ l, emb l ∈ D.excessIndices := by
    have hcard : d + 1 ≤ D.excessIndices.card := by omega
    let L : List ι := D.excessIndices.val.toList
    have hL_len : L.length = D.excessIndices.card := by
      simp only [L, Multiset.length_toList, Finset.card_def]
    refine ⟨fun l => L.get ⟨l.val, by omega⟩, ?_, fun l => ?_⟩
    · -- Injectivity: List.get on a nodup list is injective
      intro l₁ l₂ heq
      have hL_nodup : L.Nodup := Finset.nodup_toList D.excessIndices
      have hinj : Function.Injective L.get := List.nodup_iff_injective_get.mp hL_nodup
      -- hinj heq : ⟨l₁.val, _⟩ = ⟨l₂.val, _⟩ : Fin L.length
      -- Extract ℕ equality via explicit congrArg with n = L.length
      have h := hinj heq  -- h : ⟨↑l₁, _⟩ = ⟨↑l₂, _⟩ : Fin L.length
      have hval : l₁.val = l₂.val := by
        have key := @congrArg (Fin L.length) ℕ ⟨l₁.val, by omega⟩ ⟨l₂.val, by omega⟩ Fin.val h
        simpa using key
      exact Fin.ext hval
    · -- Membership
      have h_lt : l.val < L.length := by omega
      exact Finset.mem_def.mpr
        (Multiset.mem_toList.mp (List.get_mem L ⟨l.val, h_lt⟩))
  -- Helper: emb l ∈ t (D.excessIndices ⊆ t, and mem_of_mem_filter can't unfold through the def)
  have hemb_in_t : ∀ l : Fin (d + 1), emb l ∈ t := fun l => by
    have h := hemb_mem l
    simp only [Decomposition.excessIndices, Finset.mem_filter] at h
    exact h.1
  -- Step 3: Direction vectors δ_l = bv(emb l) - av(emb l) for l : Fin(d+1)
  let δ : Fin (d + 1) → E := fun l =>
    bv (emb l) - av (emb l)
  -- Step 4: Linear dependence: c : Fin(d+1) → ℝ, ∃ l₀ with c l₀ ≠ 0, Σ c_l • δ_l = 0
  obtain ⟨c, ⟨l₀, hl₀ne⟩, hcδ⟩ := linearDependent_coefficients (by omega : d < d + 1) δ
  -- Step 5: Normalize so some coefficient is negative (negate c if needed)
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
  --
  -- Strategy: perturb using only NEGATIVE coefficients.
  -- ε₀ = min { (1 - sv(emb l)) / (-c' l) : c' l < 0 }
  -- This is well-defined since c' lneg < 0 exists and all sv(emb l) < 1.
  --
  -- The perturbation shifts each excess index emb l by ε₀ · c' l · δ l:
  --   new_point(emb l) = (sv_l + ε₀ · (-c' l)) · av_l + ((1 - sv_l) - ε₀ · (-c' l)) · bv_l
  -- For c' l < 0: b-weight decreases, a-weight increases.
  -- For c' l > 0: a-weight decreases, b-weight increases.
  --   (a-weight stays ≥ 0 because ε₀ is bounded by (1-sv_l)/(-c'_l) for negative indices only,
  --    but positive indices may lose a-weight — so we add a pos bound too)
  --
  -- To preserve non-negativity for ALL indices, use the joint minimum:
  --   ε = min(ε_neg ∪ ε_pos)
  -- where ε_neg = { (1 - sv_l) / (-c'_l) : c'_l < 0 }
  --       ε_pos = { sv_l / c'_l : c'_l > 0 }
  --
  -- At the minimizer l_min:
  --   Case A (c' l_min < 0): b-weight hits 0 → new_point = av(emb l_min) ∈ S(emb l_min)
  --     → emb l_min exits excessIndices → excess count strictly decreases ✓
  --   Case B (c' l_min > 0): a-weight hits 0 → new_point = bv(emb l_min) ∈ convexHull(S)
  --     → emb l_min stays in excessIndices (bv may not be in S)
  --     → bv(emb l_min) has strictly fewer Carathéodory vertices (one eliminated)
  --     → WF induction on total Carathéodory vertex count terminates in Case A.
  --
  -- We implement Case A directly and leave Case B for the WF helper.
  --
  -- Step 6a: Define candidate ratios for the perturbation bound.
  -- For negative coefficients: ratio_neg l = (1 - sv(emb l)) / (-c' l), for c' l < 0.
  -- We build a nonempty Finset of ratios to take the minimum from.
  --
  -- Since c' lneg < 0, the set of negative-coefficient indices is nonempty.
  have neg_nonempty : ∃ l : Fin (d + 1), c' l < 0 := ⟨lneg, hlneg⟩
  -- Collect all negative-coefficient indices into a Finset.
  let neg_indices : Finset (Fin (d + 1)) :=
    Finset.univ.filter (fun l => c' l < 0)
  have neg_indices_ne : neg_indices.Nonempty := by
    simp only [neg_indices, Finset.filter_nonempty_iff]
    exact ⟨lneg, Finset.mem_univ _, hlneg⟩
  -- Step 6b: Collect all positive-coefficient indices.
  let pos_indices : Finset (Fin (d + 1)) :=
    Finset.univ.filter (fun l => 0 < c' l)
  -- Step 6c: Define ratio function (the time until weight hits boundary).
  -- ratio_neg l = (1 - sv(emb l)) / (-c' l)  for l ∈ neg_indices  [b-weight → 0]
  -- ratio_pos l = sv(emb l) / c' l             for l ∈ pos_indices  [a-weight → 0]
  -- All ratios are strictly positive:
  have ratio_neg_pos : ∀ l ∈ neg_indices, 0 < (1 - sv (emb l)) / (-c' l) := by
    intro l hl
    simp only [neg_indices, Finset.mem_filter] at hl
    apply div_pos
    · have := (hrepr (emb l) (hemb_mem l)).2.2.2.1  -- sv(emb l) < 1
      linarith
    · linarith [hl.2]
  have ratio_pos_pos : ∀ l ∈ pos_indices, 0 < sv (emb l) / c' l := by
    intro l hl
    simp only [pos_indices, Finset.mem_filter] at hl
    apply div_pos
    · exact (hrepr (emb l) (hemb_mem l)).2.2.1  -- 0 < sv(emb l)
    · exact hl.2
  -- Step 6d: Define ε as the JOINT minimum over all candidate ratios.
  -- Build a combined Finset of all ratios from both neg and pos indices.
  -- ε = min of { ratio_neg l : l ∈ neg_indices } ∪ { ratio_pos l : l ∈ pos_indices }
  --
  -- Architecture note: Using JOINT minimum ensures new_mem_convexHull is proved in Case A only
  -- (no Case B needed). The minimizer might be a neg-index (c' < 0) or pos-index (c' > 0).
  -- When minimizer is neg (b-weight → 0): new_point = av ∈ S → emb l_min exits excess ✓
  -- When minimizer is pos (a-weight → 0): new_point = bv ∈ convexHull(S) → l_min stays excess,
  --   but its Carathéodory complexity decreases. Full proof requires WF on Carathéodory count.
  let neg_ratios : Finset ℝ := neg_indices.image (fun l => (1 - sv (emb l)) / (-c' l))
  have neg_ratios_ne : neg_ratios.Nonempty := Finset.image_nonempty.mpr neg_indices_ne
  let ε₀ : ℝ := neg_ratios.min' neg_ratios_ne
  -- ε₀ is achieved at some l_min ∈ neg_indices:
  have hε₀_mem : ε₀ ∈ neg_ratios := Finset.min'_mem _ _
  obtain ⟨l_min, hl_min_neg, hl_min_eq⟩ := Finset.mem_image.mp hε₀_mem
  -- ε₀ > 0:
  have hε₀_pos : 0 < ε₀ := by
    rw [← hl_min_eq]; exact ratio_neg_pos l_min hl_min_neg
  -- ε₀ ≤ ratio_neg l for all l ∈ neg_indices:
  have hε₀_le_neg : ∀ l ∈ neg_indices, ε₀ ≤ (1 - sv (emb l)) / (-c' l) :=
    fun l hl => Finset.min'_le _ _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
  -- Joint ε: also take minimum over pos_indices if nonempty.
  -- This ensures ∀ l ∈ pos_indices, ε ≤ sv(emb l)/c'(l), so a-weights ≥ 0.
  let ε : ℝ := if h : pos_indices.Nonempty then
    min ε₀ ((pos_indices.image (fun l => sv (emb l) / c' l)).min' (Finset.image_nonempty.mpr h))
    else ε₀
  -- ε > 0 (min of positive quantities):
  have hε_pos : 0 < ε := by
    simp only [ε]
    split_ifs with h
    · apply lt_min hε₀_pos
      -- Show 0 < min' of pos_ratios: min' is one of the elements, which is > 0
      have hpos_ne : (pos_indices.image (fun l => sv (emb l) / c' l)).Nonempty :=
        Finset.image_nonempty.mpr h
      have hmin_mem := Finset.min'_mem _ hpos_ne
      obtain ⟨l, hl, hl_eq⟩ := Finset.mem_image.mp hmin_mem
      rw [← hl_eq]; exact ratio_pos_pos l hl
    · exact hε₀_pos
  -- ε ≤ ε₀ (joint min ≤ neg-only min):
  have hε_le_ε₀ : ε ≤ ε₀ := by
    simp only [ε]; split_ifs with h
    · exact min_le_left _ _
    · exact le_refl _
  -- ε ≤ ratio_neg l for all l ∈ neg_indices:
  have hε_le_neg : ∀ l ∈ neg_indices, ε ≤ (1 - sv (emb l)) / (-c' l) :=
    fun l hl => le_trans hε_le_ε₀ (hε₀_le_neg l hl)
  -- ε ≤ ratio_pos l for all l ∈ pos_indices:
  have hε_le_pos : ∀ l ∈ pos_indices, ε ≤ sv (emb l) / c' l := by
    simp only [ε]
    split_ifs with h
    · intro l hl
      apply le_trans (min_le_right _ _)
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    · intro l hl
      exact absurd ⟨l, hl⟩ h
  -- Step 6e: The joint ε satisfies ALL coefficient bounds (no Case B needed!).
  -- The check that ε₀ respects pos bounds is now replaced by the joint minimum construction.
  -- If pos_indices is nonempty, we must additionally take the minimum over pos_indices.
  -- We define ε as the true joint minimum.
  --
  -- To avoid the case split on whether pos_indices is empty, we use the following:
  -- If pos_indices is empty: ε = ε₀ (all coefficients ≤ 0, only lneg is < 0).
  -- If pos_indices is nonempty: ε = min(ε₀, min over pos ratios).
  --
  -- The minimizer l_min has c' l_min < 0 (from neg_indices), so:
  -- Case A always applies at l_min after the joint minimum.
  -- HOWEVER: if the joint minimum is achieved at a pos_index l', then Case B applies at l',
  -- and the minimizer may shift. We accept this and use a sorry for Case B.
  --
  -- Step 6f: Construct the perturbed point function using joint ε.
  -- For i ∈ image(emb): new_point(emb l) = point(emb l) + ε · c'_l · δ_l
  -- For i ∉ image(emb): new_point i = D.point i
  --
  -- Since emb is injective (indices from D.excessIndices, a Finset), at most one l satisfies
  -- emb l = i. We use ε (joint minimum) so that all convex combination weights are non-negative.
  --
  -- Step 6g: Define the new decomposition.
  -- new_point (emb l) = D.point (emb l) + ε • (c' l • δ l)
  -- new_point i = D.point i   for i ∉ range(emb)
  -- The single remaining sorry is in hnew_point_av: we need ε = ε₀ when neg-index achieves
  -- the joint minimum. The full proof requires WF descent on Carathéodory vertex count.
  let new_point : ι → E := fun i =>
    if h : ∃ l : Fin (d + 1), emb l = i then
      let l := h.choose
      D.point i + ε • (c' l • δ l)
    else
      D.point i
  -- Step 6h: Verify new_point is well-defined (choice of l is canonical via injectivity):
  have new_point_emb : ∀ l : Fin (d + 1),
      new_point (emb l) = D.point (emb l) + ε • (c' l • δ l) := by
    intro l
    simp only [new_point, dif_pos (show ∃ l' : Fin (d + 1), emb l' = emb l from ⟨l, rfl⟩)]
    congr 1
    congr 1
    have : (⟨l, rfl⟩ : ∃ l' : Fin (d + 1), emb l' = emb l).choose = l := by
      apply hemb_inj
      exact (⟨l, rfl⟩ : ∃ l' : Fin (d + 1), emb l' = emb l).choose_spec
    simp [this]
  have new_point_not_emb : ∀ i : ι, (∀ l : Fin (d + 1), emb l ≠ i) →
      new_point i = D.point i := by
    intro i hi
    simp only [new_point, dif_neg (not_exists.mpr hi)]
  -- Step 6i: Verify the sum is preserved.
  -- Σ_{i ∈ t} new_point i = Σ_{i ∈ t} D.point i + ε · Σ_l c' l · δ l
  -- = x + ε · 0 = x.
  have new_sum : ∑ i ∈ t, new_point i = x := by
    -- Split the sum over t by whether i is in range(emb) or not.
    -- The perturbation terms telescope via Σ c'_l · δ_l = 0.
    conv_lhs =>
      arg 2; ext i
      rw [show new_point i = D.point i +
            if h : ∃ l : Fin (d + 1), emb l = i then ε • (c' h.choose • δ h.choose) else 0
          from by
            split_ifs with h
            · simp only [new_point, dif_pos h]
            · simp only [new_point, dif_neg h, add_zero]]
    rw [Finset.sum_add_distrib, D.sum_eq]
    suffices h : ∑ i ∈ t, (if h : ∃ l : Fin (d + 1), emb l = i then
        ε • (c' h.choose • δ h.choose) else 0) = 0 by
      simp [h]
    -- Rewrite the sum: only excess indices contribute (others have D.point zero outside t,
    -- but emb maps into D.excessIndices ⊆ t).
    -- ∑_{i ∈ t} [if ∃ l, emb l = i then ε · c' l · δ l else 0]
    -- = ∑_l ε · c' l · δ l  (since emb is injective and image(emb) ⊆ t)
    have hemb_in_t : ∀ l : Fin (d + 1), emb l ∈ t := fun l =>
      hemb_in_t l
    rw [show ∑ i ∈ t, (if h : ∃ l : Fin (d + 1), emb l = i then
          ε • (c' h.choose • δ h.choose) else 0) =
        ∑ l : Fin (d + 1), ε • (c' l • δ l) from by
      -- Sum rearrangement: indicator sum over t = sum over Fin(d+1) via injective emb.
      -- Step 1: reduce sum over t to sum over image(emb) (terms vanish outside image(emb))
      have step1 : ∑ i ∈ t, (if h : ∃ l : Fin (d + 1), emb l = i then
            ε • (c' h.choose • δ h.choose) else 0) =
          ∑ i ∈ Finset.image emb Finset.univ, (if h : ∃ l : Fin (d + 1), emb l = i then
            ε • (c' h.choose • δ h.choose) else 0) := by
        symm
        apply Finset.sum_subset (Finset.image_subset_iff.mpr (fun l _ => hemb_in_t l))
        intro i _ hi
        have hne : ¬∃ l : Fin (d + 1), emb l = i :=
          fun ⟨l, hl⟩ => hi (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, hl⟩)
        simp only [dif_neg hne]
      -- Step 2: rewrite sum over image via injectivity of emb
      have step2 : ∑ i ∈ Finset.image emb Finset.univ, (if h : ∃ l : Fin (d + 1), emb l = i then
            ε • (c' h.choose • δ h.choose) else 0) =
          ∑ l : Fin (d + 1), ε • (c' l • δ l) := by
        rw [Finset.sum_image (fun a _ b _ h => hemb_inj h)]
        apply Finset.sum_congr rfl
        intro l _
        split_ifs with h
        · have heq : h.choose = l := hemb_inj h.choose_spec
          rw [heq]
        · exact absurd ⟨l, rfl⟩ h
      exact step1.trans step2]
    rw [← Finset.smul_sum, hc'δ, smul_zero]
  -- Step 6j: Verify each new_point lies in convexHull(S i).
  -- For i ∈ range(emb): new_point(emb l) = (sv_l + ε₀·c'_l)·av_l + ((1-sv_l) - ε₀·c'_l)·bv_l
  --   = (sv_l - ε₀·c'_l)·av_l + (1-sv_l + ε₀·c'_l)·bv_l
  --   Wait: c'_l < 0 at lneg, so ε₀·c'_lneg < 0.
  --   new a-weight at lneg: sv(lneg) - ε₀·c'(lneg) = sv(lneg) + ε₀·(-c'(lneg)) > sv(lneg) > 0 ✓
  --   new b-weight at lneg: (1 - sv(lneg)) + ε₀·c'(lneg) = (1-sv(lneg)) - ε₀·(-c'(lneg))
  --                        = (1-sv(lneg)) - ε₀·(-c'(lneg)) ≥ 0  (by definition of ε₀) ✓
  --   At l_min: b-weight = 0 exactly.
  --
  -- With joint ε: all coefficient bounds satisfied for both neg and pos indices.
  -- new_mem_convexHull requires no case split — hε_le_neg and hε_le_pos handle all cases.
  -- Claim: new_point i ∈ convexHull ℝ (S i) for all i ∈ t.
  have new_mem_convexHull : ∀ i ∈ t, new_point i ∈ convexHull ℝ (S i) := by
    -- Joint ε satisfies all coefficient bounds (both neg and pos indices).
    -- No case split needed: hε_le_neg and hε_le_pos cover all cases.
    intro i hi
    by_cases h : ∃ l : Fin (d + 1), emb l = i
    · obtain ⟨l, rfl⟩ := h
      rw [new_point_emb l]
      obtain ⟨hav_mem, hbv_mem, hsv_pos, hsv_lt1, hpoint_eq⟩ :=
        hrepr (emb l) (hemb_mem l)
      -- Rewrite as convex combination: (sv - ε·c')•av + (1-sv+ε·c')•bv
      have hrw : D.point (emb l) + ε • (c' l • δ l) =
          (sv (emb l) - ε * c' l) • av (emb l) +
          (1 - sv (emb l) + ε * c' l) • bv (emb l) := by
        rw [hpoint_eq]; simp only [δ, smul_sub, smul_smul, add_smul, sub_smul]; abel
      rw [hrw]
      have hsum : (sv (emb l) - ε * c' l) + (1 - sv (emb l) + ε * c' l) = 1 := by ring
      rcases lt_trichotomy (c' l) 0 with hneg | hzero | hpos
      · -- c'_l < 0: neg-index; hε_le_neg gives b-coeff ≥ 0; a-coeff ≥ 0 since ε > 0, -c' > 0
        have ha_pos : 0 ≤ sv (emb l) - ε * c' l :=
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
      · -- c'_l = 0: expression equals D.point (emb l)
        have heq : (sv (emb l) - ε * c' l) • av (emb l) +
            (1 - sv (emb l) + ε * c' l) • bv (emb l) = D.point (emb l) := by
          rw [hzero, mul_zero, sub_zero, add_zero, hpoint_eq]
        rw [heq]; exact D.mem_convexHull (emb l) (hemb_in_t l)
      · -- c'_l > 0: pos-index; hε_le_pos gives a-coeff ≥ 0; b-coeff ≥ 0 since 1-sv > 0
        have ha_pos : 0 ≤ sv (emb l) - ε * c' l := by
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
      exact D.mem_convexHull i hi
  -- Step 6k: new_point is zero outside t.
  have new_zero : ∀ i, i ∉ t → new_point i = 0 := by
    intro i hi
    have hDz := D.point_eq_zero i hi
    have h_no_emb : ∀ l : Fin (d + 1), emb l ≠ i := by
      intro l heq
      -- emb l ∈ D.excessIndices, and excessIndices ⊆ t
      have hmem_t : emb l ∈ t := hemb_in_t l
      exact hi (heq ▸ hmem_t)
    rw [new_point_not_emb i h_no_emb, hDz]
  -- Step 6l: Construct the new decomposition.
  let D' : Decomposition S t x :=
    ⟨new_point, new_mem_convexHull, new_zero, new_sum⟩
  -- Step 6m: Show D'.excessIndices.card < D.excessIndices.card.
  -- At l_min ∈ neg_indices: ε₀ = (1 - sv(emb l_min)) / (-c' l_min).
  -- new b-weight at emb l_min = (1 - sv(emb l_min)) + ε₀ · c'(l_min) = 0.
  -- So new_point(emb l_min) = sv'·av(emb l_min) + 0·bv(emb l_min) = sv'·av(emb l_min).
  -- But we need sv' > 0 and av(emb l_min) ∈ S(emb l_min), so new_point = sv'·av ∈ S iff sv'=1.
  -- Hmm, sv' = sv(emb l_min) - ε₀ · c'(l_min) = sv(emb l_min) + ε₀·(-c'(l_min)).
  -- Wait, new_point = D.point + ε₀ · (c'·δ) = sv·av + (1-sv)·bv + ε₀·c'·(bv-av)
  --                = (sv - ε₀·c')·av + (1-sv + ε₀·c')·bv
  -- At l_min: c' l_min < 0, so (1 - sv_min + ε₀·c'_min) = (1-sv_min) - ε₀·(-c'_min) = 0
  --   (by choice of ε₀ = (1-sv_min)/(-c'_min)).
  -- So new_point(emb l_min) = (sv_min + ε₀·(-c'_min))·av(emb l_min)
  --                          = av_scale · av(emb l_min)
  -- where av_scale = sv_min + ε₀·(-c'_min) > sv_min > 0.
  -- But av_scale ≤ 1 (need to verify).
  -- For the point to be in S (not just convexHull S), we need the representation to be a
  -- single point: av_scale = 1, i.e., sv_min + ε₀·(-c'_min) = 1, i.e., ε₀ = (1-sv_min)/(-c'_min).
  -- This is EXACTLY the definition of ε₀ at l_min! So av_scale = 1 ✓.
  -- Therefore: new_point(emb l_min) = av(emb l_min) ∈ S(emb l_min) ✓
  have hl_min_data := hrepr (emb l_min) (hemb_mem l_min)
  obtain ⟨hav_mem, _, hsv_pos, hsv_lt1, hpoint_eq⟩ := hl_min_data
  have hcl_min_neg : c' l_min < 0 := by
    simp only [neg_indices, Finset.mem_filter] at hl_min_neg; exact hl_min_neg.2
  -- D'.excessIndices ⊆ D.excessIndices: all perturbed excess indices were already excess.
  -- Proof: emb maps into D.excessIndices; non-emb indices have unchanged points.
  have hD'_subset : D'.excessIndices ⊆ D.excessIndices := by
    intro i hi
    simp only [Decomposition.excessIndices, Finset.mem_filter, D'] at hi ⊢
    obtain ⟨hi_t, hi_new⟩ := hi
    refine ⟨hi_t, ?_⟩
    by_cases h : ∃ l : Fin (d + 1), emb l = i
    · obtain ⟨l, rfl⟩ := h
      simp only [Decomposition.excessIndices, Finset.mem_filter] at hemb_mem
      exact (hemb_mem l).2
    · rw [new_point_not_emb i (not_exists.mp h)] at hi_new
      exact hi_new
  -- Case split: does the neg-index minimizer l_min achieve the JOINT minimum?
  --
  -- Case A (ε = ε₀): neg-index l_min achieves the joint min.
  --   b-weight at l_min hits 0 exactly → new_point(emb l_min) = av(emb l_min) ∈ S → exits excess.
  --
  -- Case B (ε < ε₀): some pos-index l' achieves the joint min (ε = sv(emb l') / c'(l')).
  --   a-weight at l' hits 0 → new_point(emb l') = bv(emb l') ∈ convexHull(S(emb l')).
  --   If bv(emb l') ∈ S(emb l'): l' exits excess directly (e.g., when Carathéodory count = 2).
  --   Otherwise: WF descent on total Carathéodory vertex count (Starr 1969) terminates in Case A.
  --   Full proof requires a DecoratedDecomp structure tracking vertex counts per excess index.
  by_cases hcase_A : ε = ε₀
  · -- Case A: ε = ε₀ (neg-index l_min achieves joint minimum).
    -- new_point(emb l_min) = av(emb l_min) ∈ S(emb l_min):
    have hnew_point_av : new_point (emb l_min) = av (emb l_min) := by
      rw [new_point_emb l_min, hcase_A]
      -- Expand: sv·av + (1-sv)·bv + ε₀·c'·(bv-av)
      --        = (sv - ε₀·c')·av + (1-sv+ε₀·c')·bv = 1·av + 0·bv = av
      rw [hpoint_eq]; simp only [δ]
      have hcneg : -c' l_min > 0 := neg_pos.mpr hcl_min_neg
      have hb_weight_zero : (1 - sv (emb l_min)) + ε₀ * c' l_min = 0 := by
        have h1 : ε₀ * (-c' l_min) = 1 - sv (emb l_min) := by
          rw [← hl_min_eq]
          exact div_mul_cancel₀ _ (ne_of_gt hcneg)
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
      simp only [Decomposition.excessIndices, Finset.mem_filter, D']
      intro ⟨_, hnot⟩
      exact hnot (hnew_point_av ▸ hav_mem)
    have hD_excess : emb l_min ∈ D.excessIndices := hemb_mem l_min
    have hD'_ssub : D'.excessIndices ⊂ D.excessIndices :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hD'_subset,
        fun heq => hD'_not_excess (heq ▸ hD_excess)⟩
    exact ⟨D', Finset.card_lt_card hD'_ssub⟩
  · -- Case B: ε < ε₀ (pos-index achieves joint minimum).
    -- pos_indices must be nonempty (else ε = ε₀, contradiction with Case B)
    have h_pos_ne : pos_indices.Nonempty := by
      by_contra h
      exact hcase_A (by simp only [ε, dif_neg h])
    have h_pr_ne : (pos_indices.image (fun l => sv (emb l) / c' l)).Nonempty :=
      Finset.image_nonempty.mpr h_pos_ne
    -- ε = min ε₀ (min of pos_ratios) from the definition of ε
    have hε_eq : ε = min ε₀ ((pos_indices.image (fun l => sv (emb l) / c' l)).min' h_pr_ne) := by
      simp only [ε, dif_pos h_pos_ne]
    -- The pos minimum is ≤ ε₀ (since ε ≠ ε₀ means the neg branch didn't win)
    have h_pm_le : (pos_indices.image (fun l => sv (emb l) / c' l)).min' h_pr_ne ≤ ε₀ := by
      by_contra h
      push_neg at h
      exact hcase_A (hε_eq ▸ min_eq_left (le_of_lt h))
    -- ε equals the pos minimum
    have hε_pm : ε = (pos_indices.image (fun l => sv (emb l) / c' l)).min' h_pr_ne :=
      hε_eq ▸ min_eq_right h_pm_le
    -- Extract l' ∈ pos_indices achieving the minimum ratio
    obtain ⟨l', hl'_in, hl'_eq⟩ :
        ∃ l' ∈ pos_indices, sv (emb l') / c' l' =
          (pos_indices.image (fun l => sv (emb l) / c' l)).min' h_pr_ne :=
      Finset.mem_image.mp (Finset.min'_mem _ _)
    simp only [pos_indices, Finset.mem_filter] at hl'_in
    have hl'_pos : 0 < c' l' := hl'_in.2
    -- sv(emb l') / c'(l') = ε (the joint minimum)
    have hl'_ratio : sv (emb l') / c' l' = ε := hl'_eq ▸ hε_pm.symm
    -- a-weight at l' hits 0: sv(emb l') - ε * c'(l') = 0
    have h_aw : sv (emb l') - ε * c' l' = 0 := by
      have heq : sv (emb l') = ε * c' l' := by
        rw [← hl'_ratio]; field_simp [ne_of_gt hl'_pos]
      linarith
    -- Get binary representation data for emb l'
    obtain ⟨_, hbv_mem', _, _, hpoint_eq'⟩ :=
      hrepr (emb l') (Finset.mem_of_mem_filter _ (hemb_mem l'))
    -- new_point(emb l') = bv(emb l'): a-weight = 0, b-weight = 1
    have hnew_bv : new_point (emb l') = bv (emb l') := by
      rw [new_point_emb l', hpoint_eq']; simp only [δ]
      have h_bw : (1 - sv (emb l')) + ε * c' l' = 1 := by linarith [h_aw]
      have key : sv (emb l') • av (emb l') + (1 - sv (emb l')) • bv (emb l') +
                 ε • (c' l' • (bv (emb l') - av (emb l'))) = bv (emb l') := by
        have : sv (emb l') • av (emb l') + (1 - sv (emb l')) • bv (emb l') +
               ε • (c' l' • (bv (emb l') - av (emb l'))) =
               (sv (emb l') - ε * c' l') • av (emb l') +
               ((1 - sv (emb l')) + ε * c' l') • bv (emb l') := by
          simp only [smul_sub, smul_smul, add_smul, sub_smul]; ring
        rw [this, h_aw, h_bw, zero_smul, one_smul, zero_add]
      exact key
    -- Sub-case B1: bv ∈ S(emb l') → l' exits excess → done
    by_cases hbv_S : bv (emb l') ∈ S (emb l')
    · have hl'_not_excess : emb l' ∉ D'.excessIndices := by
        simp only [Decomposition.excessIndices, Finset.mem_filter, D']
        intro ⟨_, hnot⟩
        exact hnot (hnew_bv ▸ hbv_S)
      exact ⟨D', Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hD'_subset,
        fun heq => hl'_not_excess (heq ▸ hemb_mem l')⟩)⟩
    · -- Sub-case B2: bv(emb l') ∉ S(emb l').
      -- new_point(emb l') = bv(emb l') ∈ convexHull(S(emb l')) \ S(emb l').
      --
      -- Mathematical argument (WF induction on Carathéodory depth):
      -- Define caraDepth(x, s) = min n such that x has an n-vertex Carathéodory representation.
      -- Define totalDepth(D) = Σ_{j ∈ D.excessIndices} caraDepth(D.point j, S j).
      --
      -- In B2: D'.point(emb l') = bv(emb l'), which has caraDepth = caraDepth(D.point(emb l')) - 1
      --   (bv is the renormalized remainder after removing av from the representation).
      -- All other D.point j are unchanged, so totalDepth(D') = totalDepth(D) - 1.
      --
      -- By strong induction on totalDepth ≥ 0:
      --   At totalDepth = 0: all excess points are in S (depth 0 → point ∈ S) → excessIndices = ∅,
      --     contradicting hexcess > d ≥ 0. So base case vacuously holds.
      --   Inductive step: apply one perturbation. Cases A and B1 directly decrease excess count.
      --   Case B2: totalDepth(D') = totalDepth(D) - 1 < totalDepth(D), apply IH to get D''.
      --
      -- Formal prerequisite: binary_repr_of_mem_convexHull_not_mem must return the full
      --   Carathéodory representation (count + vertices + weights), not just the binary split.
      --   Specifically, we need: if x ∈ convexHull(s) has n-vertex repr, then the constructed
      --   bv ∈ convexHull(s) has an (n-1)-vertex repr.
      -- Estimated additional work: ~80 lines (depth-tracking + induction structure).
      sorry

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
