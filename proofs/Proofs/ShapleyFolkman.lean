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

Status: formalized (3 sorries in reduce_excess_by_one Step 6: Carathéodory descent.
  (a) hconv'': perturbed point is convex combination of fF₀ l k ∈ S(emb l)
  (b) hlmin_S: at minimizer lmin with nF=2, remaining vertex ∈ S(emb lmin)
  (c) IH case: when nF≥3, construct updated Carathéodory data with nF' lmin = nF lmin - 1
  NOT submittable to Aristotle: requires structural proof, not tactic search.)
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
  · -- Weights are strictly positive
    intro i; exact hw_pos (e.symm i)
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
      (∀ i, i ∉ t → f i = 0) ∧ ∑ i in t, f i = x) :
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
  obtain ⟨n, f, w, hn2, hfS, hwpos, hwsum, hweq⟩ :=
    convexHull_not_mem_requires_two hx hxs
  -- Write n = m + 1 to use Fin.sum_univ_succ
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- t = w 0, a = f 0 ∈ s
  have ht_pos : 0 < w ⟨0, Nat.zero_lt_succ m⟩ := hwpos ⟨0, Nat.zero_lt_succ m⟩
  have hm_pos : 0 < m := by omega
  -- ∑_{Fin(m+1)} w i = w 0 + ∑_{Fin m} w(succ i)  [Fin.sum_univ_succ]
  have hsum_split : w ⟨0, Nat.zero_lt_succ m⟩ + ∑ i : Fin m, w (Fin.succ i) = 1 := by
    have := @Fin.sum_univ_succ ℝ _ m w; linarith [hwsum]
  have hrem_sum : ∑ i : Fin m, w (Fin.succ i) = 1 - w ⟨0, Nat.zero_lt_succ m⟩ := by linarith
  have hrem_pos : 0 < 1 - w ⟨0, Nat.zero_lt_succ m⟩ := by
    have : 0 < ∑ i : Fin m, w (Fin.succ i) :=
      Finset.sum_pos (fun i _ => hwpos (Fin.succ i)) ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩
    linarith
  have ht_lt1 : w ⟨0, Nat.zero_lt_succ m⟩ < 1 := by linarith
  -- b = centerMass of remaining vertices with normalized weights
  -- = (1 - w 0)⁻¹ • Σ_{i : Fin m} w(succ i) • f(succ i)
  let w' : Fin m → ℝ := fun i => w (Fin.succ i) / (1 - w ⟨0, Nat.zero_lt_succ m⟩)
  let b₀ : E := ∑ i : Fin m, w' i • f (Fin.succ i)
  have hw'_sum : ∑ i : Fin m, w' i = 1 := by
    simp only [w', Finset.sum_div, hrem_sum, div_self (ne_of_gt hrem_pos)]
  -- b₀ ∈ convexHull s via centerMass with weights w' summing to 1
  have hb₀_conv : b₀ ∈ convexHull ℝ s := by
    -- b₀ = centerMass w' f(succ ·), since ∑ w' i = 1 so (∑ w' i)⁻¹ = 1
    have hb_cm : b₀ = Finset.univ.centerMass w' (fun i => f (Fin.succ i)) := by
      show ∑ i : Fin m, w' i • f (Fin.succ i) =
           (∑ i : Fin m, w' i)⁻¹ • ∑ i : Fin m, w' i • f (Fin.succ i)
      rw [hw'_sum, inv_one, one_smul]
    rw [hb_cm]
    exact Finset.centerMass_mem_convexHull _
      (fun i _ => div_nonneg (le_of_lt (hwpos (Fin.succ i))) (le_of_lt hrem_pos))
      hw'_sum (fun i _ => hfS (Fin.succ i))
  -- x = w 0 • f 0 + (1 - w 0) • b₀
  have hx_eq : x = w ⟨0, Nat.zero_lt_succ m⟩ • f ⟨0, Nat.zero_lt_succ m⟩ +
               (1 - w ⟨0, Nat.zero_lt_succ m⟩) • b₀ := by
    rw [← hweq, Fin.sum_univ_succ]
    congr 1
    -- Goal: ∑ w(succ i) • f(succ i) = (1 - w 0) • b₀
    -- = (1-w0) • ∑ (w(succ i)/(1-w0)) • f(succ i) = ∑ w(succ i) • f(succ i)  ✓
    simp only [b₀, smul_sum, smul_smul, w']
    apply Finset.sum_congr rfl; intro i _
    congr 1
    -- Goal: w(succ i) = (1-w0) * (w(succ i) / (1-w0))
    field_simp [ne_of_gt hrem_pos]
  exact ⟨f ⟨0, Nat.zero_lt_succ m⟩, b₀, w ⟨0, Nat.zero_lt_succ m⟩,
         hfS ⟨0, Nat.zero_lt_succ m⟩, hb₀_conv, ht_pos, ht_lt1, hx_eq⟩

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
  obtain ⟨emb, hemb_mem, hemb_inj⟩ : ∃ (emb : Fin (d + 1) → ι),
      (∀ l, emb l ∈ D.excessIndices) ∧ Function.Injective emb := by
    have hcard : d + 1 ≤ D.excessIndices.card := by omega
    let L : List ι := D.excessIndices.val.toList
    have hL_len : L.length = D.excessIndices.card := by
      simp only [L, Multiset.toList_length, Finset.card_def]
    have hL_nodup : L.Nodup := Multiset.nodup_toList.mpr D.excessIndices.nodup
    refine ⟨fun l => L.get ⟨l.val, by omega⟩, ?_, ?_⟩
    · intro l
      have h_lt : l.val < L.length := by omega
      exact Finset.mem_def.mpr
        (Multiset.mem_toList.mp (List.get_mem L l.val h_lt))
    · intro a b hab
      have h := hL_nodup.get_inj_iff.mp hab
      exact Fin.ext (congr_arg Fin.val h)
  -- Step 3: Direction vectors δ_l = bv(emb l) - av(emb l) for l : Fin(d+1)
  let δ : Fin (d + 1) → E := fun l =>
    bv (emb l) - av (emb l)
  -- Step 4: Linear dependence: c : Fin(d+1) → ℝ, ∃ l₀ with c l₀ ≠ 0, Σ c_l • δ_l = 0
  obtain ⟨c, ⟨l₀, hl₀ne⟩, hcδ⟩ := linearDependent_coefficients (by omega : d < d + 1) δ
  -- Step 5: Normalize so some coefficient is negative (negate c if needed)
  obtain ⟨c', lneg, hlneg, hc'δ⟩ : ∃ (c' : Fin (d + 1) → ℝ) (lneg : Fin (d + 1)),
      c' lneg < 0 ∧ ∑ l, c' l • δ l = 0 := by
    rcases lt_trichotomy (c l₀) 0 with h | rfl | h
    · exact ⟨c, l₀, h, hcδ⟩
    · exact absurd rfl hl₀ne
    · refine ⟨fun l => -(c l), l₀, by linarith, ?_⟩
      have : ∑ l : Fin (d + 1), -(c l) • δ l = -(∑ l : Fin (d + 1), c l • δ l) := by
        simp [neg_smul, Finset.sum_neg_distrib]
      rw [this, hcδ, neg_zero]
  -- Step 6: Perturbation construction
  --
  -- ARCHITECTURAL NOTE (researcher-3, 2026-04-13):
  -- The binary representation (a ∈ S, b ∈ convexHull(S)) has a gap:
  -- the ε-minimizer might have c' > 0, giving point' = b ∈ convexHull(S) \ S,
  -- which doesn't reduce excess. Example: c'₁=-1, sv₁=0.1, c'₂=2, sv₂=0.5
  -- gives bounds A=0.9 (c'<0) vs B=0.25 (c'>0); B < A, minimizer at c'>0.
  -- Negating c' gives A'=0.25, B'=0.1 — still minimizer at c'>0.
  --
  -- CORRECT APPROACH (Starr 1969): Use full Carathéodory representations
  -- (both vertices in S) and well-founded descent on total vertex count.
  -- Each perturbation step removes one vertex. When a vertex count drops
  -- from 2 to 1, the point equals that vertex ∈ S, reducing excess.
  -- The descent terminates in finitely many steps (vertex count is a ℕ).
  --
  -- PROOF SKETCH:
  -- 1. For each excess j, get Carathéodory rep: n_j ≥ 2 points from S(j)
  --    with strictly positive weights (from eq_pos_convex_span_of_mem_convexHull)
  -- 2. Pick d+1 excess indices. For each, choose two vertices z₀, z₁ ∈ S(j).
  --    Direction: δ = z₁ - z₀ (both in S, so well-defined).
  -- 3. Linear dependence: Σ c_l · δ_l = 0 (as in Step 4 above).
  -- 4. Perturbation: shift weight between z₀ and z₁ at each excess index.
  --    ε = min_{l: c_l > 0} w₁/c_l ∪ min_{l: c_l < 0} w₀/(-c_l)
  --    At minimizer: one vertex removed, total vertex count decreases by 1.
  -- 5. New decomposition has D'.excess ≤ D.excess (excess can't increase
  --    since only excess indices are affected and they stay in convexHull(S)).
  -- 6. Iterate via well-founded descent on total vertex count.
  --    Terminates when some index drops from 2→1 vertex, making point ∈ S.
  --
  -- Implementation requires:
  -- (a) A "decorated decomposition" carrying Carathéodory data per index
  -- (b) WellFounded recursion on total vertex count
  -- (c) The perturbation construction within full representations
  -- Estimated: ~100-120 lines of Lean
  -- Implementation: see Step 3 (Carathéodory descent) below
  -- Step 3 (Carathéodory Descent): Full vertex-count descent.
  -- For each of the d+1 selected excess indices, get ALL Carathéodory vertices
  -- in S(emb l). Perturb by shifting weight between vertex 0 and vertex 1.
  -- At the minimizer lmin, one vertex weight goes to 0. If nF lmin = 2, the
  -- remaining vertex ∈ S → non-excess (direct win). If nF lmin ≥ 3, T decreases
  -- by 1, apply strong induction. By Nat.strongRecOn, terminates with excess decrease.
  --
  -- Step 3a: Extract Carathéodory data for d+1 selected excess indices.
  have hcara_data : ∀ l : Fin (d + 1),
      ∃ (n : ℕ) (f : Fin n → E) (w : Fin n → ℝ),
        2 ≤ n ∧ (∀ k, f k ∈ S (emb l)) ∧ (∀ k, 0 < w k) ∧
        ∑ k, w k = 1 ∧ ∑ k, w k • f k = D.point (emb l) := fun l => by
    have hmem := hemb_mem l
    simp only [Decomposition.excessIndices, Finset.mem_filter] at hmem
    exact convexHull_not_mem_requires_two (D.mem_convexHull _ hmem.1) hmem.2
  choose nF fF wF hn2 hfFS hwFpos hwFsum hwFpt using hcara_data
  -- Step 3b: Strong induction on T₀ = Σ l, nF l.
  suffices ∀ (T₀ : ℕ) (nF₀ : Fin (d + 1) → ℕ)
      (fF₀ : ∀ l, Fin (nF₀ l) → E) (wF₀ : ∀ l, Fin (nF₀ l) → ℝ)
      (D₀ : Decomposition S t x),
      ∑ l : Fin (d + 1), nF₀ l = T₀ →
      (∀ l, emb l ∈ D₀.excessIndices) →
      (∀ l, 2 ≤ nF₀ l) →
      (∀ l k, fF₀ l k ∈ S (emb l)) →
      (∀ l k, 0 < wF₀ l k) →
      (∀ l, ∑ k, wF₀ l k = 1) →
      (∀ l, ∑ k, wF₀ l k • fF₀ l k = D₀.point (emb l)) →
      ∃ D' : Decomposition S t x, D'.excessIndices.card < D₀.excessIndices.card from
    this (∑ l, nF l) nF fF wF D rfl hemb_mem hn2 hfFS hwFpos hwFsum hwFpt
  intro T₀
  induction T₀ using Nat.strongRecOn with
  | ind T₀ IH =>
    intro nF₀ fF₀ wF₀ D₀ hT₀ hemb₀ hn₂₀ hfFS₀ hwFpos₀ hwFsum₀ hwFpt₀
    let i₀ : ∀ l : Fin (d + 1), Fin (nF₀ l) := fun l => ⟨0, by have := hn₂₀ l; omega⟩
    let i₁ : ∀ l : Fin (d + 1), Fin (nF₀ l) := fun l => ⟨1, by have := hn₂₀ l; omega⟩
    -- Direction vectors: δ₀ l = fF₀ l 1 - fF₀ l 0 (both in S(emb l))
    let δ₀ : Fin (d + 1) → E := fun l => fF₀ l (i₁ l) - fF₀ l (i₀ l)
    -- Linear dependence among d+1 direction vectors in d-dim
    obtain ⟨c₀, ⟨l₀', hl₀'ne⟩, hc₀δ⟩ := linearDependent_coefficients (by omega : d < d + 1) δ₀
    -- Normalize c₀ so some coefficient is negative
    obtain ⟨c₀', lneg₀, hlneg₀, hc₀'δ⟩ :
        ∃ (c₀' : Fin (d + 1) → ℝ) (lneg₀ : Fin (d + 1)),
        c₀' lneg₀ < 0 ∧ ∑ l, c₀' l • δ₀ l = 0 := by
      rcases lt_trichotomy (c₀ l₀') 0 with h | rfl | h
      · exact ⟨c₀, l₀', h, hc₀δ⟩
      · exact absurd rfl hl₀'ne
      · exact ⟨fun l => -(c₀ l), l₀', by linarith,
               by simp [neg_smul, ← Finset.sum_neg_distrib, hc₀δ]⟩
    -- Active set: l where c₀' l ≠ 0
    let activeL := (Finset.univ : Finset (Fin (d + 1))).filter (fun l => c₀' l ≠ 0)
    have hactNe : activeL.Nonempty :=
      ⟨lneg₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_lt hlneg₀⟩⟩
    -- Ratios: bounds on ε before a weight goes to 0
    let ratioOf : Fin (d + 1) → ℝ := fun l =>
      if c₀' l < 0 then wF₀ l (i₁ l) / (-c₀' l)
      else wF₀ l (i₀ l) / c₀' l
    have hratPos : ∀ l ∈ activeL, 0 < ratioOf l := by
      intro l hl
      have hne : c₀' l ≠ 0 := (Finset.mem_filter.mp hl).2
      simp only [ratioOf]
      rcases lt_or_gt_of_ne hne with h | h
      · simp only [h, ↓reduceIte]
        exact div_pos (hwFpos₀ l (i₁ l)) (neg_pos.mpr h)
      · simp only [h, not_lt.mpr (le_of_lt h), ↓reduceIte]
        exact div_pos (hwFpos₀ l (i₀ l)) h
    -- ε₀ = infimum of active ratios; lmin achieves it
    let ε₀ := activeL.inf' hactNe ratioOf
    obtain ⟨lmin, hlmin_act, hlmin_eq⟩ := Finset.exists_mem_eq_inf' hactNe ratioOf
    have hlmin_ne : c₀' lmin ≠ 0 := (Finset.mem_filter.mp hlmin_act).2
    have hε₀_pos : 0 < ε₀ := hlmin_eq ▸ hratPos lmin hlmin_act
    -- Perturbed decomposition: shift weight between vertex 0 and vertex 1
    let point'' : ι → E := fun j =>
      D₀.point j + ε₀ • ∑ l : Fin (d + 1), if emb l = j then c₀' l • δ₀ l else 0
    have hzero'' : ∀ j, j ∉ t → point'' j = 0 := by
      intro j hj
      simp only [point'', D₀.point_eq_zero j hj, zero_add]
      apply smul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro l _
      exact if_neg (ne_of_mem_of_not_mem (Finset.mem_filter.mp (hemb₀ l)).1 hj)
    have hsum'' : ∑ j in t, point'' j = x := by
      have key : ∑ j in t, ε₀ • ∑ l : Fin (d + 1),
          (if emb l = j then c₀' l • δ₀ l else 0) = 0 := by
        rw [← smul_sum]
        suffices ∑ j in t, ∑ l : Fin (d + 1), (if emb l = j then c₀' l • δ₀ l else 0) = 0 by
          simp [this]
        rw [Finset.sum_comm]
        have : ∀ l : Fin (d + 1), ∑ j in t, (if emb l = j then c₀' l • δ₀ l else 0) =
            c₀' l • δ₀ l := fun l => by
          rw [Finset.sum_ite_eq' t (emb l) (fun _ => c₀' l • δ₀ l)]
          simp [(Finset.mem_filter.mp (hemb₀ l)).1]
        simp [this, hc₀'δ]
      simp only [point'', Finset.sum_add_distrib, D₀.sum_eq, key, add_zero]
    -- Simplify point'' (emb l): using injectivity, the sum collapses to one term
    have hsum_eq : ∀ l : Fin (d + 1),
        ∑ l' : Fin (d + 1), (if emb l' = emb l then c₀' l' • δ₀ l' else 0) =
        c₀' l • δ₀ l := by
      intro l
      simp_rw [hemb_inj.eq_iff]
      simp [Finset.sum_ite_eq]
    have hconv'' : ∀ j ∈ t, point'' j ∈ convexHull ℝ (S j) := by
      intro j hj
      by_cases hex : ∃ l : Fin (d + 1), emb l = j
      · obtain ⟨l, rfl⟩ := hex
        -- point'' (emb l) is a convex combination of fF₀ l k ∈ S(emb l)
        -- with perturbed weights that are non-negative and sum to 1
        -- Perturbed weights: shift ε₀ * c₀' l between vertex i₀ and i₁
        let w' : Fin (nF₀ l) → ℝ := fun k =>
          if k = i₀ l then wF₀ l k - ε₀ * c₀' l
          else if k = i₁ l then wF₀ l k + ε₀ * c₀' l
          else wF₀ l k
        -- Perturbed weights are non-negative
        have hw'_nn : ∀ k, 0 ≤ w' k := by
          intro k
          simp only [w']
          split_ifs with h0 h1
          · -- k = i₀ l
            rcases le_or_lt (c₀' l) 0 with hle | hlt
            · linarith [hwFpos₀ l (i₀ l), mul_nonpos_of_nonneg_of_nonpos (le_of_lt hε₀_pos) hle]
            · -- c₀' l > 0: ε₀ ≤ ratioOf l = wF₀ l (i₀ l) / c₀' l
              have hl_act : l ∈ activeL :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_gt hlt⟩
              have hle : ε₀ ≤ ratioOf l := Finset.inf'_le _ hl_act
              simp only [ratioOf, not_lt.mpr (le_of_lt hlt), hlt, ↓reduceIte] at hle
              exact sub_nonneg.mpr (div_le_iff hlt |>.mp hle)
          · -- k = i₁ l
            rcases le_or_lt 0 (c₀' l) with hge | hlt
            · linarith [hwFpos₀ l (i₁ l), mul_nonneg (le_of_lt hε₀_pos) hge]
            · -- c₀' l < 0: ε₀ ≤ ratioOf l = wF₀ l (i₁ l) / (-c₀' l)
              have hl_act : l ∈ activeL :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_lt hlt⟩
              have hle : ε₀ ≤ ratioOf l := Finset.inf'_le _ hl_act
              simp only [ratioOf, hlt, ↓reduceIte] at hle
              have hpos : 0 < -c₀' l := neg_pos.mpr hlt
              linarith [div_le_iff hpos |>.mp hle, hwFpos₀ l (i₁ l),
                        mul_nonneg (le_of_lt hε₀_pos) (le_of_lt hpos)]
          · exact le_of_lt (hwFpos₀ l k)
        -- Perturbed weights sum to 1 (perturbation cancels)
        have hw'_sum : ∑ k : Fin (nF₀ l), w' k = 1 := by
          have h01 : i₀ l ≠ i₁ l := Fin.ne_of_lt (by simp [i₀, i₁, Fin.lt_iff_val_lt_val])
          conv_lhs =>
            arg 2; ext k
            rw [show w' k = wF₀ l k +
                (if k = i₁ l then ε₀ * c₀' l else 0) -
                (if k = i₀ l then ε₀ * c₀' l else 0) from by
              simp only [w']; split_ifs <;> ring]
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.sum_ite_eq', Finset.mem_univ, ite_true, hwFsum₀ l]
          ring
        -- point'' (emb l) equals the perturbed weighted sum
        -- Key: ∑ w'•f = ∑ wF•f + ε*c'•δ₀ l = D₀.point(emb l) + ε*c'•δ₀ l = point''(emb l)
        have hΔ_sum : ∑ k : Fin (nF₀ l), (w' k - wF₀ l k) • fF₀ l k =
            ε₀ * c₀' l • δ₀ l := by
          have h01 : i₀ l ≠ i₁ l := Fin.ne_of_lt (by simp [i₀, i₁]; omega)
          have hΔ : ∀ k : Fin (nF₀ l), w' k - wF₀ l k =
              if k = i₀ l then -(ε₀ * c₀' l)
              else if k = i₁ l then ε₀ * c₀' l else 0 := by
            intro k; simp only [w']; split_ifs <;> ring
          simp_rw [hΔ, ite_smul, zero_smul, neg_smul, smul_smul]
          -- After expansion: ∑ k, (if k=i₀ then -(val)•f k else if k=i₁ then val•f k else 0)
          -- = -(val • f(i₀)) + val • f(i₁) = val • (f(i₁) - f(i₀)) = val • δ₀ l
          rw [show ∑ k : Fin (nF₀ l), (if k = i₀ l then -(ε₀ * c₀' l • fF₀ l k)
                  else if k = i₁ l then ε₀ * c₀' l • fF₀ l k else 0) =
              -(ε₀ * c₀' l • fF₀ l (i₀ l)) + ε₀ * c₀' l • fF₀ l (i₁ l) from by
            -- Decompose nested ite into sum of two separate ite terms
            have decomp : ∀ k : Fin (nF₀ l),
                (if k = i₀ l then -(ε₀ * c₀' l • fF₀ l k)
                  else if k = i₁ l then ε₀ * c₀' l • fF₀ l k else 0) =
                (if k = i₀ l then -(ε₀ * c₀' l • fF₀ l (i₀ l)) else 0) +
                (if k = i₁ l then ε₀ * c₀' l • fF₀ l (i₁ l) else 0) := fun k => by
              by_cases h1 : k = i₀ l
              · subst h1; simp [h01]
              · by_cases h2 : k = i₁ l
                · subst h2; simp [h1]
                · simp [h1, h2]
            simp_rw [decomp, Finset.sum_add_distrib]
            simp [Finset.sum_ite_eq, Finset.mem_univ]]
          simp [δ₀, smul_sub, neg_smul]
          abel
        have hpt : point'' (emb l) = ∑ k : Fin (nF₀ l), w' k • fF₀ l k := by
          simp only [point'', hsum_eq l, smul_smul, ← hwFpt₀ l]
          rw [show ∑ k : Fin (nF₀ l), w' k • fF₀ l k =
              ∑ k : Fin (nF₀ l), wF₀ l k • fF₀ l k +
              ∑ k : Fin (nF₀ l), (w' k - wF₀ l k) • fF₀ l k from by
            rw [← Finset.sum_add_distrib]
            congr 1; ext k; rw [← add_smul]
            congr 1; ring]
          rw [hΔ_sum]
        -- Apply centerMass_mem_convexHull
        rw [hpt]
        have hmem := Finset.centerMass_mem_convexHull (Finset.univ)
          (w := w') (z := fF₀ l)
          (fun k _ => hw'_nn k) hw'_sum (fun k _ => hfFS₀ l k)
        rwa [Finset.centerMass_def, hw'_sum, inv_one, one_smul] at hmem
      · have : ∑ l : Fin (d + 1), (if emb l = j then c₀' l • δ₀ l else 0) = 0 :=
          Finset.sum_eq_zero (fun l _ => if_neg (fun h => hex ⟨l, h⟩))
        simp only [point'', this, smul_zero, add_zero]
        exact D₀.mem_convexHull j hj
    let D'' : Decomposition S t x := ⟨point'', hconv'', hzero'', hsum''⟩
    -- D''.excessIndices ⊆ D₀.excessIndices:
    -- perturbed indices are already in D₀.excessIndices;
    -- non-perturbed indices have unchanged points.
    have hsubset'' : D''.excessIndices ⊆ D₀.excessIndices := by
      intro j hj
      simp only [Decomposition.excessIndices, Finset.mem_filter] at hj ⊢
      refine ⟨hj.1, ?_⟩
      by_cases hex : ∃ l : Fin (d + 1), emb l = j
      · -- j = emb l: emb l ∈ D₀.excessIndices → D₀.point j ∉ S j
        obtain ⟨l, rfl⟩ := hex
        exact (Finset.mem_filter.mp (hemb₀ l)).2
      · -- j ∉ range(emb): D''.point j = D₀.point j, so D''.point j ∉ S j ↔ D₀.point j ∉ S j
        intro hjS
        apply hj.2
        simp only [D'', point'',
          Finset.sum_eq_zero (fun l _ => if_neg (fun h => hex ⟨l, h⟩)),
          smul_zero, add_zero]
        exact hjS
    -- Case: nF₀ lmin = 2 → direct excess decrease
    rcases eq_or_lt_of_le (hn₂₀ lmin) with h2 | h2
    · -- With nF₀ lmin = 2, the zero-weight vertex leaves exactly one vertex ∈ S
      -- Two-term Carathéodory sum for lmin
      have h2sum : ∑ k : Fin (nF₀ lmin), wF₀ lmin k • fF₀ lmin k =
          wF₀ lmin (i₀ lmin) • fF₀ lmin (i₀ lmin) +
          wF₀ lmin (i₁ lmin) • fF₀ lmin (i₁ lmin) := by
        conv_lhs => rw [show nF₀ lmin = 2 from h2.symm]
        exact Fin.sum_univ_two _
      have h2sum_w : wF₀ lmin (i₀ lmin) + wF₀ lmin (i₁ lmin) = 1 := by
        have hsw := hwFsum₀ lmin
        conv_lhs at hsw => rw [show nF₀ lmin = 2 from h2.symm]
        simpa [Fin.sum_univ_two] using hsw
      have hlmin_S : D''.point (emb lmin) ∈ S (emb lmin) := by
        -- D''.point (emb lmin) = point'' (emb lmin) = D₀.point(emb lmin) + ε₀*(c₀'*δ₀)
        -- At lmin, one weight goes to 0, collapsing to a single vertex ∈ S
        show point'' (emb lmin) ∈ S (emb lmin)
        rcases lt_or_gt_of_ne hlmin_ne with hlt | hgt
        · -- c₀' lmin < 0: ε₀ = wF₀ lmin(i₁) / (-c₀'), weight at i₁ → 0
          have hrat : ratioOf lmin = wF₀ lmin (i₁ lmin) / (-c₀' lmin) := by
            simp [ratioOf, hlt]
          have hε_val : ε₀ * c₀' lmin = -(wF₀ lmin (i₁ lmin)) := by
            have heq := hlmin_eq; rw [hrat] at heq
            have hpos : (-c₀' lmin) > 0 := neg_pos.mpr hlt
            field_simp [ne_of_gt hpos] at heq; linarith
          -- point'' (emb lmin) collapses to fF₀ lmin (i₀ lmin) ∈ S
          suffices h : point'' (emb lmin) = fF₀ lmin (i₀ lmin) by
            rw [h]; exact hfFS₀ lmin (i₀ lmin)
          calc point'' (emb lmin)
              = D₀.point (emb lmin) + ε₀ * c₀' lmin • δ₀ lmin := by
                  simp only [point'', hsum_eq, smul_smul]
            _ = wF₀ lmin (i₀ lmin) • fF₀ lmin (i₀ lmin) +
                wF₀ lmin (i₁ lmin) • fF₀ lmin (i₁ lmin) +
                (-(wF₀ lmin (i₁ lmin))) • (fF₀ lmin (i₁ lmin) - fF₀ lmin (i₀ lmin)) := by
                  rw [← hwFpt₀ lmin, h2sum, hε_val, δ₀, neg_smul]
            _ = wF₀ lmin (i₀ lmin) • fF₀ lmin (i₀ lmin) +
                wF₀ lmin (i₁ lmin) • fF₀ lmin (i₀ lmin) := by
                  rw [neg_smul, smul_sub]; abel
            _ = fF₀ lmin (i₀ lmin) := by rw [← add_smul, h2sum_w, one_smul]
        · -- c₀' lmin > 0: weight at i₀ → 0
          have hrat : ratioOf lmin = wF₀ lmin (i₀ lmin) / c₀' lmin := by
            simp [ratioOf, not_lt.mpr (le_of_lt hgt), hgt]
          have hε_val : ε₀ * c₀' lmin = wF₀ lmin (i₀ lmin) := by
            have heq := hlmin_eq; rw [hrat] at heq
            field_simp [ne_of_gt hgt] at heq; linarith
          suffices h : point'' (emb lmin) = fF₀ lmin (i₁ lmin) by
            rw [h]; exact hfFS₀ lmin (i₁ lmin)
          calc point'' (emb lmin)
              = D₀.point (emb lmin) + ε₀ * c₀' lmin • δ₀ lmin := by
                  simp only [point'', hsum_eq, smul_smul]
            _ = wF₀ lmin (i₀ lmin) • fF₀ lmin (i₀ lmin) +
                wF₀ lmin (i₁ lmin) • fF₀ lmin (i₁ lmin) +
                wF₀ lmin (i₀ lmin) • (fF₀ lmin (i₁ lmin) - fF₀ lmin (i₀ lmin)) := by
                  rw [← hwFpt₀ lmin, h2sum, hε_val, δ₀]
            _ = wF₀ lmin (i₁ lmin) • fF₀ lmin (i₁ lmin) +
                wF₀ lmin (i₀ lmin) • fF₀ lmin (i₁ lmin) := by
                  rw [smul_sub]; abel
            _ = fF₀ lmin (i₁ lmin) := by rw [← add_smul, add_comm, h2sum_w, one_smul]
      have hlmin_nexc : emb lmin ∉ D''.excessIndices := by
        simp only [D'', Decomposition.excessIndices, Finset.mem_filter, not_and]
        intro _; exact hlmin_S
      exact ⟨D'', Finset.card_lt_card
        (Finset.ssubset_of_subset_of_ne hsubset'' (fun heq => by
          rw [← heq] at hlmin_nexc
          exact hlmin_nexc (hemb₀ lmin)))⟩
    · -- nF₀ lmin ≥ 3: vertex count T decreases; apply IH
      -- Case split: did any emb l exit excessIndices?
      by_cases hemb'' : ∀ l : Fin (d + 1), emb l ∈ D''.excessIndices
      · -- All emb l still excess. Apply IH with reduced Carathéodory data.
        -- dropL = all tied minimizers whose perturbed weight hits 0
        let dropL := activeL.filter (fun l => ratioOf l = ε₀)
        have hlmin_drop : lmin ∈ dropL :=
          Finset.mem_filter.mpr ⟨hlmin_act, hlmin_eq.symm⟩
        -- In the hemb'' case, nF₀ l ≥ 3 for each l ∈ dropL
        -- (nF₀ l = 2 would give D''.point ∈ S, contradicting hemb'')
        have hn3_drop : ∀ l ∈ dropL, 3 ≤ nF₀ l := by
          intro l hl
          have hne_l : c₀' l ≠ 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
          have hrat_l : ratioOf l = ε₀ := (Finset.mem_filter.mp hl).2
          by_contra hlt3; push_neg at hlt3
          have heq2 : nF₀ l = 2 := le_antisymm (by omega) (hn₂₀ l)
          have h2s : ∑ k : Fin (nF₀ l), wF₀ l k • fF₀ l k =
              wF₀ l (i₀ l) • fF₀ l (i₀ l) + wF₀ l (i₁ l) • fF₀ l (i₁ l) := by
            conv_lhs => rw [show nF₀ l = 2 from heq2.symm]; exact Fin.sum_univ_two _
          have h2w : wF₀ l (i₀ l) + wF₀ l (i₁ l) = 1 := by
            have := hwFsum₀ l; conv_lhs at this => rw [show nF₀ l = 2 from heq2.symm]
            simpa [Fin.sum_univ_two] using this
          have hlS : point'' (emb l) ∈ S (emb l) := by
            rcases lt_or_gt_of_ne hne_l with hlt | hgt
            · have hε_eq : ε₀ * c₀' l = -(wF₀ l (i₁ l)) := by
                have hrat' : ratioOf l = wF₀ l (i₁ l) / (-c₀' l) := by simp [ratioOf, hlt]
                have : (-c₀' l) * ε₀ = wF₀ l (i₁ l) := by
                  rw [← hrat_l, hrat']; field_simp [ne_of_gt (neg_pos.mpr hlt)]
                linarith [show (-c₀' l) * ε₀ = -(ε₀ * c₀' l) from by ring]
              suffices h : point'' (emb l) = fF₀ l (i₀ l) by rw [h]; exact hfFS₀ l (i₀ l)
              calc point'' (emb l) = D₀.point (emb l) + ε₀ * c₀' l • δ₀ l := by
                    simp only [point'', hsum_eq, smul_smul]
                _ = fF₀ l (i₀ l) := by
                    rw [← hwFpt₀ l, h2s, hε_eq, δ₀, neg_smul, neg_smul, smul_sub]; abel
            · have hε_eq : ε₀ * c₀' l = wF₀ l (i₀ l) := by
                have hrat' : ratioOf l = wF₀ l (i₀ l) / c₀' l := by
                  simp [ratioOf, not_lt.mpr (le_of_lt hgt), hgt]
                have : c₀' l * ε₀ = wF₀ l (i₀ l) := by
                  rw [← hrat_l, hrat']; field_simp [ne_of_gt hgt]
                linarith [show c₀' l * ε₀ = ε₀ * c₀' l from by ring]
              suffices h : point'' (emb l) = fF₀ l (i₁ l) by rw [h]; exact hfFS₀ l (i₁ l)
              calc point'' (emb l) = D₀.point (emb l) + ε₀ * c₀' l • δ₀ l := by
                    simp only [point'', hsum_eq, smul_smul]
                _ = fF₀ l (i₁ l) := by
                    rw [← hwFpt₀ l, h2s, hε_eq, δ₀, smul_sub]; abel
          exact absurd (hemb'' l) (by
            simp only [D'', Decomposition.excessIndices, Finset.mem_filter, not_and, not_not]
            intro _; exact hlS)
        -- Reduced counts: drop one vertex per l ∈ dropL
        let nF₀' : Fin (d + 1) → ℕ := fun l => if l ∈ dropL then nF₀ l - 1 else nF₀ l
        -- Drop index at l: vertex whose perturbed weight = 0
        let idropAt : ∀ l : Fin (d + 1), Fin (nF₀ l) := fun l =>
          if c₀' l < 0 then i₁ l else i₀ l
        -- Perturbed weights for all indices
        let wP : ∀ l : Fin (d + 1), Fin (nF₀ l) → ℝ := fun l k =>
          if k = i₀ l then wF₀ l k - ε₀ * c₀' l
          else if k = i₁ l then wF₀ l k + ε₀ * c₀' l
          else wF₀ l k
        -- wP l (idropAt l) = 0 for l ∈ dropL
        have hwP_drop : ∀ l ∈ dropL, wP l (idropAt l) = 0 := by
          intro l hl
          have hne_l : c₀' l ≠ 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
          have hrat_l : ratioOf l = ε₀ := (Finset.mem_filter.mp hl).2
          simp only [wP, idropAt]
          rcases lt_or_gt_of_ne hne_l with hlt | hgt
          · simp only [hlt, ↓reduceIte, show ¬(i₁ l = i₀ l) from
                (Fin.ne_of_lt (by simp [i₀, i₁]; omega)).symm, ↓reduceIte]
            have : (-c₀' l) * ε₀ = wF₀ l (i₁ l) := by
              rw [← hrat_l]; simp [ratioOf, hlt]
              field_simp [ne_of_gt (neg_pos.mpr hlt)]
            linarith [show (-c₀' l) * ε₀ = -(ε₀ * c₀' l) from by ring]
          · simp only [not_lt.mpr (le_of_lt hgt), hgt, ↓reduceIte]
            have : c₀' l * ε₀ = wF₀ l (i₀ l) := by
              rw [← hrat_l]; simp [ratioOf, not_lt.mpr (le_of_lt hgt), hgt]
              field_simp [ne_of_gt hgt]
            linarith [show c₀' l * ε₀ = ε₀ * c₀' l from by ring]
        -- ∑ k, wP l k = 1 for all l (perturbation cancels in sum)
        have hwP_sum : ∀ l : Fin (d + 1), ∑ k : Fin (nF₀ l), wP l k = 1 := by
          intro l
          have h01l : i₀ l ≠ i₁ l := Fin.ne_of_lt (by simp [i₀, i₁]; omega)
          simp only [wP]
          conv_lhs =>
            arg 2; ext k
            rw [show (if k = i₀ l then wF₀ l k - ε₀ * c₀' l
                      else if k = i₁ l then wF₀ l k + ε₀ * c₀' l
                      else wF₀ l k) =
                wF₀ l k + (if k = i₁ l then ε₀ * c₀' l else 0) -
                (if k = i₀ l then ε₀ * c₀' l else 0) from by split_ifs <;> ring]
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.sum_ite_eq', Finset.mem_univ, ite_true, hwFsum₀ l]
          ring
        -- ∑ k, wP l k • fF₀ l k = D''.point (emb l) for all l
        have hwP_pt : ∀ l : Fin (d + 1),
            ∑ k : Fin (nF₀ l), wP l k • fF₀ l k = D''.point (emb l) := by
          intro l
          -- D''.point = point''; point'' (emb l) = D₀.point(emb l) + ε₀ * c₀' l • δ₀ l
          change ∑ k : Fin (nF₀ l), wP l k • fF₀ l k = point'' (emb l)
          rw [show point'' (emb l) = D₀.point (emb l) + ε₀ * c₀' l • δ₀ l from by
            simp only [point'', hsum_eq l, smul_smul]]
          rw [← hwFpt₀ l]
          -- Goal: ∑ wP • f = ∑ wF • f + ε * c' • δ
          have h01l : i₀ l ≠ i₁ l := Fin.ne_of_lt (by simp [i₀, i₁]; omega)
          simp only [wP]
          conv_lhs =>
            arg 2; ext k
            rw [show (if k = i₀ l then wF₀ l k - ε₀ * c₀' l
                      else if k = i₁ l then wF₀ l k + ε₀ * c₀' l
                      else wF₀ l k) • fF₀ l k =
                wF₀ l k • fF₀ l k +
                (if k = i₁ l then ε₀ * c₀' l • fF₀ l k else 0) -
                (if k = i₀ l then ε₀ * c₀' l • fF₀ l k else 0) from by
              split_ifs <;> [ring; ring; ring; ring]]
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          rw [Finset.sum_ite_eq', Finset.mem_univ, if_true,
              Finset.sum_ite_eq', Finset.mem_univ, if_true]
          simp [δ₀, smul_sub]; abel
        -- Skip function: Fin(nF₀' l) → Fin(nF₀ l), injective, skipping idropAt l
        -- For l ∉ dropL: nF₀' l = nF₀ l, skip = identity cast
        -- For l ∈ dropL: skip via Fin.succAbove
        have hsucc_cast : ∀ l ∈ dropL, nF₀ l - 1 + 1 = nF₀ l := by
          intro l hl; have := hn3_drop l hl; omega
        let skip : ∀ l : Fin (d + 1), Fin (nF₀' l) → Fin (nF₀ l) := fun l k =>
          if h : l ∈ dropL then
            Fin.cast (hsucc_cast l h) (Fin.succAbove
              ((idropAt l).cast (hsucc_cast l h).symm)
              (k.cast (show nF₀' l = nF₀ l - 1 by simp [nF₀', h])))
          else k.cast (show nF₀' l = nF₀ l by simp [nF₀', h])
        -- skip l k ≠ idropAt l for l ∈ dropL
        have hskip_ne : ∀ l ∈ dropL, ∀ k, skip l k ≠ idropAt l := by
          intro l hl k
          simp only [skip, dif_pos hl]
          intro heq
          have heq' : Fin.succAbove ((idropAt l).cast (hsucc_cast l hl).symm)
              (k.cast (show nF₀' l = nF₀ l - 1 by simp [nF₀', hl])) =
              (idropAt l).cast (hsucc_cast l hl).symm := by
            apply_fun Fin.cast (hsucc_cast l hl) at heq
            simpa [Fin.cast_trans, Fin.cast_refl] using heq
          exact absurd heq' (Fin.succAbove_ne _ _)
        -- skip l is injective
        have hskip_inj : ∀ l, Function.Injective (skip l) := by
          intro l
          by_cases h : l ∈ dropL
          · simp only [skip, dif_pos h]
            intro a b hab
            have hab' := Fin.cast_injective _ hab
            have := (Fin.strictMono_succAbove _).injective hab'
            exact Fin.cast_injective _ this
          · simp only [skip, dif_neg h]
            exact fun a b hab => Fin.cast_injective _ hab
        -- Key: ∑ k, wP l (skip l k) • fF₀ l (skip l k) = ∑ k, wP l k • fF₀ l k
        -- (the missing term wP l (idropAt l) = 0, so sum is unchanged)
        have hskip_sum_smul : ∀ l ∈ dropL,
            ∑ k : Fin (nF₀' l), wP l (skip l k) • fF₀ l (skip l k) =
            ∑ k : Fin (nF₀ l), wP l k • fF₀ l k := by
          intro l hl
          -- Reindex: sum over injective image = sum over all minus missing term (= 0)
          -- Prove image(skip l) = filter(≠ idropAt l) by cardinality
          have hmap_eq : Finset.univ.map ⟨skip l, hskip_inj l⟩ =
              (Finset.univ : Finset (Fin (nF₀ l))).filter (· ≠ idropAt l) := by
            apply Finset.eq_of_subset_of_card_le
            · intro k hk
              simp only [Finset.mem_map, Finset.mem_univ, true_and] at hk
              obtain ⟨j, rfl⟩ := hk
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hskip_ne l hl j⟩
            · rw [Finset.card_map, Fintype.card_fin,
                  show (Finset.univ : Finset (Fin (nF₀ l))).filter (· ≠ idropAt l) =
                      (Finset.univ : Finset (Fin (nF₀ l))).erase (idropAt l) from by
                    ext k; simp [Finset.mem_filter, Finset.mem_erase],
                  Finset.card_erase_of_mem (Finset.mem_univ _), Fintype.card_fin]
              simp only [nF₀', if_pos hl]
          rw [← Finset.sum_map Finset.univ ⟨skip l, hskip_inj l⟩, hmap_eq]
          -- filter(≠ p) = erase p; then use sum_erase_add with zero term
          have herase : (Finset.univ : Finset (Fin (nF₀ l))).filter (· ≠ idropAt l) =
              (Finset.univ : Finset (Fin (nF₀ l))).erase (idropAt l) := by
            ext k; simp [Finset.mem_filter, Finset.mem_erase]
          rw [herase]; symm
          rw [← Finset.sum_erase_add (ha := Finset.mem_univ (idropAt l))]
          simp [hwP_drop l hl]
        -- Key: ∑ k, wP l (skip l k) = ∑ k, wP l k (same zero-term argument)
        have hskip_sum : ∀ l ∈ dropL,
            ∑ k : Fin (nF₀' l), wP l (skip l k) =
            ∑ k : Fin (nF₀ l), wP l k := by
          intro l hl
          have hmap_eq : Finset.univ.map ⟨skip l, hskip_inj l⟩ =
              (Finset.univ : Finset (Fin (nF₀ l))).filter (· ≠ idropAt l) := by
            apply Finset.eq_of_subset_of_card_le
            · intro k hk
              simp only [Finset.mem_map, Finset.mem_univ, true_and] at hk
              obtain ⟨j, rfl⟩ := hk
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hskip_ne l hl j⟩
            · rw [Finset.card_map, Fintype.card_fin,
                  show (Finset.univ : Finset (Fin (nF₀ l))).filter (· ≠ idropAt l) =
                      (Finset.univ : Finset (Fin (nF₀ l))).erase (idropAt l) from by
                    ext k; simp [Finset.mem_filter, Finset.mem_erase],
                  Finset.card_erase_of_mem (Finset.mem_univ _), Fintype.card_fin]
              simp only [nF₀', if_pos hl]
          rw [← Finset.sum_map Finset.univ ⟨skip l, hskip_inj l⟩, hmap_eq]
          have herase : (Finset.univ : Finset (Fin (nF₀ l))).filter (· ≠ idropAt l) =
              (Finset.univ : Finset (Fin (nF₀ l))).erase (idropAt l) := by
            ext k; simp [Finset.mem_filter, Finset.mem_erase]
          rw [herase]; symm
          rw [← Finset.sum_erase_add (ha := Finset.mem_univ (idropAt l))]
          simp [hwP_drop l hl]
        -- Define fF₀' and wF₀'
        let fF₀' : ∀ l, Fin (nF₀' l) → E := fun l k => fF₀ l (skip l k)
        let wF₀' : ∀ l, Fin (nF₀' l) → ℝ := fun l k => wP l (skip l k)
        have hn2' : ∀ l, 2 ≤ nF₀' l := by
          intro l; simp only [nF₀']
          split_ifs with h
          · have := hn3_drop l h; omega
          · exact hn₂₀ l
        have hfmem' : ∀ l k, fF₀' l k ∈ S (emb l) := fun l k => hfFS₀ l (skip l k)
        have hwpos' : ∀ l k, 0 < wF₀' l k := by
          intro l k
          simp only [wF₀', wP]
          split_ifs with h0 h1
          · -- k = i₀ (skip l k), c' behavior
            rcases le_or_lt (c₀' l) 0 with hle | hlt
            · linarith [hwFpos₀ l (skip l k),
                        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hε₀_pos) hle]
            · have hl_act : l ∈ activeL :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_gt hlt⟩
              by_cases hdl : l ∈ dropL
              · -- skip l k ≠ idropAt l, and idropAt l = i₀ l when c' > 0
                have hidrop : idropAt l = i₀ l := by simp [idropAt, not_lt.mpr (le_of_lt hlt)]
                have : skip l k ≠ idropAt l := hskip_ne l hdl k
                rw [hidrop, ← h0] at this; exact absurd rfl this
              · have hle_ratio : ε₀ < ratioOf l :=
                  lt_of_le_of_ne (Finset.inf'_le _ hl_act)
                    (fun h => hdl (Finset.mem_filter.mpr ⟨hl_act, h⟩))
                simp only [ratioOf, not_lt.mpr (le_of_lt hlt), hlt, ↓reduceIte] at hle_ratio
                linarith [div_lt_iff hlt |>.mp hle_ratio, hwFpos₀ l (skip l k)]
          · -- k = i₁ (skip l k)
            rcases le_or_lt 0 (c₀' l) with hge | hlt
            · linarith [hwFpos₀ l (skip l k), mul_nonneg (le_of_lt hε₀_pos) hge]
            · have hl_act : l ∈ activeL :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_lt hlt⟩
              by_cases hdl : l ∈ dropL
              · have hidrop : idropAt l = i₁ l := by simp [idropAt, hlt]
                have : skip l k ≠ idropAt l := hskip_ne l hdl k
                rw [hidrop, ← h1] at this; exact absurd rfl this
              · have hle_ratio : ε₀ < ratioOf l :=
                  lt_of_le_of_ne (Finset.inf'_le _ hl_act)
                    (fun h => hdl (Finset.mem_filter.mpr ⟨hl_act, h⟩))
                simp only [ratioOf, hlt, ↓reduceIte] at hle_ratio
                have hpos : 0 < -c₀' l := neg_pos.mpr hlt
                linarith [div_lt_iff hpos |>.mp hle_ratio, hwFpos₀ l (skip l k)]
          · exact hwFpos₀ l (skip l k)
        have hwsum' : ∀ l, ∑ k, wF₀' l k = 1 := by
          intro l
          simp only [wF₀']
          by_cases h : l ∈ dropL
          · rw [hskip_sum l h, hwP_sum l]
          · simp only [skip, dif_neg h, Fin.cast_refl, Function.comp_id]
            -- skip l k = k.cast, so wP l (skip l k) = wP l k with cast
            have : ∑ k : Fin (nF₀' l), wP l (k.cast (show nF₀' l = nF₀ l by simp [nF₀', h])) =
                ∑ k : Fin (nF₀ l), wP l k := Finset.sum_nbij
                  (fun k => k.cast (show nF₀' l = nF₀ l by simp [nF₀', h]))
                  (fun _ _ => Finset.mem_univ _) (fun _ _ => rfl)
                  (fun a b _ _ h => Fin.cast_injective _ h)
                  (fun b _ => ⟨b.cast (show nF₀ l = nF₀' l by simp [nF₀', h]),
                               Finset.mem_univ _, by simp [Fin.cast_trans]⟩)
            rw [this, hwP_sum l]
        have hwpt' : ∀ l, ∑ k, wF₀' l k • fF₀' l k = D''.point (emb l) := by
          intro l
          simp only [wF₀', fF₀']
          by_cases h : l ∈ dropL
          · rw [hskip_sum_smul l h, hwP_pt l]
          · simp only [skip, dif_neg h]
            have : ∑ k : Fin (nF₀' l), wP l (k.cast (show nF₀' l = nF₀ l by simp [nF₀', h])) •
                fF₀ l (k.cast (show nF₀' l = nF₀ l by simp [nF₀', h])) =
                ∑ k : Fin (nF₀ l), wP l k • fF₀ l k := Finset.sum_nbij
                  (fun k => k.cast (show nF₀' l = nF₀ l by simp [nF₀', h]))
                  (fun _ _ => Finset.mem_univ _) (fun _ _ => rfl)
                  (fun a b _ _ h => Fin.cast_injective _ h)
                  (fun b _ => ⟨b.cast (show nF₀ l = nF₀' l by simp [nF₀', h]),
                               Finset.mem_univ _, by simp [Fin.cast_trans]⟩)
            rw [this, hwP_pt l]
        have hT'_lt : ∑ l : Fin (d + 1), nF₀' l < T₀ := by
          rw [← hT₀]
          apply Finset.sum_lt_sum
          · intro l _
            simp only [nF₀']
            split_ifs with h
            · have := hn3_drop l h; omega
            · le_refl _
          · exact ⟨lmin, Finset.mem_univ _,
              by simp only [nF₀', if_pos hlmin_drop]; have := h2; omega⟩
        obtain ⟨D', hD'⟩ :=
          IH (∑ l, nF₀' l) hT'_lt nF₀' fF₀' wF₀' D'' rfl hemb'' hn2' hfmem' hwpos' hwsum' hwpt'
        exact ⟨D', lt_of_lt_of_le hD' (Finset.card_le_card hsubset'')⟩
      · -- Some emb l₀ ∉ D''.excessIndices → D''.excessIndices ⊊ D₀.excessIndices → done
        push_neg at hemb''
        obtain ⟨l₀, hl₀⟩ := hemb''
        exact ⟨D'', Finset.card_lt_card
          ⟨hsubset'', fun h => hl₀ (h (hemb₀ l₀))⟩⟩

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
      (∀ i, i ∉ t → f i = 0) ∧ ∑ i in t, f i = x) :
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
    {x : E} (hx : x ∈ convexHull ℝ (∑ i in t, S i)) :
    ∃ (f : ι → E),
      (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      ∑ i in t, f i = x ∧
      (t.filter (fun i => f i ∉ S i)).card ≤ Module.finrank ℝ E := by
  -- Step 1: convexHull(∑ Sᵢ) ⊆ ∑ convexHull(Sᵢ)
  -- Proof: ∑ Sᵢ ⊆ ∑ conv(Sᵢ) (monotonicity) and ∑ conv(Sᵢ) is convex,
  -- so convexHull(∑ Sᵢ) ⊆ ∑ conv(Sᵢ) by convexHull_min.
  have h_sub : ∑ i in t, S i ⊆ ∑ i in t, convexHull ℝ (S i) :=
    Set.finset_sum_subset_finset_sum t S (fun i => convexHull ℝ (S i))
      (fun i _ => subset_convexHull ℝ (S i))
  have h_conv : Convex ℝ (∑ i in t, convexHull ℝ (S i)) :=
    convex_sum (fun i => convexHull ℝ (S i)) (fun i _ => convex_convexHull ℝ (S i))
  have hx' : x ∈ ∑ i in t, convexHull ℝ (S i) :=
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
  have hg'_sum : ∑ i in t, g' i = x := by
    have : ∑ i in t, g' i = ∑ i in t, g i :=
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
  -- n • S = ∑ i in Finset.univ, (fun _ => S) i for ι = Fin n
  -- Apply sum_close_to_convexHull with constant family
  have hS_eq : n • S = ∑ i in (Finset.univ : Finset (Fin n)), (fun _ : Fin n => S) i := by
    rw [Finset.sum_const]; simp [Fintype.card_fin]
  rw [hS_eq] at hx
  obtain ⟨f, hf_mem, hf_sum, hf_excess⟩ :=
    sum_close_to_convexHull (fun i _ => hne) hx
  exact ⟨f, fun i => hf_mem i (Finset.mem_univ i), hf_sum, hf_excess⟩

end ShapleyFolkman
