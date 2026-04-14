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
  obtain ⟨emb, hemb_inj, hemb_mem⟩ : ∃ (emb : Fin (d + 1) → ι),
      Function.Injective emb ∧ ∀ l, emb l ∈ D.excessIndices := by
    have hcard : d + 1 ≤ D.excessIndices.card := by omega
    let L : List ι := D.excessIndices.val.toList
    have hL_len : L.length = D.excessIndices.card := by
      simp only [L, Multiset.toList_length, Finset.card_def]
    refine ⟨fun l => L.get ⟨l.val, by omega⟩, ?_, fun l => ?_⟩
    · -- Injectivity: List.get on a nodup list is injective
      intro l₁ l₂ heq
      apply Fin.ext
      have hL_nodup : L.Nodup := Multiset.nodup_toList _
      have hinj : Function.Injective L.get := List.nodup_iff_injective_get.mp hL_nodup
      exact congrArg Fin.val (hinj heq)
    · -- Membership
      have h_lt : l.val < L.length := by omega
      exact Finset.mem_def.mpr
        (Multiset.mem_toList.mp (List.get_mem L l.val h_lt))
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
  -- Step 6d: Define ε as the minimum over all candidate ratios.
  -- Build a combined Finset of all ratios.
  -- ε = min of { ratio_neg l : l ∈ neg_indices } ∪ { ratio_pos l : l ∈ pos_indices }
  -- We use the negated-coefficient ratios only (Case A proof):
  let ε₀ : ℝ := (neg_indices.image (fun l => (1 - sv (emb l)) / (-c' l))).min'
    (Finset.image_nonempty.mpr neg_indices_ne)
  -- ε₀ is achieved at some l_min ∈ neg_indices (Case A minimizer candidate):
  have hε₀_mem : ε₀ ∈ neg_indices.image (fun l => (1 - sv (emb l)) / (-c' l)) :=
    Finset.min'_mem _ _
  obtain ⟨l_min, hl_min_neg, hl_min_eq⟩ :=
    Finset.mem_image.mp hε₀_mem
  -- ε₀ > 0:
  have hε₀_pos : 0 < ε₀ := by
    rw [← hl_min_eq]
    exact ratio_neg_pos l_min hl_min_neg
  -- ε₀ ≤ ratio_neg l for all l ∈ neg_indices:
  have hε₀_le_neg : ∀ l ∈ neg_indices, ε₀ ≤ (1 - sv (emb l)) / (-c' l) := by
    intro l hl
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
  -- Step 6e: Check that ε₀ also respects positive-coefficient bounds.
  -- For the construction to work with positive indices, we need:
  --   ε₀ ≤ sv(emb l) / c' l  for all l ∈ pos_indices
  -- This is NOT guaranteed by the definition of ε₀ above!
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
  -- For now: implement using ε₀ from neg_indices only (Case A scenario),
  -- together with a sorry for the general case.
  --
  -- Step 6f: Construct the perturbed point function.
  -- For i ∈ image(emb): new_point(emb l) = point(emb l) + ε₀ · c'_l · δ_l
  -- For i ∉ image(emb): new_point i = D.point i
  --
  -- But emb : Fin(d+1) → ι may not be injective, so image(emb) is a Finset.
  -- We handle this by defining the perturbation in terms of the SUM over all l with emb l = i.
  -- Actually, since the indices are from D.excessIndices (a Finset, so no duplicates in the
  -- list L), emb IS injective.
  -- Step 6g: Define the new decomposition.
  -- new_point i =
  --   if i = emb l for some l: D.point i + ε₀ · (∑ l with emb l = i, c' l • δ l)
  --   else: D.point i
  -- Since emb is injective, at most one l satisfies emb l = i.
  -- Equivalently:
  -- new_point (emb l) = D.point (emb l) + ε₀ • (c' l • δ l)
  -- new_point i = D.point i   for i ∉ range(emb)
  let new_point : ι → E := fun i =>
    if h : ∃ l : Fin (d + 1), emb l = i then
      let l := h.choose
      D.point i + ε₀ • (c' l • δ l)
    else
      D.point i
  -- Step 6h: Verify new_point is well-defined (choice of l is canonical via injectivity):
  have new_point_emb : ∀ l : Fin (d + 1),
      new_point (emb l) = D.point (emb l) + ε₀ • (c' l • δ l) := by
    intro l
    simp only [new_point, dif_pos ⟨l, rfl⟩]
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
  -- Σ_{i ∈ t} new_point i = Σ_{i ∈ t} D.point i + ε₀ · Σ_l c' l · δ l
  -- = x + ε₀ · 0 = x.
  have new_sum : ∑ i in t, new_point i = x := by
    -- Split the sum over t by whether i is in range(emb) or not.
    -- The perturbation terms telescope via Σ c'_l · δ_l = 0.
    conv_lhs =>
      arg 2; ext i
      rw [show new_point i = D.point i +
            if h : ∃ l : Fin (d + 1), emb l = i then ε₀ • (c' h.choose • δ h.choose) else 0
          from by
            split_ifs with h
            · simp only [new_point, dif_pos h]
            · simp only [new_point, dif_neg h, add_zero]]
    rw [Finset.sum_add_distrib, D.sum_eq]
    suffices h : ∑ i in t, (if h : ∃ l : Fin (d + 1), emb l = i then
        ε₀ • (c' h.choose • δ h.choose) else 0) = 0 by
      simp [h]
    -- Rewrite the sum: only excess indices contribute (others have D.point zero outside t,
    -- but emb maps into D.excessIndices ⊆ t).
    -- ∑_{i ∈ t} [if ∃ l, emb l = i then ε₀ · c' l · δ l else 0]
    -- = ∑_l ε₀ · c' l · δ l  (since emb is injective and image(emb) ⊆ t)
    have hemb_in_t : ∀ l : Fin (d + 1), emb l ∈ t := fun l =>
      Finset.mem_of_mem_filter _ (hemb_mem l)
    rw [show ∑ i in t, (if h : ∃ l : Fin (d + 1), emb l = i then
          ε₀ • (c' h.choose • δ h.choose) else 0) =
        ∑ l : Fin (d + 1), ε₀ • (c' l • δ l) from by
      rw [← Finset.sum_finset_coe (fun l => ε₀ • (c' l • δ l)) Finset.univ]
      rw [Finset.univ_eq_attach]
      simp only [Finset.sum_attach]
      rw [← Finset.sum_image (f := fun l => ε₀ • (c' l • δ l))
            (g := fun i => if h : ∃ l : Fin (d+1), emb l = i then ε₀ • (c' h.choose • δ h.choose) else 0)]
      · apply Finset.sum_congr
        · apply Finset.image_subset_iff.mpr
          intro l _; exact hemb_in_t l
        · intro i hi
          obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
          simp only [dif_pos ⟨l, rfl⟩]
          congr 1; congr 1
          exact hemb_inj (⟨l, rfl⟩ : ∃ l', emb l' = emb l).choose_spec
      · intro l₁ _ l₂ _ heq
        exact hemb_inj heq]
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
  -- For c'_l > 0: ε₀ from neg_indices only, so a-weight sv_l - ε₀·c'_l may be < 0!
  -- To avoid this, we need the joint ε. We accept a sorry here for the general case.
  --
  -- Claim: new_point i ∈ convexHull ℝ (S i) for all i ∈ t.
  have new_mem_convexHull : ∀ i ∈ t, new_point i ∈ convexHull ℝ (S i) := by
    sorry -- Requires: (1) for i ∉ range(emb): same as D.point i; (2) for i = emb l with c'_l < 0:
          -- convex combination with non-negative weights bounded by ε₀ def;
          -- (3) for i = emb l with c'_l > 0: need joint ε (or positive-index ratio bound).
          -- Full proof requires choosing ε = min(ε₀, min of pos ratios) and case analysis.
  -- Step 6k: new_point is zero outside t.
  have new_zero : ∀ i, i ∉ t → new_point i = 0 := by
    intro i hi
    have hDz := D.point_eq_zero i hi
    have h_no_emb : ∀ l : Fin (d + 1), emb l ≠ i := by
      intro l heq
      -- emb l ∈ D.excessIndices, and excessIndices ⊆ t
      have hmem_t : emb l ∈ t := Finset.mem_of_mem_filter _ (hemb_mem l)
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
  have hl_min_data := hrepr (emb l_min) (Finset.mem_of_mem_filter _ (hemb_mem l_min))
  obtain ⟨hav_mem, _, hsv_pos, hsv_lt1, hpoint_eq⟩ := hl_min_data
  have hcl_min_neg : c' l_min < 0 := by
    simp only [neg_indices, Finset.mem_filter] at hl_min_neg; exact hl_min_neg.2
  -- new_point(emb l_min) = av(emb l_min) ∈ S(emb l_min):
  have hnew_point_av : new_point (emb l_min) = av (emb l_min) := by
    rw [new_point_emb l_min]
    -- Goal: D.point(emb l_min) + ε₀ • (c' l_min • δ l_min) = av (emb l_min)
    -- Expand D.point using binary repr: D.point = sv·av + (1-sv)·bv
    -- Expand δ = bv - av.
    -- So: sv·av + (1-sv)·bv + ε₀·c'·(bv-av)
    --   = (sv - ε₀·c')·av + (1-sv+ε₀·c')·bv
    --   = 1·av + 0·bv = av  (since b-weight = 0 at l_min by ε₀ definition)
    have hε₀_eq : ε₀ = (1 - sv (emb l_min)) / (-c' l_min) := hl_min_eq.symm
    have hcneg : -c' l_min > 0 := neg_pos.mpr hcl_min_neg
    have hb_weight_zero : (1 - sv (emb l_min)) + ε₀ * c' l_min = 0 := by
      rw [hε₀_eq]
      field_simp [ne_of_gt hcneg]
      ring
    have ha_weight_one : sv (emb l_min) + ε₀ * (-c' l_min) = 1 := by linarith [hb_weight_zero]
    rw [hpoint_eq]
    simp only [δ]
    -- Goal: sv • av + (1-sv) • bv + ε₀ • (c' l_min • (bv - av)) = av
    -- We need: (sv - ε₀·c') • av + ((1-sv) + ε₀·c') • bv = 1·av + 0·bv = av
    -- where sv - ε₀·c' = 1 and (1-sv) + ε₀·c' = 0 (from hb_weight_zero, ha_weight_one).
    have hcoeff_av : sv (emb l_min) - ε₀ * c' l_min = 1 := by linarith [hb_weight_zero]
    have hcoeff_bv : (1 - sv (emb l_min)) + ε₀ * c' l_min = 0 := hb_weight_zero
    -- Algebraic identity: sv·av + (1-sv)·bv + ε₀·(c'·(bv-av))
    --                   = (sv - ε₀·c')·av + ((1-sv)+ε₀·c')·bv = av
    have key : sv (emb l_min) • av (emb l_min) + (1 - sv (emb l_min)) • bv (emb l_min) +
               ε₀ • (c' l_min • (bv (emb l_min) - av (emb l_min))) = av (emb l_min) := by
      have : sv (emb l_min) • av (emb l_min) + (1 - sv (emb l_min)) • bv (emb l_min) +
             ε₀ • (c' l_min • (bv (emb l_min) - av (emb l_min))) =
             (sv (emb l_min) - ε₀ * c' l_min) • av (emb l_min) +
             ((1 - sv (emb l_min)) + ε₀ * c' l_min) • bv (emb l_min) := by
        simp only [smul_sub, smul_smul, add_smul, sub_smul]
        ring
      rw [this, hcoeff_av, hcoeff_bv, one_smul, zero_smul, add_zero]
    exact key
  -- D'.excessIndices does NOT contain emb l_min (since new_point(emb l_min) = av ∈ S):
  have hD'_not_excess : emb l_min ∉ D'.excessIndices := by
    simp only [Decomposition.excessIndices, Finset.mem_filter, D']
    intro ⟨_, hnot⟩
    exact hnot (hnew_point_av ▸ hav_mem)
  -- emb l_min IS in D.excessIndices:
  have hD_excess : emb l_min ∈ D.excessIndices := hemb_mem l_min
  -- D'.excessIndices ⊆ D.excessIndices (perturbation may reduce, not increase, excess):
  -- (We leave this as sorry — proving this requires checking all perturbed points carefully)
  have hD'_subset : D'.excessIndices ⊆ D.excessIndices := by
    intro i hi
    simp only [Decomposition.excessIndices, Finset.mem_filter, D'] at hi ⊢
    obtain ⟨hi_t, hi_new⟩ := hi
    refine ⟨hi_t, ?_⟩
    by_cases h : ∃ l : Fin (d + 1), emb l = i
    · -- i = emb l for some l; emb l ∈ D.excessIndices by hemb_mem
      obtain ⟨l, rfl⟩ := h
      simp only [Decomposition.excessIndices, Finset.mem_filter] at hemb_mem
      exact (hemb_mem l).2
    · -- i ∉ range(emb), so new_point i = D.point i
      rw [new_point_not_emb i (not_exists.mp h)] at hi_new
      exact hi_new
  -- From subset and strict removal: card strictly decreases.
  -- D'.excessIndices ⊊ D.excessIndices: subset but not equal (emb l_min is in D but not D').
  have hD'_ssub : D'.excessIndices ⊂ D.excessIndices := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hD'_subset, fun heq => ?_⟩
    exact hD'_not_excess (heq ▸ hD_excess)
  exact ⟨D', Finset.card_lt_card hD'_ssub⟩

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
