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

Status: formalized (1 sorry in reduce_excess_by_one Step 6, Case B).
  Case A (minimizer has c' < 0) is now fully proved.
  Case B (minimizer has c' ≥ 0) requires Carathéodory vertex-count descent:
    induct on total vertex count across all Carathéodory representations,
    not just excess count. See Step 6 Case B comments for architecture.
  NOT submittable to Aristotle: requires structural proof, not tactic search.)
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Filter.Basic

set_option linter.unusedVariables false

open Set Finset
open scoped BigOperators Pointwise

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
  obtain ⟨emb, hemb_mem⟩ : ∃ (emb : Fin (d + 1) → ι),
      ∀ l, emb l ∈ D.excessIndices := by
    have hcard : d + 1 ≤ D.excessIndices.card := by omega
    let L : List ι := D.excessIndices.val.toList
    have hL_len : L.length = D.excessIndices.card := by
      simp only [L, Multiset.toList_length, Finset.card_def]
    refine ⟨fun l => L.get ⟨l.val, by omega⟩, fun l => ?_⟩
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
  -- ε = inf of binding constraints: ensures all convex weights stay ≥ 0 after perturbation.
  --   For c' l > 0: a-weight sv(emb l) - ε·c' l ≥ 0  requires  ε ≤ sv(emb l) / c' l
  --   For c' l < 0: b-weight 1-sv(emb l) + ε·c' l ≥ 0  requires  ε ≤ (1-sv(emb l)) / (-c' l)
  -- The minimizing index lmin (achieving ε = bnd lmin) exits excess when c' lmin < 0
  -- (b-weight drops to 0, point' = av ∈ S).  When c' lmin > 0, the a-weight drops to 0
  -- (point' = bv ∈ convexHull(S)).  The latter case requires Carathéodory descent (see sorry).
  --
  -- Define binding constraints
  let bnd : Fin (d + 1) → ℝ := fun l =>
    if 0 < c' l then sv (emb l) / c' l
    else if c' l < 0 then (1 - sv (emb l)) / (-(c' l))
    else 1
  have hbnd_pos : ∀ l, 0 < bnd l := fun l => by
    simp only [bnd]; split_ifs with h₁ h₂
    · exact div_pos (hrepr (emb l) (hemb_mem l)).2.2.1 h₁
    · exact div_pos (by linarith [(hrepr (emb l) (hemb_mem l)).2.2.2.1]) (by linarith)
    · exact one_pos
  -- ε is the minimum of all binding constraints (achieved at some lmin)
  let ε : ℝ := Finset.inf' Finset.univ ⟨lneg, Finset.mem_univ _⟩ bnd
  have hε_le : ∀ l : Fin (d + 1), ε ≤ bnd l :=
    fun l => Finset.inf'_le _ (Finset.mem_univ l)
  have hε_pos : 0 < ε := by
    obtain ⟨lmin, _, hlmin⟩ := Finset.exists_min_image Finset.univ bnd ⟨lneg, Finset.mem_univ _⟩
    have hε_eq : ε = bnd lmin :=
      le_antisymm (Finset.inf'_le _ (Finset.mem_univ _))
                  (Finset.le_inf' _ _ (fun l _ => hlmin l (Finset.mem_univ _)))
    linarith [hbnd_pos lmin]
  -- emb is injective (comes from List.get on a nodup Finset list)
  have hemb_inj : Function.Injective emb := by
    intro l₁ l₂ h
    have hnodup : (D.excessIndices.val.toList).Nodup := Multiset.toList_nodup _
    have hlen : (D.excessIndices.val.toList).length = D.excessIndices.card := by
      simp [Multiset.toList_length, Finset.card_def]
    have hl₁ : l₁.val < (D.excessIndices.val.toList).length := by omega
    have hl₂ : l₂.val < (D.excessIndices.val.toList).length := by omega
    exact Fin.ext ((hnodup.get_inj_iff hl₁ hl₂).mp h)
  -- Perturbation adjustment: ε · (Σ c' l · δ l for emb l = i)
  let adj : ι → E := fun i =>
    ε • ∑ l : Fin (d + 1), if emb l = i then c' l • δ l else 0
  let D'_pt : ι → E := fun i => D.point i + adj i
  -- adj(emb l) = ε · c' l · δ l  (by injectivity, only one term contributes)
  have hadj_l : ∀ l : Fin (d + 1), adj (emb l) = ε • c' l • δ l := fun l => by
    simp only [adj]
    congr 1
    rw [Fintype.sum_eq_single l (fun l' hl' => by simp [hemb_inj.ne hl'])]
    simp
  -- emb l ∈ t for all l (excess indices are in t)
  have hemb_in_t : ∀ l : Fin (d + 1), emb l ∈ t :=
    fun l => (Finset.mem_filter.mp (hemb_mem l)).1
  -- Sum of adj over t is 0 (uses hc'δ)
  have hadj_sum : ∑ i in t, adj i = 0 := by
    simp only [adj, ← Finset.smul_sum]
    suffices h : ∑ i in t, ∑ l : Fin (d + 1), (if emb l = i then c' l • δ l else 0) =
        ∑ l : Fin (d + 1), c' l • δ l by rw [h, hc'δ, smul_zero]
    rw [Finset.sum_comm]
    congr 1; ext l
    rw [Finset.sum_ite_eq', if_pos (hemb_in_t l)]
  -- D'_pt sum preserved
  have hD'_sum : ∑ i in t, D'_pt i = x := by
    simp only [D'_pt, Finset.sum_add_distrib, D.sum_eq, hadj_sum, add_zero]
  -- D'_pt = 0 outside t
  have hD'_zero : ∀ i, i ∉ t → D'_pt i = 0 := fun i hi => by
    simp only [D'_pt, adj, D.point_eq_zero i hi, zero_add, smul_sum, smul_eq_zero]
    right; apply Finset.sum_eq_zero; intro l _
    simp [show emb l ≠ i from fun h => hi (h ▸ hemb_in_t l)]
  -- Weight bounds: after perturbation, both convex weights at each excess index are ≥ 0
  have hweights : ∀ l : Fin (d + 1),
      0 ≤ sv (emb l) - ε * c' l ∧ 0 ≤ 1 - sv (emb l) + ε * c' l := fun l => by
    obtain ⟨_, _, hsv_pos, hsv_lt1, _⟩ := hrepr (emb l) (hemb_mem l)
    have hle := hε_le l
    have hbnd_eq : bnd l = if 0 < c' l then sv (emb l) / c' l
        else if c' l < 0 then (1 - sv (emb l)) / (-(c' l)) else 1 := rfl
    rw [hbnd_eq] at hle
    split_ifs at hle with h₁ h₂
    · -- c' l > 0: ε ≤ sv/c' → ε·c' ≤ sv (a-weight ≥ 0); b-weight ≥ 1-sv > 0
      have hbound := (le_div_iff h₁).mp hle
      exact ⟨by linarith, by nlinarith [mul_pos hε_pos h₁]⟩
    · -- c' l < 0: ε ≤ (1-sv)/(-c') → ε·(-c') ≤ 1-sv (b-weight ≥ 0); a-weight ≥ sv > 0
      have hbound := (le_div_iff (neg_pos.mpr h₂)).mp hle
      exact ⟨by nlinarith [mul_neg_of_pos_of_neg hε_pos h₂], by linarith⟩
    · -- c' l = 0: no perturbation
      push_neg at h₁ h₂
      have hc'0 : c' l = 0 := le_antisymm h₁ (not_lt.mp h₂)
      simp [hc'0, hsv_pos.le, hsv_lt1.le]
  -- D'_pt at each excess index is in convexHull(S) (convex combination with ≥ 0 weights)
  have hD'_excess_conv : ∀ l : Fin (d + 1), D'_pt (emb l) ∈ convexHull ℝ (S (emb l)) := by
    intro l
    obtain ⟨hav_S, hbv_conv, _, _, hpt_eq⟩ := hrepr (emb l) (hemb_mem l)
    obtain ⟨hnn_a, hnn_b⟩ := hweights l
    rw [show D'_pt (emb l) = (sv (emb l) - ε * c' l) • av (emb l) +
        (1 - sv (emb l) + ε * c' l) • bv (emb l) from by
      simp only [D'_pt, hadj_l l, δ]; rw [hpt_eq]; ring]
    exact convex_convexHull ℝ (S (emb l))
      (subset_convexHull ℝ _ hav_S) hbv_conv hnn_a hnn_b (by ring)
  -- D'_pt i ∈ convexHull(S i) for all i ∈ t
  have hD'_mem : ∀ i ∈ t, D'_pt i ∈ convexHull ℝ (S i) := fun i hi => by
    by_cases hrange : ∃ l : Fin (d + 1), emb l = i
    · obtain ⟨l, rfl⟩ := hrange; exact hD'_excess_conv l
    · push_neg at hrange
      simp only [D'_pt, adj, show ∀ l : Fin (d + 1), emb l ≠ i from hrange,
        ite_false, Finset.sum_const_zero, smul_zero, add_zero]
      exact D.mem_convexHull i hi
  -- Construct D'
  refine ⟨⟨D'_pt, hD'_mem, hD'_zero, hD'_sum⟩, ?_⟩
  -- Goal: D'.excessIndices.card < D.excessIndices.card
  --
  -- Key proof structure:
  --   1. D'.excessIndices ⊆ D.excessIndices  (perturbation never creates new excess indices)
  --   2. Case A (global minimizer has c'(lmin) < 0): emb(lmin) exits excess → strict subset
  --   3. Case B (global minimizer has c'(lmin) ≥ 0): Carathéodory descent needed (sorry)
  --
  -- For (1): D'_pt i = D.point i for i ∉ image(emb), so non-excess stays non-excess.
  -- For emb l: D'_pt(emb l) ∈ convexHull(S(emb l)) and emb l ∈ D.excessIndices by hemb_mem.
  have hsub : D'.excessIndices ⊆ D.excessIndices := by
    intro i hi
    simp only [Decomposition.excessIndices, Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    by_cases hrange : ∃ l : Fin (d + 1), emb l = i
    · obtain ⟨l, rfl⟩ := hrange
      exact (Finset.mem_filter.mp (hemb_mem l)).2
    · push_neg at hrange
      have heq : D'_pt i = D.point i := by
        simp only [D'_pt, adj, show ∀ l : Fin (d + 1), emb l ≠ i from hrange,
          ite_false, Finset.sum_const_zero, smul_zero, add_zero]
      rw [heq] at hi; exact hi.2
  -- Get a minimizer lmin (achieving the infimum)
  obtain ⟨lmin, -, hlmin⟩ :=
    Finset.exists_min_image Finset.univ bnd ⟨lneg, Finset.mem_univ _⟩
  have hε_eq : ε = bnd lmin :=
    le_antisymm (Finset.inf'_le _ (Finset.mem_univ _))
                (Finset.le_inf' _ _ (fun l _ => hlmin l (Finset.mem_univ _)))
  -- Case split on sign of c'(lmin)
  rcases lt_or_le (c' lmin) 0 with hlmin_neg | hlmin_nonneg
  · -- Case A: c'(lmin) < 0
    -- bnd(lmin) = (1-sv(emb lmin)) / (-c'(lmin)), so ε * c'(lmin) = -(1-sv(emb lmin))
    -- b-weight = 1 - sv(emb lmin) + ε * c'(lmin) = 0 → D'_pt(emb lmin) = av(emb lmin) ∈ S
    have hbnd_lmin : bnd lmin = (1 - sv (emb lmin)) / (-(c' lmin)) := by
      simp only [bnd, if_neg (not_lt.mpr hlmin_neg.le), if_pos hlmin_neg]
    have hc'ne : -(c' lmin) ≠ 0 := neg_ne_zero.mpr (ne_of_lt hlmin_neg)
    have hb_zero : 1 - sv (emb lmin) + ε * c' lmin = 0 := by
      rw [hε_eq, hbnd_lmin]
      field_simp [hc'ne]; ring
    have ha_one : sv (emb lmin) - ε * c' lmin = 1 := by linarith [hb_zero]
    -- D'_pt(emb lmin) = av(emb lmin) ∈ S(emb lmin)
    have hDprime_lmin : D'_pt (emb lmin) = av (emb lmin) := by
      rw [show D'_pt (emb lmin) = (sv (emb lmin) - ε * c' lmin) • av (emb lmin) +
          (1 - sv (emb lmin) + ε * c' lmin) • bv (emb lmin) from by
        simp only [D'_pt, hadj_l lmin, δ]
        rw [(hrepr (emb lmin) (hemb_mem lmin)).2.2.2.2]; ring]
      rw [ha_one, hb_zero, one_smul, zero_smul, add_zero]
    -- emb lmin ∉ D'.excessIndices (D'_pt = av ∈ S)
    have hlmin_out : emb lmin ∉ D'.excessIndices := by
      simp only [Decomposition.excessIndices, Finset.mem_filter, not_and, not_not]
      intro _; rw [hDprime_lmin]; exact (hrepr (emb lmin) (hemb_mem lmin)).1
    -- D'.excessIndices ⊊ D.excessIndices → card strictly decreases
    exact Finset.card_lt_card ⟨hsub, fun h => hlmin_out (h (hemb_mem lmin))⟩
  · -- Case B: c'(lmin) ≥ 0
    -- When c'(lmin) > 0: D'_pt(emb lmin) = bv(emb lmin) ∈ convexHull(S(emb lmin)).
    --   If bv ∉ S, emb(lmin) remains in excess. All other excess indices also remain.
    -- When c'(lmin) = 0: no perturbation at lmin; other indices stay in strict conv. comb.
    --
    -- Both cases require Carathéodory descent: induct on total vertex count across all
    -- Carathéodory representations (not just excess count). Each perturbation step removes
    -- exactly one vertex, regardless of Case A or B. When vertex count reaches |t| + d,
    -- no more than d indices can have ≥ 2 vertices → excess ≤ d.
    --
    -- Architecture needed:
    --   (a) Decorated decomposition: Decomposition + Carathéodory data per index
    --   (b) Total vertex count: a natural number that decreases each step
    --   (c) Well-founded recursion on vertex count (not excess count)
    --
    -- Estimated: 80-120 additional lines
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
