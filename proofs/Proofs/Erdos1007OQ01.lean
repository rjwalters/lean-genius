/-
Erdős Problem #1007 OQ-01: Minimum Edges for Graph Dimension d in General

Extension of Erdos1007Problem.lean studying the function minEdges(d) = minimum
number of edges in a graph of dimension exactly d.

Known values:
  d=1: minEdges(1) = 1  (K₂)
  d=2: minEdges(2) = 3  (K₃)
  d=3: minEdges(3) = 6  (K₄)
  d=4: minEdges(4) = 9  (K_{3,3}, House 2013)
  d=5: minEdges(5) = 15 (K₆ or K_{1,3,3}, Chaffee-Noble 2016)

Key observations:
- For d ≤ 3: minEdges(d) = C(d+1, 2) = d(d+1)/2 (complete graph K_{d+1})
- For d = 4: minEdges(4) = 9 < C(5,2) = 10 (K_{3,3} beats K₅)
- For d = 5: minEdges(5) = 15 = C(6,2) (K₆ is optimal again)

The general question: What is minEdges(d) as a function of d?

Lower bound (trivial): minEdges(d) ≥ d (need at least d edges for d-dimensional rigidity)
Upper bound: minEdges(d) ≤ C(d+1, 2) (K_{d+1} always has dimension d)

This formalization proves:
- Simplex embedding: K_n embeds in ℝⁿ with unit distances (§1b, proved)
- Every irreflexive graph has a unit embedding (§1c, proved — no axiom needed)
- Known values and structural results for small d (§3-4)
- General upper/lower bounds (§5)
- The complete graph optimality conjecture implies monotonicity (§8)
- The complete graph optimality conjecture implies quadratic growth (§8)
- Verified monotonicity of C(d+1,2) as a building block (§8)
- Growth rate analysis from known values (§9)

Axiom count: 11 (all for computational search results or rigidity bounds)
-/

import Mathlib

open Finset

-- ============================================================================
-- § 1. Graph Dimension (from parent file)
-- ============================================================================

/-- A unit distance embedding of a graph in ℝⁿ -/
structure UnitDistanceEmbedding' (V : Type*) (adj : V → V → Prop) (n : ℕ) where
  embed : V → Fin n → ℝ
  unit_edges : ∀ u v, adj u v →
    Real.sqrt (Finset.univ.sum fun i => (embed u i - embed v i)^2) = 1

/-- A graph can be embedded as unit distances in ℝⁿ -/
def hasUnitEmbedding' (V : Type*) (adj : V → V → Prop) (n : ℕ) : Prop :=
  Nonempty (UnitDistanceEmbedding' V adj n)

-- ============================================================================
-- § 1b. Simplex Embedding Construction
-- ============================================================================

-- The key construction: embed vertex i as (1/√2) · eᵢ in ℝⁿ.
-- Then for i ≠ j: ‖vᵢ - vⱼ‖² = (1/√2)² + (-1/√2)² = 1/2 + 1/2 = 1.
-- This gives a unit-distance embedding of K_n in ℝⁿ.
--
-- This infrastructure is placed early because it's needed to prove that
-- every irreflexive graph has a unit embedding (§1c), which is required
-- by the definition of graphDimension' below.

/-- The simplex embedding function: vertex i maps to (1/√2) eᵢ -/
noncomputable def simplexEmbed (n : ℕ) (i : Fin n) (j : Fin n) : ℝ :=
  if i = j then 1 / Real.sqrt 2 else 0

/-- Key lemma: (1/√2)² = 1/2 -/
private theorem inv_sqrt_two_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
  have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- Key computation: the squared difference at coordinate k for distinct vertices i, j.
    This equals 1/2 when k = i or k = j, and 0 otherwise. -/
theorem simplexEmbed_sq_diff (n : ℕ) (i j : Fin n) (hij : i ≠ j) (k : Fin n) :
    (simplexEmbed n i k - simplexEmbed n j k) ^ 2 =
      if k = i then 1 / 2 else if k = j then 1 / 2 else 0 := by
  simp only [simplexEmbed]
  by_cases hki : i = k
  · subst hki
    simp only [if_true, ite_eq_right_iff]
    have : ¬(j = i) := hij.symm
    simp only [this, ite_false, sub_zero, ite_true]
    exact inv_sqrt_two_sq
  · by_cases hkj : j = k
    · subst hkj
      simp only [hki, ite_false, if_true, zero_sub, neg_sq, Ne.symm hij, ite_false, ite_true]
      exact inv_sqrt_two_sq
    · simp only [hki, hkj, ite_false, sub_self, zero_pow, Ne.symm hki, Ne.symm hkj]
      norm_num

/-- The squared distance sum for the simplex embedding equals 1. -/
theorem simplexEmbed_dist_sq (n : ℕ) (hn : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    Finset.univ.sum (fun k => (simplexEmbed n i k - simplexEmbed n j k) ^ 2) = 1 := by
  simp_rw [simplexEmbed_sq_diff n i j hij]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  have h1 : ∀ k ∈ Finset.univ.erase i,
      (if k = i then (1:ℝ)/2 else if k = j then 1/2 else 0) =
      if k = j then 1/2 else 0 := by
    intro k hk; simp [(Finset.mem_erase.mp hk).1]
  rw [Finset.sum_congr rfl h1]
  have hj_mem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  rw [← Finset.add_sum_erase _ _ hj_mem]
  simp only [ite_true]
  have h2 : ∀ k ∈ (Finset.univ.erase i).erase j,
      (if k = j then (1:ℝ)/2 else 0) = 0 := by
    intro k hk; simp [(Finset.mem_erase.mp hk).1]
  rw [Finset.sum_congr rfl h2, Finset.sum_const_zero]
  ring

/-- The complete graph K_n admits a unit-distance embedding in ℝⁿ for n ≥ 2. -/
theorem complete_graph_unit_embedding (n : ℕ) (hn : 2 ≤ n) :
    hasUnitEmbedding' (Fin n) (fun i j => i ≠ j) n := by
  refine ⟨⟨simplexEmbed n, fun u v huv => ?_⟩⟩
  rw [simplexEmbed_dist_sq n hn u v huv, Real.sqrt_one]

/-- Any subgraph of K_n inherits the unit embedding from K_n. -/
theorem subgraph_unit_embedding (n : ℕ) (hn : 2 ≤ n)
    (adj : Fin n → Fin n → Prop) (hsub : ∀ u v, adj u v → u ≠ v) :
    hasUnitEmbedding' (Fin n) adj n := by
  refine ⟨⟨simplexEmbed n, fun u v hadj => ?_⟩⟩
  rw [simplexEmbed_dist_sq n hn u v (hsub u v hadj), Real.sqrt_one]

-- ============================================================================
-- § 1c. Embedding Existence (Proved)
-- ============================================================================

-- Every irreflexive (simple) graph admits a unit-distance embedding in some ℝⁿ.
-- Irreflexivity is essential: self-loops require ‖v - v‖ = ‖0‖ = 1, which
-- is impossible, so graphs with self-loops have NO unit embedding.
-- (A prior version axiomatized this without irreflexivity, which was unsound —
-- it allowed derivation of False for any graph with a self-loop.)
--
-- Proof: If |V| ≤ 1, irreflexivity forces adj to be empty, so any map works.
-- If |V| ≥ 2, compose the simplex embedding with V ≃ Fin |V|. Since adj is
-- irreflexive, adj u v → u ≠ v, so the complete graph's unit embedding works.
open Classical in
theorem hasUnitEmbedding_exists_irrefl (V : Type*) [Fintype V]
    (adj : V → V → Prop) (hirr : Irreflexive adj) :
    ∃ n, hasUnitEmbedding' V adj n := by
  by_cases hcard : Fintype.card V ≤ 1
  · use 1
    refine ⟨⟨fun _ _ => 0, fun u v hadj => ?_⟩⟩
    exact absurd (Fintype.card_le_one_iff.mp hcard u v ▸ hadj) (hirr u)
  · push_neg at hcard
    set c := Fintype.card V
    have hc2 : 2 ≤ c := hcard
    use c
    have e : V ≃ Fin c := (Fintype.truncEquivFin V).out
    refine ⟨⟨fun v => simplexEmbed c (e v), fun u v hadj => ?_⟩⟩
    have huv : u ≠ v := fun h => hirr u (h ▸ hadj)
    rw [simplexEmbed_dist_sq c hc2 (e u) (e v) (e.injective.ne huv), Real.sqrt_one]

-- ============================================================================
-- § 1d. Graph Dimension
-- ============================================================================

open Classical in
noncomputable def graphDimension' (V : Type*) [Fintype V] (adj : V → V → Prop)
    (hirr : Irreflexive adj) : ℕ :=
  Nat.find (hasUnitEmbedding_exists_irrefl V adj hirr)

-- ============================================================================
-- § 2. Minimum Edge Function
-- ============================================================================

/-- minEdges(d) is the minimum number of edges among all graphs with dimension d.
    We axiomatize this as extracting the minimum requires a search over all graphs. -/
axiom minEdgesForDim : ℕ → ℕ

-- ============================================================================
-- § 3. Known Values
-- ============================================================================

/-- minEdges(0) = 0 (no edges in a 0-dimensional graph, which embeds in ℝ⁰) -/
axiom minEdges_dim0 : minEdgesForDim 0 = 0

/-- minEdges(1) = 1 (a single edge = K₂) -/
axiom minEdges_dim1 : minEdgesForDim 1 = 1

/-- minEdges(2) = 3 (triangle = K₃) -/
axiom minEdges_dim2 : minEdgesForDim 2 = 3

/-- minEdges(3) = 6 (tetrahedron = K₄) -/
axiom minEdges_dim3 : minEdgesForDim 3 = 6

/-- minEdges(4) = 9 (K_{3,3}, House 2013) -/
axiom minEdges_dim4 : minEdgesForDim 4 = 9

/-- minEdges(5) = 15 (K₆ or K_{1,3,3}, Chaffee-Noble 2016) -/
axiom minEdges_dim5 : minEdgesForDim 5 = 15

-- ============================================================================
-- § 4. Structural Results
-- ============================================================================

/-- For d ≤ 3, the minimum is achieved by the complete graph K_{d+1},
    giving minEdges(d) = C(d+1, 2) = d(d+1)/2. -/
theorem small_dim_complete (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    minEdgesForDim d = Nat.choose (d + 1) 2 := by
  interval_cases d
  · rw [minEdges_dim1]; native_decide
  · rw [minEdges_dim2]; native_decide
  · rw [minEdges_dim3]; native_decide

/-- For d = 4, the complete graph K₅ has C(5,2) = 10 edges but K_{3,3}
    achieves dimension 4 with only 9 edges. This is the first "surprise". -/
theorem dim4_beats_complete : minEdgesForDim 4 < Nat.choose 5 2 := by
  rw [minEdges_dim4]
  native_decide

/-- For d = 5, the minimum equals C(6,2) again. -/
theorem dim5_matches_complete : minEdgesForDim 5 = Nat.choose 6 2 := by
  rw [minEdges_dim5]
  native_decide

-- ============================================================================
-- § 5. General Bounds
-- ============================================================================

/-- Trivial lower bound: a graph of dimension d must have at least d edges.
    (Intuition: d independent constraints require d edges minimum.) -/
axiom minEdges_lower_bound (d : ℕ) (hd : 0 < d) :
    d ≤ minEdgesForDim d

/-- Upper bound: K_{d+1} always achieves dimension d (for d ≥ 1),
    so minEdges(d) ≤ C(d+1, 2). -/
axiom minEdges_upper_bound (d : ℕ) (hd : 0 < d) :
    minEdgesForDim d ≤ Nat.choose (d + 1) 2

/-- The values so far grow roughly quadratically in d:
    1, 3, 6, 9, 15 for d = 1,...,5. -/
theorem values_are_nondecreasing_small :
    minEdgesForDim 1 ≤ minEdgesForDim 2 ∧
    minEdgesForDim 2 ≤ minEdgesForDim 3 ∧
    minEdgesForDim 3 ≤ minEdgesForDim 4 ∧
    minEdgesForDim 4 ≤ minEdgesForDim 5 := by
  simp [minEdges_dim1, minEdges_dim2, minEdges_dim3, minEdges_dim4, minEdges_dim5]

-- ============================================================================
-- § 6. Open Questions and Conjectures
-- ============================================================================

/-- Is minEdges monotone? I.e., does d₁ ≤ d₂ imply minEdges(d₁) ≤ minEdges(d₂)? -/
def minEdges_monotone_conjecture : Prop :=
  ∀ d₁ d₂ : ℕ, d₁ ≤ d₂ → minEdgesForDim d₁ ≤ minEdgesForDim d₂

/-- Does minEdges(d) = Θ(d²)? The data suggests quadratic growth. -/
def minEdges_quadratic_conjecture : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    ∀ d : ℕ, 1 ≤ d →
      c₁ * (d : ℝ) ^ 2 ≤ (minEdgesForDim d : ℝ) ∧
      (minEdgesForDim d : ℝ) ≤ c₂ * (d : ℝ) ^ 2

/-- Is K_{d+1} always optimal (for d ≠ 4)?
    Known: yes for d ≤ 3 and d = 5. The d = 4 case is the only known exception. -/
def complete_graph_optimal_conjecture : Prop :=
  ∀ d : ℕ, d ≠ 4 → 1 ≤ d → minEdgesForDim d = Nat.choose (d + 1) 2

/-- The upper bound from C(d+1,2) gives quadratic growth explicitly. -/
theorem upper_bound_quadratic (d : ℕ) (hd : 1 ≤ d) :
    (minEdgesForDim d : ℝ) ≤ ((d + 1 : ℝ) * d) / 2 := by
  have hub := minEdges_upper_bound d (by omega)
  have hle : (minEdgesForDim d : ℝ) ≤ (Nat.choose (d + 1) 2 : ℝ) := Nat.cast_le.mpr hub
  suffices h : (Nat.choose (d + 1) 2 : ℝ) = ((d + 1 : ℝ) * d) / 2 by linarith
  rw [Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  have hdvd : 2 ∣ (d + 1) * d := by
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
    · exact ⟨(2 * k + 1) * k, by ring⟩
    · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
  rw [Nat.cast_div hdvd (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast; ring

/-- The lower bound d gives at least linear growth. -/
theorem lower_bound_linear (d : ℕ) (hd : 1 ≤ d) :
    (d : ℝ) ≤ (minEdgesForDim d : ℝ) := by
  exact_mod_cast minEdges_lower_bound d (by omega)

-- ============================================================================
-- § 7. Graph Dimension of Complete Graphs
-- ============================================================================

-- Corollary: graphDimension(K_n) ≤ n for n ≥ 2.
-- (The optimal bound is n-1, which requires a harder rigidity argument.)
open Classical in
theorem complete_graph_dim_le (n : ℕ) (hn : 2 ≤ n) :
    graphDimension' (Fin n) (fun i j => i ≠ j) (fun x h => h rfl) ≤ n := by
  exact Nat.find_le ⟨⟨simplexEmbed n, fun u v huv => by
    rw [simplexEmbed_dist_sq n hn u v huv, Real.sqrt_one]⟩⟩

-- ============================================================================
-- § 8. Conjecture Relationships
-- ============================================================================

-- We prove that the complete graph optimality conjecture (for d ≠ 4)
-- implies the monotonicity conjecture. The key ingredient is that
-- C(d+1, 2) is monotone in d.

/-- C(n, 2) is monotone: if n ≤ m then C(n,2) ≤ C(m,2). -/
theorem choose_two_mono {n m : ℕ} (h : n ≤ m) : Nat.choose n 2 ≤ Nat.choose m 2 :=
  Nat.choose_le_choose 2 h

/-- Monotonicity of C(d+1, 2) in d. -/
theorem choose_succ_two_mono {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    Nat.choose (d₁ + 1) 2 ≤ Nat.choose (d₂ + 1) 2 :=
  choose_two_mono (by omega)

/-- C(d+1, 2) ≥ d for all d ≥ 1. This means the upper bound from
    complete graphs is always at least as large as the lower bound. -/
theorem choose_succ_two_ge (d : ℕ) (hd : 1 ≤ d) : d ≤ Nat.choose (d + 1) 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  have h1 : 2 * d ≤ (d + 1) * d := by nlinarith
  omega

/-- The complete graph optimality conjecture implies monotonicity.
    Proof: For d ≠ 4, use C(d+1,2) monotonicity. For d = 4, use the
    known value 9 which sits between C(4,2)=6 and C(6,2)=15. -/
theorem optimal_implies_monotone :
    complete_graph_optimal_conjecture → minEdges_monotone_conjecture := by
  intro hopt d₁ d₂ hle
  by_cases hd1 : d₁ = 0
  · subst hd1; rw [minEdges_dim0]; exact Nat.zero_le _
  by_cases hd2 : d₂ = 0
  · omega
  -- Both d₁, d₂ ≥ 1
  have hd1_pos : 1 ≤ d₁ := by omega
  have hd2_pos : 1 ≤ d₂ := by omega
  by_cases h4a : d₁ = 4
  · -- d₁ = 4, so d₂ ≥ 4
    subst h4a
    by_cases h4b : d₂ = 4
    · subst h4b; exact le_refl _
    · -- d₂ > 4 and d₂ ≠ 4
      rw [minEdges_dim4, hopt d₂ h4b (by omega)]
      calc 9 = Nat.choose 5 2 - 1 := by native_decide
        _ ≤ Nat.choose (d₂ + 1) 2 := by
          have : Nat.choose 5 2 ≤ Nat.choose (d₂ + 1) 2 :=
            choose_two_mono (by omega)
          omega
  · by_cases h4b : d₂ = 4
    · -- d₁ ≠ 4, d₂ = 4, d₁ ≤ 4 → d₁ ≤ 3
      subst h4b
      rw [hopt d₁ h4a (by omega), minEdges_dim4]
      have hd1_le : d₁ ≤ 3 := by omega
      have h1 : Nat.choose (d₁ + 1) 2 ≤ Nat.choose 4 2 := choose_two_mono (by omega)
      have h2 : Nat.choose 4 2 = 6 := by native_decide
      omega
    · -- Neither is 4
      rw [hopt d₁ h4a (by omega), hopt d₂ h4b (by omega)]
      exact choose_succ_two_mono hle

/-- Helper: C(d+1, 2) as a real number equals (d+1)*d/2. -/
private theorem choose_succ_two_real (d : ℕ) :
    (Nat.choose (d + 1) 2 : ℝ) = ((d : ℝ) + 1) * (d : ℝ) / 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  have hdvd : 2 ∣ (d + 1) * d := by
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
    · exact ⟨(2 * k + 1) * k, by ring⟩
    · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
  rw [Nat.cast_div hdvd (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast; ring

/-- The complete graph optimality conjecture implies quadratic growth.
    If K_{d+1} is optimal for all d ≠ 4, then minEdges(d) = Θ(d²)
    with constants c₁ = 1/2, c₂ = 1.
    - Lower: d²/2 ≤ d(d+1)/2 since d ≤ d+1. For d=4: 8 ≤ 9.
    - Upper: d(d+1)/2 ≤ d² since d+1 ≤ 2d for d ≥ 1. For d=4: 9 ≤ 16. -/
theorem optimal_implies_quadratic :
    complete_graph_optimal_conjecture → minEdges_quadratic_conjecture := by
  intro hopt
  refine ⟨1/2, 1, by norm_num, by norm_num, fun d hd => ?_⟩
  by_cases hd4 : d = 4
  · -- d = 4: minEdges(4) = 9, need 8 ≤ 9 and 9 ≤ 16
    subst hd4
    simp only [minEdges_dim4]
    constructor <;> norm_num
  · -- d ≠ 4: minEdges(d) = C(d+1,2) = d(d+1)/2
    rw [hopt d hd4 hd]
    rw [choose_succ_two_real]
    constructor
    · -- 1/2 * d² ≤ (d+1)*d/2, i.e., d² ≤ (d+1)*d = d²+d
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
      nlinarith
    · -- (d+1)*d/2 ≤ 1 * d², i.e., (d+1)*d ≤ 2*d², i.e., d+1 ≤ 2*d
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
      have hd_ge : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith

-- ============================================================================
-- § 9. Growth Rate Analysis
-- ============================================================================

/-- The ratio minEdges(d)/d for known values shows the growth rate.
    d=1: 1/1 = 1, d=2: 3/2 = 1.5, d=3: 6/3 = 2, d=4: 9/4 = 2.25, d=5: 15/5 = 3.
    The ratio itself grows roughly linearly, consistent with Θ(d²). -/
theorem growth_rate_d1 : minEdgesForDim 1 / 1 = 1 := by rw [minEdges_dim1]
theorem growth_rate_d3 : minEdgesForDim 3 / 3 = 2 := by rw [minEdges_dim3]
theorem growth_rate_d5 : minEdgesForDim 5 / 5 = 3 := by rw [minEdges_dim5]

/-- The successive differences: Δ(d) = minEdges(d+1) - minEdges(d)
    d=1→2: 2, d=2→3: 3, d=3→4: 3, d=4→5: 6.
    For d ≠ 3→4, the differences equal d+1 (matching C(d+2,2) - C(d+1,2)). -/
theorem diff_1_to_2 : minEdgesForDim 2 - minEdgesForDim 1 = 2 := by
  rw [minEdges_dim1, minEdges_dim2]
theorem diff_2_to_3 : minEdgesForDim 3 - minEdgesForDim 2 = 3 := by
  rw [minEdges_dim2, minEdges_dim3]
theorem diff_3_to_4 : minEdgesForDim 4 - minEdgesForDim 3 = 3 := by
  rw [minEdges_dim3, minEdges_dim4]
theorem diff_4_to_5 : minEdgesForDim 5 - minEdgesForDim 4 = 6 := by
  rw [minEdges_dim4, minEdges_dim5]

/-- The d=3→4 difference is anomalous: it equals 3 instead of 4.
    This is precisely the d=4 "surprise" where K_{3,3} beats K₅. -/
theorem diff_anomaly :
    minEdgesForDim 4 - minEdgesForDim 3 < (3 + 1) := by
  rw [minEdges_dim3, minEdges_dim4]; norm_num

/-- Under the complete graph conjecture, the successive differences are exactly d+1.
    C(d+2, 2) - C(d+1, 2) = (d+1)(d)/2 + (d+1) - (d+1)(d)/2 = d+1. -/
theorem optimal_diff (hopt : complete_graph_optimal_conjecture) (d : ℕ) (hd : 1 ≤ d)
    (hd4 : d ≠ 4) (hd4' : d + 1 ≠ 4) :
    minEdgesForDim (d + 1) - minEdgesForDim d = d + 1 := by
  rw [hopt (d + 1) hd4' (by omega), hopt d hd4 hd]
  simp only [Nat.choose_two_right, Nat.add_sub_cancel]
  -- Goal: (d + 1 + 1) * (d + 1) / 2 - (d + 1) * d / 2 = d + 1
  have h1 : (d + 1 + 1) * (d + 1) = (d + 1) * d + 2 * (d + 1) := by ring
  have h2 : 2 ∣ (d + 1) * d := by
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
    · exact ⟨(2 * k + 1) * k, by ring⟩
    · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
  rw [h1, Nat.add_div_of_dvd_right h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

-- ============================================================================
-- § 10. Deficiency Function
-- ============================================================================

-- The "deficiency" δ(d) = C(d+1,2) - minEdges(d) measures how much the
-- optimal graph beats K_{d+1}. Known: δ(d) = 0 for d ≤ 3 and d = 5, δ(4) = 1.

/-- The deficiency: how many edges K_{d+1} "wastes" compared to optimal. -/
noncomputable def deficiency (d : ℕ) : ℕ := Nat.choose (d + 1) 2 - minEdgesForDim d

theorem deficiency_dim1 : deficiency 1 = 0 := by
  simp [deficiency, minEdges_dim1]
theorem deficiency_dim2 : deficiency 2 = 0 := by
  simp [deficiency, minEdges_dim2]
theorem deficiency_dim3 : deficiency 3 = 0 := by
  simp [deficiency, minEdges_dim3]; native_decide
theorem deficiency_dim4 : deficiency 4 = 1 := by
  simp [deficiency, minEdges_dim4]; native_decide
theorem deficiency_dim5 : deficiency 5 = 0 := by
  simp [deficiency, minEdges_dim5]; native_decide

/-- The complete graph optimality conjecture is equivalent to deficiency = 0 for d ≠ 4. -/
theorem optimal_iff_zero_deficiency :
    complete_graph_optimal_conjecture ↔
    ∀ d : ℕ, d ≠ 4 → 1 ≤ d → deficiency d = 0 := by
  constructor
  · intro hopt d hd4 hd1
    simp [deficiency, hopt d hd4 hd1]
  · intro hdef d hd4 hd1
    have hub := minEdges_upper_bound d (by omega)
    have hdef0 := hdef d hd4 hd1
    simp [deficiency] at hdef0
    omega

/-- d=4 is the unique known anomaly in the first 5 dimensions. -/
theorem unique_anomaly_small :
    ∀ d : ℕ, 1 ≤ d → d ≤ 5 → deficiency d ≠ 0 → d = 4 := by
  intro d hd1 hd5 hdef
  interval_cases d <;> simp_all [deficiency_dim1, deficiency_dim2, deficiency_dim3,
    deficiency_dim4, deficiency_dim5]

#check @complete_graph_unit_embedding
#check @complete_graph_dim_le
#check @subgraph_unit_embedding
#check @hasUnitEmbedding_exists_irrefl
#check @optimal_implies_monotone
#check @optimal_implies_quadratic
#check @optimal_iff_zero_deficiency
#check @unique_anomaly_small
