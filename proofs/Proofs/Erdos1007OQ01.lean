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
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

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

axiom hasUnitEmbedding_exists' (V : Type*) [Fintype V] (adj : V → V → Prop) :
  ∃ n, hasUnitEmbedding' V adj n

open Classical in
noncomputable def graphDimension' (V : Type*) [Fintype V] (adj : V → V → Prop) : ℕ :=
  Nat.find (hasUnitEmbedding_exists' V adj)

-- ============================================================================
-- § 2. Minimum Edge Function
-- ============================================================================

/-- minEdges(d) is the minimum number of edges among all graphs with dimension d.
    We axiomatize this as extracting the minimum requires a search over all graphs. -/
axiom minEdgesForDim : ℕ → ℕ

/-- Every graph of dimension d has at least minEdges(d) edges. -/
axiom minEdgesForDim_le (d : ℕ) (V : Type) [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj] :
    graphDimension' V adj = d →
    minEdgesForDim d ≤ (Finset.univ.filter (fun p : V × V => adj p.1 p.2)).card

/-- There exists a graph achieving the minimum. -/
axiom minEdgesForDim_achieved (d : ℕ) (hd : 0 < d) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (adj : V → V → Prop) (_ : DecidableRel adj),
      graphDimension' V adj = d ∧
      (Finset.univ.filter (fun p : V × V => adj p.1 p.2)).card = minEdgesForDim d

-- ============================================================================
-- § 3. Known Values
-- ============================================================================

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

#check @small_dim_complete
#check @dim4_beats_complete
#check @dim5_matches_complete
#check @upper_bound_quadratic
#check @lower_bound_linear
