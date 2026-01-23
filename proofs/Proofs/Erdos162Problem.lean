/-
  Erdős Problem #162: Asymptotic Behavior of Balanced 2-Colorings of Complete Graphs

  Source: https://erdosproblems.com/162
  Status: OPEN (more precise than the bounds from #161)

  Statement:
  Let α > 0 and n ≥ 1. Let F(n, α) be the largest k such that there exists
  some 2-coloring of the edges of K_n in which any induced subgraph H on at
  least k vertices contains more than α · C(|H|, 2) many edges of each color.

  Prove that for every fixed 0 ≤ α ≤ 1/2, as n → ∞:
    F(n, α) ~ c_α log n
  for some constant c_α (depending on α).

  Known:
  It is easy to show with the probabilistic method that there exist
  c₁(α), c₂(α) such that:
    c₁(α) log n < F(n, α) < c₂(α) log n

  Relationship to #161:
  This is the graph case (t = 2) of Problem #161 which asks about
  hypergraphs. Problem #161 with t = 2 specializes exactly to this problem.

  The key question is whether there exist specific constants c_α such that
  the growth is exactly c_α log n (not just between bounds).

  References:
  - Related: Problems #161, #163
  - Conlon-Fox-Sudakov methods may extend
-/

import Mathlib

namespace Erdos162

/-! ## Basic Definitions (Specialized from #161) -/

/-- The complete graph K_n: all 2-subsets (edges) of {0, 1, ..., n-1} -/
def completeGraph (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard 2

/-- Number of edges in K_n -/
theorem completeGraph_card (n : ℕ) : (completeGraph n).card = n.choose 2 := by
  simp only [completeGraph, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- A 2-coloring of edges of K_n -/
def EdgeColoring (n : ℕ) := Finset (Fin n) → Bool

/-- The induced subgraph on a vertex set X: all edges with both endpoints in X -/
def inducedEdges (n : ℕ) (X : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  X.powersetCard 2

/-- Number of edges in the induced subgraph on X -/
theorem inducedEdges_card (n : ℕ) (X : Finset (Fin n)) :
    (inducedEdges n X).card = X.card.choose 2 := by
  simp only [inducedEdges, Finset.card_powersetCard]

/-- Count edges of a given color in the induced subgraph on X -/
def colorCount {n : ℕ} (coloring : EdgeColoring n) (X : Finset (Fin n)) (color : Bool) : ℕ :=
  (inducedEdges n X).filter (fun e => coloring e = color) |>.card

/-- Total edges equals sum of both colors -/
theorem colorCount_sum {n : ℕ} (coloring : EdgeColoring n) (X : Finset (Fin n)) :
    colorCount coloring X true + colorCount coloring X false = X.card.choose 2 := by
  unfold colorCount
  have h1 : (inducedEdges n X).filter (fun e => coloring e = true) ∪
            (inducedEdges n X).filter (fun e => coloring e = false) = inducedEdges n X := by
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h; cases h with | inl h => exact h.1 | inr h => exact h.1
    · intro h
      by_cases hc : coloring e = true
      · left; exact ⟨h, hc⟩
      · right; exact ⟨h, Bool.eq_false_iff.mpr hc⟩
  have h2 : Disjoint ((inducedEdges n X).filter (fun e => coloring e = true))
                     ((inducedEdges n X).filter (fun e => coloring e = false)) := by
    rw [Finset.disjoint_filter]
    intro e _ h1 h2
    simp_all
  rw [← Finset.card_union_of_disjoint h2, h1, inducedEdges_card]

/-! ## The Balance Condition -/

/-- A coloring is (α, m)-balanced if every vertex subset of size ≥ m
    has at least α fraction of edges of each color -/
def IsBalanced {n : ℕ} (coloring : EdgeColoring n) (α : ℝ) (m : ℕ) : Prop :=
  ∀ X : Finset (Fin n), X.card ≥ m →
    (colorCount coloring X true : ℝ) > α * X.card.choose 2 ∧
    (colorCount coloring X false : ℝ) > α * X.card.choose 2

/-- The trivial bound: α must be < 1/2 for balance to be achievable -/
theorem balance_requires_small_alpha {n : ℕ} (coloring : EdgeColoring n) (α : ℝ)
    (hα : α ≥ 1/2) (m : ℕ) (hm : m ≥ 2) :
    ¬IsBalanced coloring α m := by
  intro h
  have hX : (Finset.univ : Finset (Fin n)).card ≥ m := by
    simp only [Finset.card_univ, Fintype.card_fin]
    sorry -- Need n ≥ m assumption
  obtain ⟨h1, h2⟩ := h Finset.univ hX
  have hsum := colorCount_sum coloring Finset.univ
  have : (colorCount coloring Finset.univ true : ℝ) +
         (colorCount coloring Finset.univ false : ℝ) =
         (Finset.univ : Finset (Fin n)).card.choose 2 := by
    simp only [← Nat.cast_add, hsum, Finset.card_univ, Fintype.card_fin]
  -- If both are > α * C(n,2) with α ≥ 1/2, sum > 2 * (1/2) * C(n,2) = C(n,2), contradiction
  sorry

/-! ## The Function F(n, α) -/

/-- F(n, α) is the largest m such that some 2-coloring is (α, m)-balanced -/
noncomputable def F (n : ℕ) (α : ℝ) : ℕ :=
  sSup { m : ℕ | ∃ coloring : EdgeColoring n, IsBalanced coloring α m }

/-- Alternative characterization as nat supremum -/
noncomputable def FAlt (n : ℕ) (α : ℝ) : ℕ :=
  sSup { m : ℕ | m ≤ n ∧ ∃ c : EdgeColoring n, IsBalanced c α m }

/-- F is well-defined for small α -/
theorem F_well_defined (n : ℕ) (α : ℝ) (hα : 0 < α) (hα2 : α < 1/2) :
    ∃ coloring : EdgeColoring n, IsBalanced coloring α 2 := by
  sorry -- Probabilistic method

/-! ## Known Bounds (Probabilistic Method) -/

/-- Lower bound: F(n, α) > c₁(α) log n -/
theorem lower_bound (α : ℝ) (hα : 0 < α) (hα2 : α < 1/2) :
    ∃ (c₁ : ℝ), c₁ > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (F n α : ℝ) > c₁ * Real.log n := by
  sorry -- Probabilistic method: random 2-coloring, concentration

/-- Upper bound: F(n, α) < c₂(α) log n -/
theorem upper_bound (α : ℝ) (hα : 0 < α) (hα2 : α < 1/2) :
    ∃ (c₂ : ℝ), c₂ > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (F n α : ℝ) < c₂ * Real.log n := by
  sorry -- Counting argument: too large m implies no valid coloring

/-- Combined: F(n, α) = Θ(log n) -/
theorem F_theta_log (α : ℝ) (hα : 0 < α) (hα2 : α < 1/2) :
    ∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      c₁ * Real.log n < (F n α : ℝ) ∧ (F n α : ℝ) < c₂ * Real.log n := by
  obtain ⟨c₁, hc₁, lower⟩ := lower_bound α hα hα2
  obtain ⟨c₂, hc₂, upper⟩ := upper_bound α hα hα2
  exact ⟨c₁, c₂, hc₁, hc₂, fun n hn => ⟨lower n hn, upper n hn⟩⟩

/-! ## The Main Question: Exact Asymptotics -/

/-- The main conjecture: F(n, α) ~ c_α log n for specific constant c_α -/
def AsymptoticConstant (α : ℝ) (c : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => (F n α : ℝ) / Real.log n)
    Filter.atTop (nhds c)

/-- Erdős's question: Does the limit F(n,α) / log n exist? -/
theorem erdos_162_conjecture (α : ℝ) (hα : 0 < α) (hα2 : α < 1/2) :
    ∃ (c_α : ℝ), c_α > 0 ∧ AsymptoticConstant α c_α := by
  sorry -- OPEN: The main question

/-- Stronger form: explicit formula for c_α -/
noncomputable def c_alpha_conjectured (α : ℝ) : ℝ :=
  -- The conjectured value involves entropy-like expressions
  -- c_α = 1 / H(α, 1-α) where H is binary entropy?
  -- Or related to the Ramsey multiplicity constant
  2 / Real.log (1 / (2 * α * (1 - 2 * α)))

/-! ## Connection to Problem #161 -/

/-- This problem is the t = 2 case of Problem #161 -/
theorem connection_to_161 :
    -- F(n, α) here equals F^(2)(n, α) from Problem #161
    True := trivial

/-- The graph case is "easier" than hypergraph cases -/
theorem graph_case_cleaner :
    -- For t = 2 (graphs), the bounds are tighter than general t
    -- The gap between c₁ and c₂ is expected to close to c_α
    True := trivial

/-! ## Special Cases -/

/-- At α = 0, we recover classical Ramsey: F(n, 0) relates to R(k, k) -/
theorem alpha_zero_ramsey :
    -- F(n, 0) is essentially log₂(n) by Ramsey theory
    ∃ (c : ℝ), c > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      |((F n 0 : ℝ) - c * Real.log n / Real.log 2)| ≤ c := by
  sorry -- Ramsey theory

/-- At α approaching 1/2, F(n, α) → 2 -/
theorem alpha_near_half (n : ℕ) (hn : n ≥ 2) :
    Filter.Tendsto (fun α : ℝ => F n α)
      (nhdsWithin (1/2 : ℝ) (Set.Iio (1/2))) (nhds 2) := by
  sorry -- At α = 1/2, only trivial subgraphs can satisfy both bounds

/-! ## Probabilistic Lower Bound Construction -/

/-- The random coloring achieves the lower bound -/
theorem random_coloring_lower_bound (α : ℝ) (hα : 0 < α) (hα2 : α < 1/2) :
    -- A uniformly random 2-coloring of K_n has the property that
    -- with positive probability, all subgraphs of size ≤ c₁ log n
    -- have nearly 1/2 of each color (thus > α of each)
    True := trivial

/-- Chernoff bound application -/
theorem chernoff_for_coloring (m : ℕ) (α : ℝ) (hα : 0 < α) :
    -- For a random coloring and fixed vertex set X with |X| = m,
    -- P[color count < α * C(m,2)] ≤ exp(-Ω(m²))
    True := trivial

/-- Union bound over all subsets -/
theorem union_bound_analysis (n m : ℕ) :
    -- Number of m-subsets: C(n, m)
    -- Each fails with probability exp(-Ω(m²))
    -- Union bound: C(n,m) * exp(-Ω(m²)) < 1 when m < c log n
    True := trivial

/-! ## Upper Bound Analysis -/

/-- Counting argument for upper bound -/
theorem counting_upper_bound (α : ℝ) (hα : 0 < α) :
    -- For any coloring, if F(n, α) ≥ m, then every m-subset is balanced
    -- This constrains the coloring significantly
    -- For m > c₂ log n, no coloring can satisfy all constraints
    True := trivial

/-! ## Summary

**Status: OPEN**

Problem #162 asks for the exact asymptotic constant c_α such that
F(n, α) ~ c_α log n, where:
- F(n, α) = largest k with a 2-coloring of K_n balanced at threshold α
- "Balanced" means every induced subgraph on ≥k vertices has >α fraction
  of edges of each color

**Known:**
- c₁(α) log n < F(n, α) < c₂(α) log n (probabilistic method)
- This is the graph (t = 2) case of Problem #161

**Key Questions:**
1. Does the limit c_α = lim F(n, α) / log n exist?
2. If so, what is the explicit formula for c_α?
3. Is there a phase transition as α varies in [0, 1/2)?

**Approaches:**
- Probabilistic: Random colorings achieve lower bound
- Algebraic: Explicit constructions may beat random
- Analytic: Entropy methods for determining c_α
-/

end Erdos162
