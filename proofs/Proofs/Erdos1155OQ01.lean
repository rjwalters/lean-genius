/-
Erdős Problem #1155 OQ-01: Triangle Removal Process — Exact Asymptotics

Extension of Erdos1155Problem.lean focusing on:
1. Proving the parent file's sorries (triangleFree_iff_cliqueFree3, complete_has_triangles)
2. Formalizing the gap between BFL n^{3/2+o(1)} and the conjectured Θ(n^{3/2})
3. Proving structural lemmas about the asymptotic characterization

The main open question: Does E[f(n)] ≍ n^{3/2} hold with explicit constants?
BFL (2015) showed f(n) = n^{3/2+o(1)} a.s., but the conjecture asks for
c₁·n^{3/2} ≤ f(n) ≤ c₂·n^{3/2} with fixed constants c₁, c₂ > 0.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter SimpleGraph Finset

-- ============================================================================
-- § 1. Triangle definitions and equivalences
-- ============================================================================

/-- A triangle in a graph: three distinct mutually adjacent vertices. -/
def IsTriangle' {V : Type*} (G : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- A graph is triangle-free if it contains no triangles. -/
def IsTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, ¬IsTriangle' G a b c

/-- Triangle-free ↔ CliqueFree 3 for simple graphs.
    Forward: if no pointwise triangle, then no 3-element clique.
    Backward: if no 3-clique, then no pointwise triangle. -/
theorem triangleFree_iff_cliqueFree3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : IsTriangleFree G ↔ G.CliqueFree 3 := by
  constructor
  · -- IsTriangleFree → CliqueFree 3
    intro htf s hs
    -- A 3-clique s gives three distinct pairwise-adjacent vertices
    -- which contradicts triangle-freeness
    sorry
  · -- CliqueFree 3 → IsTriangleFree
    intro hcf a b c ⟨hab, hbc, hac, hadj_ab, hadj_bc, hadj_ac⟩
    -- {a, b, c} is a 3-clique, contradicting CliqueFree 3
    sorry

/-- The complete graph on n ≥ 3 vertices contains a triangle. -/
theorem complete_has_triangles' {n : ℕ} (hn : 3 ≤ n) :
    ¬IsTriangleFree (⊤ : SimpleGraph (Fin n)) := by
  intro h
  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  let v2 : Fin n := ⟨2, by omega⟩
  have h01 : v0 ≠ v1 := by intro heq; simp [v0, v1] at heq
  have h12 : v1 ≠ v2 := by intro heq; simp [v1, v2] at heq
  have h02 : v0 ≠ v2 := by intro heq; simp [v0, v2] at heq
  have adj01 : (⊤ : SimpleGraph (Fin n)).Adj v0 v1 := by
    simp only [SimpleGraph.top_adj]; exact h01
  have adj12 : (⊤ : SimpleGraph (Fin n)).Adj v1 v2 := by
    simp only [SimpleGraph.top_adj]; exact h12
  have adj02 : (⊤ : SimpleGraph (Fin n)).Adj v0 v2 := by
    simp only [SimpleGraph.top_adj]; exact h02
  exact h v0 v1 v2 ⟨h01, h12, h02, adj01, adj12, adj02⟩

-- ============================================================================
-- § 2. Asymptotic infrastructure
-- ============================================================================

-- Import the axiomatized function from the parent file
axiom triangleRemovalEdges : ℕ → ℝ
axiom triangleRemovalEdges_nonneg (n : ℕ) : 0 ≤ triangleRemovalEdges n
axiom triangleRemovalEdges_le_complete (n : ℕ) :
    triangleRemovalEdges n ≤ (n * (n - 1) : ℝ) / 2

axiom bfl_upper_bound :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε)

axiom bfl_lower_bound :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ ((3 : ℝ) / 2 - ε) ≤ triangleRemovalEdges n

/-- The Erdős conjecture: f(n) = Θ(n^{3/2}) with explicit constants. -/
def erdos_1155_conjecture : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    ∀ᶠ (n : ℕ) in atTop,
      c₁ * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ triangleRemovalEdges n ∧
      triangleRemovalEdges n ≤ c₂ * (n : ℝ) ^ ((3 : ℝ) / 2)

-- ============================================================================
-- § 3. OQ-01: Gap analysis — what separates BFL from the full conjecture
-- ============================================================================

/-- The BFL result in "sandwich" form: for any ε > 0, eventually
    n^{3/2-ε} ≤ f(n) ≤ n^{3/2+ε}. -/
theorem bfl_sandwich :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ ((3 : ℝ) / 2 - ε) ≤ triangleRemovalEdges n ∧
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε) := by
  intro ε hε
  exact (bfl_lower_bound ε hε).and (bfl_upper_bound ε hε)

/-- The conjecture implies the BFL upper bound (conjecture is strictly stronger). -/
theorem conjecture_implies_bfl_upper :
    erdos_1155_conjecture →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε) := by
  intro ⟨c₁, c₂, _, _, hconj⟩ ε hε
  -- For large n, c₂ · n^{3/2} ≤ n^{3/2+ε} since n^ε → ∞
  -- We need: c₂ · n^{3/2} ≤ n^{3/2+ε}, i.e., c₂ ≤ n^ε
  -- This holds eventually since n^ε → ∞ and c₂ is a constant
  sorry

/-- The conjecture implies the BFL lower bound (conjecture is strictly stronger). -/
theorem conjecture_implies_bfl_lower :
    erdos_1155_conjecture →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ ((3 : ℝ) / 2 - ε) ≤ triangleRemovalEdges n := by
  intro ⟨c₁, c₂, hc₁, _, hconj⟩ ε hε
  -- For large n, n^{3/2-ε} ≤ c₁ · n^{3/2} since c₁ · n^ε ≥ 1 eventually
  sorry

/-- A weaker form of the conjecture: there exists C such that
    f(n) ≤ C · n^{3/2} eventually. This is the upper Θ-bound. -/
def upper_theta_bound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ (n : ℕ) in atTop,
      triangleRemovalEdges n ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2)

/-- A weaker form of the conjecture: there exists c such that
    c · n^{3/2} ≤ f(n) eventually. This is the lower Θ-bound. -/
def lower_theta_bound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ (n : ℕ) in atTop,
      c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ triangleRemovalEdges n

/-- The full conjecture is equivalent to both one-sided Θ-bounds holding. -/
theorem conjecture_iff_both_bounds :
    erdos_1155_conjecture ↔ (upper_theta_bound ∧ lower_theta_bound) := by
  constructor
  · intro ⟨c₁, c₂, hc₁, hc₁c₂, h⟩
    exact ⟨⟨c₂, lt_of_lt_of_le hc₁ hc₁c₂, h.mono fun n hn => hn.2⟩,
           ⟨c₁, hc₁, h.mono fun n hn => hn.1⟩⟩
  · intro ⟨⟨C, hC, hup⟩, ⟨c, hc, hlo⟩⟩
    exact ⟨c, C, hc, by
      by_contra h
      push_neg at h
      -- If c > C, then we have c·n^{3/2} ≤ f(n) ≤ C·n^{3/2} eventually
      -- but c > C means c·n^{3/2} > C·n^{3/2} for large n, contradiction
      sorry,
      hlo.and hup⟩

-- ============================================================================
-- § 4. Exponent gap characterization
-- ============================================================================

/-- The BFL exponent is exactly 3/2 (not a weaker bound like 7/4).
    This is a consequence of the two-sided BFL result. -/
theorem bfl_exponent_is_three_halves :
    ∀ α : ℝ, α > 3/2 →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ α := by
  intro α hα
  have hε : (0 : ℝ) < α - 3/2 := by linarith
  have := bfl_upper_bound (α - 3/2) hε
  apply this.mono
  intro n hn
  have : (3 : ℝ) / 2 + (α - 3 / 2) = α := by ring
  rw [this] at hn
  exact hn

/-- The BFL result is tight from below: no exponent below 3/2 works. -/
theorem bfl_lower_tight :
    ∀ β : ℝ, β < 3/2 →
      ¬ (∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ β) := by
  intro β hβ hcontra
  have hε : (0 : ℝ) < 3/2 - β := by linarith
  have hlo := bfl_lower_bound ((3/2 - β) / 2) (by linarith)
  -- Eventually n^{3/2 - ε} ≤ f(n) ≤ n^β where 3/2 - ε > β, contradiction
  sorry

-- ============================================================================
-- § 5. Monotonicity and basic structural results
-- ============================================================================

/-- For small n, f(n) = 0 since K_n has no triangles (n < 3) or
    removing the unique triangle in K_3 leaves 0 edges. -/
theorem f_small_values_bound :
    triangleRemovalEdges 0 ≤ 0 ∧
    triangleRemovalEdges 1 ≤ 0 ∧
    triangleRemovalEdges 2 ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · -- K_0 has 0 edges
    have := triangleRemovalEdges_le_complete 0
    simp at this
    exact this
  · -- K_1 has 0 edges
    have := triangleRemovalEdges_le_complete 1
    simp at this
    exact this
  · -- K_2 has 1 edge, so f(2) ≤ 1
    have := triangleRemovalEdges_le_complete 2
    norm_num at this
    linarith

/-- The BFL result gives a concrete exponent separation:
    for any ε, the ratio f(n)/n^{3/2} is eventually in [n^{-ε}, n^ε]. -/
theorem bfl_ratio_characterization :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ (-ε) ≤ triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2) ∧
        triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2) ≤ (n : ℝ) ^ ε := by
  intro ε hε
  -- This follows from BFL sandwich after dividing by n^{3/2}
  -- n^{3/2-ε} / n^{3/2} = n^{-ε} and n^{3/2+ε} / n^{3/2} = n^ε
  sorry

-- ============================================================================
-- § 6. What would resolve the conjecture
-- ============================================================================

/-- Key sufficient condition: if the ratio f(n)/n^{3/2} converges to some
    limit L > 0, then the full conjecture holds. -/
theorem limit_implies_conjecture :
    (∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun n : ℕ => triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2))
        atTop (nhds L)) →
    erdos_1155_conjecture := by
  intro ⟨L, hL, htends⟩
  -- If f(n)/n^{3/2} → L, then for ε = L/2, eventually L/2 ≤ f(n)/n^{3/2} ≤ 3L/2
  -- So (L/2)·n^{3/2} ≤ f(n) ≤ (3L/2)·n^{3/2}
  sorry

/-- Even a limsup/liminf condition suffices: if both are finite and positive. -/
def limsup_liminf_condition : Prop :=
  (∃ C : ℝ, 0 < C ∧
    ∀ᶠ (n : ℕ) in atTop, triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2) ≤ C) ∧
  (∃ c : ℝ, 0 < c ∧
    ∀ᶠ (n : ℕ) in atTop, c ≤ triangleRemovalEdges n / (n : ℝ) ^ ((3:ℝ)/2))

theorem limsup_liminf_implies_conjecture :
    limsup_liminf_condition → erdos_1155_conjecture := by
  intro ⟨⟨C, hC, hup⟩, ⟨c, hc, hlo⟩⟩
  refine ⟨c, C, hc, ?_, ?_⟩
  · -- Need c ≤ C; this follows from the fact that eventually
    -- c ≤ f(n)/n^{3/2} ≤ C, so c ≤ C
    sorry
  · -- Eventually c·n^{3/2} ≤ f(n) ≤ C·n^{3/2}
    -- follows from dividing the ratio bounds by n^{3/2}
    sorry

#check @bfl_sandwich
#check @conjecture_iff_both_bounds
#check @bfl_exponent_is_three_halves
#check @limit_implies_conjecture
