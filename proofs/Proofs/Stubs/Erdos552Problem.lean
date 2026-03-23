/-
  Erdős Problem #552: Ramsey Number R(C₄, Sₙ)

  Source: https://erdosproblems.com/552
  Status: OPEN
  Prize: $100

  Statement:
  Determine the Ramsey number R(C₄, Sₙ), where Sₙ = K_{1,n} is the star on n+1
  vertices. In particular, is it true that for any c > 0, there are infinitely
  many n such that R(C₄, Sₙ) ≤ n + √n - c?

  Known Bounds:
  - Lower: n + √n - 6n^{11/40} (Burr-Erdős-Faudree-Rousseau-Schelp 1989)
  - Upper: n + ⌈√n⌉ + 1 (Parsons 1975)

  Exact Values:
  - n = q² + 1 (q prime power): R(C₄, Sₙ) = n + ⌈√n⌉
  - n = q² (q prime power): R(C₄, Sₙ) = n + ⌈√n⌉ + 1

  Connection to prime gaps: Under Cramér's conjecture, lower bound improves to
  n + √n - n^{o(1)}.

  Tags: graph-theory, ramsey-theory, combinatorics
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Erdos552

open SimpleGraph Finset

/- ## Part I: Graph Definitions -/

/-- The cycle graph C_n on n vertices. -/
def cycleGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj := fun i j => (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val
  symm := by intro i j h; cases h <;> (right; assumption) <|> (left; assumption)
  loopless := by
    intro i h
    cases h with
    | inl h => simp at h; omega
    | inr h => simp at h; omega

/-- The 4-cycle C₄. -/
def C4 : SimpleGraph (Fin 4) := cycleGraph 4

/-- The star graph S_n = K_{1,n} on n+1 vertices (center + n leaves). -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj := fun i j => (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
  symm := by intro i j h; cases h <;> (right; exact ⟨‹_›.1, ‹_›.2⟩) <|> (left; exact ⟨‹_›.1, ‹_›.2⟩)
  loopless := by intro i h; cases h <;> omega

/- ## Part II: Ramsey Numbers -/

/-- A graph G contains H as a subgraph. -/
def ContainsSubgraph {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ u v : W, H.Adj u v → G.Adj (f u) (f v)

/-- The complement of a graph. -/
def complement {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj := fun u v => u ≠ v ∧ ¬G.Adj u v
  symm := by intro u v ⟨hne, hadj⟩; exact ⟨hne.symm, fun h => hadj (G.symm h)⟩
  loopless := by intro v ⟨hne, _⟩; exact hne rfl

/-- R(H₁, H₂) = minimum N such that every 2-coloring of K_N contains
    monochromatic H₁ (color 1) or monochromatic H₂ (color 2). -/
noncomputable def ramseyNumber {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (H₁ : SimpleGraph V₁) (H₂ : SimpleGraph V₂) : ℕ :=
  sInf {N : ℕ | ∀ G : SimpleGraph (Fin N),
    ContainsSubgraph G H₁ ∨ ContainsSubgraph (complement G) H₂}

/-- R(C₄, Sₙ) is the specific Ramsey number of interest. -/
noncomputable def R_C4_Sn (n : ℕ) : ℕ :=
  ramseyNumber C4 (starGraph n)

/- ## Part III: Known Bounds -/

/-- Parsons (1975) upper bound: R(C₄, Sₙ) ≤ n + ⌈√n⌉ + 1. -/
theorem parsons_upper_bound (n : ℕ) (hn : n ≥ 1) :
    R_C4_Sn n ≤ n + Nat.ceil (Real.sqrt n) + 1 := by
  sorry

/-- Burr-Erdős-Faudree-Rousseau-Schelp (1989) lower bound:
    R(C₄, Sₙ) ≥ n + √n - 6n^{11/40}. -/
theorem befrs_lower_bound :
    ∀ᶠ n in Filter.atTop,
      (R_C4_Sn n : ℝ) ≥ n + Real.sqrt n - 6 * (n : ℝ) ^ (11/40 : ℝ) := by
  sorry

/-- Combining bounds: R(C₄, Sₙ) = n + √n + O(n^{11/40}). -/
theorem asymptotic_bounds :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ n in Filter.atTop,
      |((R_C4_Sn n : ℝ) - n - Real.sqrt n)| ≤ C * (n : ℝ) ^ (11/40 : ℝ) := by
  sorry

/- ## Part IV: Exact Values for Special n -/

/-- For n = q² + 1 where q is a prime power: R(C₄, Sₙ) = n + ⌈√n⌉. -/
theorem exact_value_q2_plus_1 (q : ℕ) (hq : Nat.Prime q ∨ ∃ p k, Nat.Prime p ∧ q = p ^ k) :
    R_C4_Sn (q ^ 2 + 1) = q ^ 2 + 1 + q := by
  sorry

/-- For n = q² where q is a prime power: R(C₄, Sₙ) = n + ⌈√n⌉ + 1. -/
theorem exact_value_q2 (q : ℕ) (hq : Nat.Prime q ∨ ∃ p k, Nat.Prime p ∧ q = p ^ k) :
    R_C4_Sn (q ^ 2) = q ^ 2 + q + 1 := by
  sorry

/-- For n = q² - t where 0 ≤ t ≤ q: explicit formula. -/
theorem exact_value_q2_minus_t (q t : ℕ) (ht : t ≤ q)
    (hq : Nat.Prime q ∨ ∃ p k, Nat.Prime p ∧ q = p ^ k) :
    R_C4_Sn (q ^ 2 - t) = q ^ 2 - t + q + 1 := by
  sorry

/- ## Part V: The Main Question -/

/-- The Erdős question: For any c > 0, are there infinitely many n with
    R(C₄, Sₙ) ≤ n + √n - c? -/
def ErdosQuestion (c : ℝ) : Prop :=
  {n : ℕ | (R_C4_Sn n : ℝ) ≤ n + Real.sqrt n - c}.Infinite

/-- The full conjecture: This holds for ALL c > 0. -/
def ErdosConjecture : Prop :=
  ∀ c : ℝ, c > 0 → ErdosQuestion c

/-- The negation: There exists c > 0 such that eventually R(C₄, Sₙ) > n + √n - c. -/
def ErdosConjectureNegation : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in Filter.atTop, (R_C4_Sn n : ℝ) > n + Real.sqrt n - c

/- ## Part VI: Connection to Prime Gaps -/

/-- The prime gap after p. -/
noncomputable def primeGap (p : ℕ) : ℕ :=
  if hp : Nat.Prime p then
    sInf {q : ℕ | Nat.Prime q ∧ q > p} - p
  else 0

/-- Cramér's conjecture: primeGap(p) = O((log p)²). -/
def CramerConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ p : ℕ, Nat.Prime p →
    (primeGap p : ℝ) ≤ C * (Real.log p) ^ 2

/-- Under Cramér's conjecture, the lower bound improves. -/
theorem cramer_implies_better_bound (hC : CramerConjecture) :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      (R_C4_Sn n : ℝ) ≥ n + Real.sqrt n - (n : ℝ) ^ ε := by
  sorry

/- ## Part VII: The Function f(n) -/

/-- Define f(n) = R(C₄, Sₙ) for convenience. -/
noncomputable def f : ℕ → ℕ := R_C4_Sn

/-- Question: Does f(n+1) = f(n) infinitely often? -/
def ConsecutiveEqualQuestion : Prop :=
  {n : ℕ | f (n + 1) = f n}.Infinite

/-- Question: Is f(n+1) ≤ f(n) + 2 always? -/
def BoundedIncreaseQuestion : Prop :=
  ∀ n : ℕ, f (n + 1) ≤ f n + 2

/-- Observation: f is eventually strictly increasing. -/
theorem f_eventually_increasing :
    ∀ᶠ n in Filter.atTop, f n < f (n + 1) := by
  sorry

/- ## Part VIII: Constructions -/

/-- The Parsons construction uses projective planes. -/
theorem parsons_construction (q : ℕ) (hq : Nat.Prime q) :
    ∃ G : SimpleGraph (Fin (q ^ 2 + q + 1)),
      ¬ContainsSubgraph G C4 ∧ ¬ContainsSubgraph (complement G) (starGraph (q ^ 2)) := by
  sorry

/-- The polarity graph of PG(2,q) achieves the lower bound. -/
def polarityGraph (q : ℕ) : SimpleGraph (Fin (q ^ 2 + q + 1)) := by
  sorry

/- ## Part IX: Related Results -/

/-- The minimum degree condition for C₄. -/
theorem c4_minimum_degree (n : ℕ) (G : SimpleGraph (Fin n)) (hn : n ≥ 4) :
    (∀ v : Fin n, G.degree v ≥ n / 2) → ContainsSubgraph G C4 := by
  sorry

/-- For general stars: R(C₄, K_{1,n}) relates to extremal graph theory. -/
theorem c4_star_extremal (n : ℕ) :
    R_C4_Sn n ≤ n + 2 * Nat.sqrt n + 3 := by
  sorry

end Erdos552

/-
  ## Summary

  This file formalizes Erdős Problem #552 on the Ramsey number R(C₄, Sₙ).

  **Status**: OPEN
  **Prize**: $100

  **The Problem**: Determine R(C₄, Sₙ) where Sₙ = K_{1,n} is the star.
  In particular: for any c > 0, are there infinitely many n with
  R(C₄, Sₙ) ≤ n + √n - c?

  **Known Bounds**:
  - Lower: n + √n - 6n^{11/40} (Burr-Erdős-Faudree-Rousseau-Schelp 1989)
  - Upper: n + ⌈√n⌉ + 1 (Parsons 1975)
  - All known values are n + ⌈√n⌉ or n + ⌈√n⌉ + 1

  **Exact Values**:
  - n = q² + 1 (q prime power): R = n + ⌈√n⌉
  - n = q² (q prime power): R = n + ⌈√n⌉ + 1

  **Connection to Prime Gaps**: Under Cramér's conjecture, lower bound
  improves to n + √n - n^{o(1)}.

  **What we formalize**:
  1. Cycle and star graph definitions
  2. Ramsey number definition
  3. Parsons upper bound and BEFRS lower bound
  4. Exact values for special n
  5. The main Erdős question
  6. Connection to prime gaps and Cramér's conjecture
  7. Related questions about f(n) = R(C₄, Sₙ)

  **Key sorries**:
  - `parsons_upper_bound`: The main upper bound
  - `befrs_lower_bound`: The main lower bound
  - `exact_value_q2_plus_1`, `exact_value_q2`: Exact formulas

  **Open question**: Does the answer to Erdős's question depend on prime gaps?
-/
