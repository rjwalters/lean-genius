/-
Erdős Problem #808: Graph-Restricted Sum-Product Bounds

Source: https://erdosproblems.com/808
Status: SOLVED (DISPROVED, with weaker positive result)

Statement (Erdős-Szemerédi conjecture, graph version):
Let c, ε > 0 and n be sufficiently large. If A ⊂ ℕ has |A| = n and G is
any graph on A with at least n^{1+c} edges, then
  max(|A +_G A|, |A ·_G A|) ≥ |A|^{1+c-ε}
where A +_G A = {a + b : (a,b) ∈ G} and A ·_G A = {a · b : (a,b) ∈ G}.

Counterexample (Alon-Ruzsa-Solymosi, 2020):
For arbitrarily large n, ∃ A with |A| = n and G with ≫ n^{5/3} edges
such that max(|A +_G A|, |A ·_G A|) ≪ n^{4/3+o(1)}.

Positive Result (ARS 2020):
max(|A +_G A|, |A ·_G A|) ≫ m^{3/2} · n^{-7/4}.

References:
- [ARS20] Alon, Ruzsa, Solymosi, Publ. Mat. (2020), 143-155
- [Er77c] Erdős, "Problems and results on combinatorial number theory III"
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

open Finset

namespace Erdos808

/- ## Part I: Basic Definitions -/

/-- **Graph-restricted sumset:** A +_G A = {a + b : (a,b) ∈ G}.
Only sums of adjacent vertices are counted. -/
def graphSumset (A : Finset ℕ) (G : Finset (ℕ × ℕ)) : Finset ℕ :=
  G.image (fun p => p.1 + p.2)

/-- **Graph-restricted product set:** A ·_G A = {a · b : (a,b) ∈ G}.
Only products of adjacent vertices are counted. -/
def graphProductset (A : Finset ℕ) (G : Finset (ℕ × ℕ)) : Finset ℕ :=
  G.image (fun p => p.1 * p.2)

/-- **Graph on a set A:** All edges connect vertices in A. -/
def isGraphOn (G : Finset (ℕ × ℕ)) (A : Finset ℕ) : Prop :=
  ∀ p ∈ G, p.1 ∈ A ∧ p.2 ∈ A

/- ## Part II: The Original Conjecture (DISPROVED) -/

/-- **The Erdős-Szemerédi graph conjecture:**
If G has ≥ n^{1+c} edges on a set of size n, then
max(|A +_G A|, |A ·_G A|) ≥ n^{1+c-ε}. This was DISPROVED. -/
def ErdosConjecture808 : Prop :=
  ∀ c ε : ℝ, c > 0 → ε > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∀ A : Finset ℕ, A.card = n →
        ∀ G : Finset (ℕ × ℕ), isGraphOn G A →
          (G.card : ℝ) ≥ n^(1 + c) →
          max (graphSumset A G).card (graphProductset A G).card ≥ n^(1 + c - ε)

/-- **The conjecture is FALSE.** -/
axiom erdos_808_false : ¬ErdosConjecture808

/- ## Part III: The Counterexample (ARS 2020) -/

/-- **Alon-Ruzsa-Solymosi counterexample (2020):**
For arbitrarily large n, ∃ A with |A| = n and G with ≫ n^{5/3-o(1)} edges
such that max(|A +_G A|, |A ·_G A|) ≪ n^{4/3+o(1)}. -/
axiom ars_counterexample :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
    ∃ A : Finset ℕ, A.card = n ∧
    ∃ G : Finset (ℕ × ℕ), isGraphOn G A ∧
      (∀ δ : ℝ, δ > 0 →
        (G.card : ℝ) ≥ (n : ℝ)^(5/3 - δ)) ∧
      (∃ C : ℝ, C > 0 ∧
        max (graphSumset A G).card (graphProductset A G).card ≤ C * (n : ℝ)^(4/3 + 1/100))

/-- **Gap in the counterexample:**
Conjecture predicts n^{5/3-ε} outputs from n^{5/3} edges,
but only n^{4/3+o(1)} are achieved. Gap: 5/3 - 4/3 = 1/3. -/
theorem counterexample_gap : (5 : ℚ)/3 - 4/3 = 1/3 := by norm_num

/- ## Part IV: The Positive Result (ARS 2020) -/

/-- **Alon-Ruzsa-Solymosi positive bound (2020):**
If A has size n and G has m edges, then
max(|A +_G A|, |A ·_G A|) ≫ m^{3/2} · n^{-7/4}. -/
axiom ars_positive_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n > 0 →
      ∀ A : Finset ℕ, A.card = n →
        ∀ G : Finset (ℕ × ℕ), isGraphOn G A →
          (max (graphSumset A G).card (graphProductset A G).card : ℝ) ≥
            c * (G.card : ℝ)^(3/2) * (n : ℝ)^(-7/4)

/- ## Part V: Connection to Sum-Product Conjecture -/

/-- **The classical sum-product conjecture (Problem 52):**
For any finite A ⊂ ℤ and ε > 0, max(|A+A|, |A·A|) ≥ |A|^{2-ε}.
This is the complete graph case (G = A × A).
The failure of Problem 808 shows graph structure matters crucially:
sparse graphs can exploit arithmetic structure to limit expansion. -/
def SumProductConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∀ A : Finset ℕ, A.card = n →
        max ((A.image (fun p => p.1 + p.2)).card)
            ((A.image (fun p => p.1 * p.2)).card) ≥ n^(2 - ε)

/- ## Part VI: Summary -/

/-- **Erdős Problem #808: DISPROVED (with positive result)**

- CONJECTURE: FALSE (Alon-Ruzsa-Solymosi 2020)
- COUNTEREXAMPLE: n^{5/3} edges can give only n^{4/3} outputs
- POSITIVE RESULT: max(|A +_G A|, |A ·_G A|) ≥ c · m^{3/2} · n^{-7/4} -/
theorem erdos_808 :
    ¬ErdosConjecture808 ∧
    (∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n > 0 →
        ∀ A : Finset ℕ, A.card = n →
          ∀ G : Finset (ℕ × ℕ), isGraphOn G A →
            (max (graphSumset A G).card (graphProductset A G).card : ℝ) ≥
              c * (G.card : ℝ)^(3/2) * (n : ℝ)^(-7/4)) :=
  ⟨erdos_808_false, ars_positive_bound⟩

end Erdos808
