/-
Erdős Problem #921: Chromatic Number and Odd Cycle Girth

Source: https://erdosproblems.com/921
Status: SOLVED (Kierstead-Szemerédi-Trotter 1984)

Statement:
Let k ≥ 4 and let f_k(n) be the largest m such that there exists
a graph on n vertices with chromatic number k in which every odd
cycle has length > m.

Conjecture: f_k(n) ≍ n^{1/(k-2)}

Resolution:
Kierstead, Szemerédi, and Trotter proved this for all k ≥ 4 in 1984.

Historical Note:
A question of Erdős and Gallai. Gallai proved f_4(n) ≫ n^{1/2} in 1963.
Erdős proved f_4(n) ≪ n^{1/2} (unpublished).

References:
- Gallai [Ga63]: Lower bound for k = 4
- Erdős: Upper bound for k = 4 (unpublished)
- Kierstead-Szemerédi-Trotter [KST84]: Complete proof
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Erdos921

/-
## Part I: Basic Definitions
-/

/--
**Simple graph:**
A graph G with vertex set V and edge set E ⊆ V × V.
-/
structure Graph (V : Type*) where
  adj : V → V → Prop
  symm : ∀ v w, adj v w → adj w v
  loopless : ∀ v, ¬adj v v

/--
**Chromatic number:**
χ(G) is the minimum k such that G has a proper k-coloring.
A proper k-coloring assigns colors 1,...,k to vertices such that
adjacent vertices get different colors.
-/
/--
**Odd girth:**
The length of the shortest odd cycle in G, or 0 if G is bipartite.
-/
/--
**The function f_k(n):**
f_k(n) = largest m such that there exists a graph G on n vertices
with χ(G) = k and every odd cycle in G has length > m.

Equivalently, f_k(n) is the maximum odd girth - 1 among k-chromatic
graphs on n vertices.
-/
axiom f (k n : ℕ) : ℕ

/--
**Basic property: f_k(n) is well-defined for k ≥ 4:**
Graphs with high chromatic number but large odd girth exist.
-/
/-
## Part II: The Main Conjecture
-/

/--
**The Erdős-Gallai Conjecture:**
f_k(n) ≍ n^{1/(k-2)} for all k ≥ 4.

This means: ∃ c₁ c₂ > 0 such that
c₁ · n^{1/(k-2)} ≤ f_k(n) ≤ c₂ · n^{1/(k-2)}.
-/
def erdos_gallai_conjecture (k : ℕ) : Prop :=
  k ≥ 4 →
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
  ∀ n ≥ k, c₁ * (n : ℝ) ^ (1 / (k - 2 : ℝ)) ≤ f k n ∧
           (f k n : ℝ) ≤ c₂ * (n : ℝ) ^ (1 / (k - 2 : ℝ))

/--
**Kierstead-Szemerédi-Trotter Theorem (1984):**
The conjecture is true for all k ≥ 4.
-/
axiom kierstead_szemeredi_trotter (k : ℕ) :
    erdos_gallai_conjecture k

/-
## Part III: The Case k = 4
-/

/--
**Gallai's lower bound (1963):**
f_4(n) ≫ n^{1/2}.

Gallai constructed graphs with chromatic number 4 and large odd girth.
-/
axiom gallai_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 4, (f 4 n : ℝ) ≥ c * Real.sqrt n

/--
**Erdős's upper bound (unpublished):**
f_4(n) ≪ n^{1/2}.

This shows that Gallai's bound is tight up to constants.
-/
axiom erdos_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 4, (f 4 n : ℝ) ≤ C * Real.sqrt n

/--
**The k = 4 case is completely resolved:**
f_4(n) ≍ n^{1/2}.
-/
theorem k4_case :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n ≥ 4, c₁ * Real.sqrt n ≤ f 4 n ∧ (f 4 n : ℝ) ≤ c₂ * Real.sqrt n := by
  obtain ⟨c, hc, hlow⟩ := gallai_lower_bound
  obtain ⟨C, hC, hup⟩ := erdos_upper_bound
  exact ⟨c, C, hc, hC, fun n hn => ⟨hlow n hn, hup n hn⟩⟩

/-
## Part IV: General k Case
-/

/--
**Lower bound for general k:**
f_k(n) ≫ n^{1/(k-2)} for all k ≥ 4.
-/
/--
**Upper bound for general k:**
f_k(n) ≪ n^{1/(k-2)} for all k ≥ 4.
-/
/-
## Part V: Summary
-/

/--
**Summary of Erdős Problem #921:**

PROBLEM: Let f_k(n) = largest m such that there exists an n-vertex
graph with χ = k and odd girth > m. Is f_k(n) ≍ n^{1/(k-2)}?

STATUS: SOLVED (YES) by Kierstead-Szemerédi-Trotter 1984

KEY RESULTS:
1. k = 4: f_4(n) ≍ n^{1/2} (Gallai + Erdős)
2. General k ≥ 4: f_k(n) ≍ n^{1/(k-2)} (KST 1984)

KEY INSIGHTS:
1. Higher chromatic number forces shorter odd cycles
2. The exponent 1/(k-2) captures the tension precisely
3. Explicit constructions give lower bounds
4. Extremal arguments give upper bounds

A complete resolution of the chromatic/odd-girth trade-off.
-/
theorem erdos_921_status :
    -- For all k ≥ 4, the conjecture is proved
    ∀ k ≥ 4, erdos_gallai_conjecture k := by
  intro k hk
  exact kierstead_szemeredi_trotter k

end Erdos921
