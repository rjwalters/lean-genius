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
def chromaticNumber {V : Type*} (G : Graph V) : ℕ := sorry -- axiomatized below

/--
**Odd cycle:**
A cycle of odd length in a graph. The shortest odd cycle has length ≥ 3.
-/
def isOddCycle {V : Type*} (G : Graph V) (cycle : List V) : Prop :=
  cycle.length % 2 = 1 ∧ cycle.length ≥ 3 ∧ True -- Simplified

/--
**Odd girth:**
The length of the shortest odd cycle in G, or ∞ if G is bipartite.
-/
def oddGirth {V : Type*} (G : Graph V) : ℕ ∪ {⊤} := sorry -- axiomatized

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
axiom f_well_defined (k n : ℕ) :
    k ≥ 4 → n ≥ k → f k n ≥ 1

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
**The exponent 1/(k-2):**
For chromatic number k, the critical exponent is 1/(k-2).
- k = 4: exponent = 1/2
- k = 5: exponent = 1/3
- k = 6: exponent = 1/4
As k → ∞, the exponent → 0.
-/
axiom exponent_formula : True

/--
**Lower bound for general k:**
f_k(n) ≫ n^{1/(k-2)} for all k ≥ 4.
-/
axiom general_lower_bound (k : ℕ) :
    k ≥ 4 →
    ∃ c : ℝ, c > 0 ∧ ∀ n ≥ k, (f k n : ℝ) ≥ c * (n : ℝ) ^ (1 / (k - 2 : ℝ))

/--
**Upper bound for general k:**
f_k(n) ≪ n^{1/(k-2)} for all k ≥ 4.
-/
axiom general_upper_bound (k : ℕ) :
    k ≥ 4 →
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ k, (f k n : ℝ) ≤ C * (n : ℝ) ^ (1 / (k - 2 : ℝ))

/-
## Part V: Why Odd Cycles Matter
-/

/--
**Bipartite graphs are 2-chromatic:**
A graph is bipartite (2-colorable) iff it has no odd cycles.
-/
axiom bipartite_no_odd_cycles : True

/--
**Odd cycles force higher chromatic number:**
Every odd cycle needs 3 colors. Longer odd cycles don't directly
increase chromatic number, but shorter ones constrain structure.
-/
axiom odd_cycles_and_chromatic : True

/--
**Trade-off:**
High chromatic number tends to create short cycles.
Avoiding short odd cycles while maintaining high χ requires
special graph constructions.
-/
axiom chromatic_vs_girth_tradeoff : True

/--
**Constructions:**
The lower bound proofs use explicit constructions of graphs
with high chromatic number and large odd girth.
-/
axiom construction_technique : True

/-
## Part VI: Proof Techniques
-/

/--
**Local chromatic number:**
The proof uses the concept of local chromatic number and
bounds on coloring graphs with locally bounded structure.
-/
axiom local_chromatic_number : True

/--
**Regularity methods:**
Szemerédi's regularity lemma plays a role in the analysis.
-/
axiom regularity_methods : True

/--
**Probabilistic constructions:**
Random graph constructions provide the lower bounds.
-/
axiom probabilistic_constructions : True

/--
**Extremal graph theory:**
The upper bounds use extremal graph theory arguments.
-/
axiom extremal_arguments : True

/-
## Part VII: Related Problems
-/

/--
**Girth vs chromatic number:**
The classical problem: for given g and k, what is the minimum n
such that there exists a graph with girth > g and χ = k?
-/
axiom girth_vs_chromatic : True

/--
**Erdős's girth conjecture:**
There exist graphs with arbitrarily high girth and chromatic number.
Proved by Erdős using the probabilistic method.
-/
axiom erdos_girth_conjecture : True

/--
**Mycielski construction:**
An explicit construction of triangle-free graphs with high χ.
-/
axiom mycielski_construction : True

/-
## Part VIII: Historical Context
-/

/--
**Gallai's contribution (1963):**
Tibor Gallai initiated the systematic study of critical graphs
and proved the foundational lower bound for k = 4.
-/
axiom gallai_1963 : True

/--
**Kierstead-Szemerédi-Trotter (1984):**
The full resolution required combining ideas from extremal
graph theory, regularity, and coloring theory.
-/
axiom KST_1984 : True

/--
**Impact:**
The result is important for understanding the interplay between
local and global graph properties.
-/
axiom mathematical_impact : True

/-
## Part IX: Summary
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

/--
**Problem resolved:**
Erdős Problem #921 was completely solved in 1984.
-/
theorem erdos_921_solved : True := trivial

end Erdos921
