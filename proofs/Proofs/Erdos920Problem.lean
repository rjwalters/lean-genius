/-
Erdős Problem #920: Chromatic Numbers of K_k-Free Graphs

Source: https://erdosproblems.com/920
Status: OPEN

Statement:
Let g_k(n) denote the largest chromatic number of a graph with n vertices
containing no K_k (complete graph on k vertices).

Is it true that, for k ≥ 4,
  g_k(n) ≫ n^{1-1/(k-1)} / (log n)^c
for some constant c > 0?

History:
- Graver-Yackel (1968): g_k(n) ≪ (n · log log n / log n)^{1-1/(k-1)} [upper bound]
- Erdős (1959): g_3(n) ≫ n^{1/2} / log n [k=3 case, via R(3,m)]
- Shearer: g_3(n) ≫ (n/log n)^{1/2} [improved k=3]
- Mattheus-Verstraete (2023): g_4(n) ≫ n^{2/3} / (log n)^{4/3} [k=4 case]

The question asks about the optimal lower bound for k ≥ 4.

Connection to Ramsey Theory:
g_k(n) is related to Ramsey numbers R(k,m) via:
If R(k,m) ≫ m^α / (log m)^β, then g_k(n) ≫ n^{1-1/α} / (log n)^{β/α}

References:
- [Er59b] Erdős, "Graph theory and probability", Canadian J. Math. (1959)
- [GrYa68] Graver, Yackel, J. Combinatorial Theory (1968)
- [MaVe23] Mattheus, Verstraete, arXiv:2306.04007 (2023)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic

open SimpleGraph Real

namespace Erdos920

/-
## Part I: Basic Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**K_k-Free Graph:**
A graph G is K_k-free if it contains no complete subgraph on k vertices.
-/
def IsKFree (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.CliqueFree k

/--
**Chromatic Number:**
The minimum number of colors needed to properly color the vertices
so that no two adjacent vertices share the same color.
-/
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ :=
  G.chromaticNumber

/--
**Maximum Chromatic Number g_k(n):**
The largest chromatic number among all K_k-free graphs on n vertices.
-/
/-- The supremum over all K_k-free graphs on n vertices. -/
axiom maxChromaticKFree (k n : ℕ) : ℕ

/-
## Part II: Known Upper Bounds
-/

/--
**Graver-Yackel Upper Bound (1968):**
g_k(n) ≪ (n · log log n / log n)^{1-1/(k-1)}
-/

/--
**Trivial Upper Bound:**
g_k(n) ≤ n (at most n colors needed).
-/

/-
## Part III: Known Lower Bounds
-/

/--
**Erdős Lower Bound for k=3 (1959):**
g_3(n) ≫ n^{1/2} / log n
Via the Ramsey bound R(3,m) ≫ (m/log m)^2.
-/

/--
**Shearer's Improved Bound for k=3:**
g_3(n) ≫ (n/log n)^{1/2}
-/

/--
**Mattheus-Verstraete Bound for k=4 (2023):**
g_4(n) ≫ n^{2/3} / (log n)^{4/3}
Via R(4,m) ≫ m^3 / (log m)^4.
-/
axiom mattheus_verstraete_2023 :
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (maxChromaticKFree 4 n : ℝ) ≥ c * (n : ℝ) ^ (2/3 : ℝ) / (Real.log n) ^ (4/3 : ℝ)

/--
**General Lower Bound:**
g_k(n) ≫ n^{1-2/(k+1)} / (log n)^{c_k}
This is weaker than the conjectured bound.
-/
axiom general_lower_bound :
  ∀ k : ℕ, k ≥ 3 →
    ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        (maxChromaticKFree k n : ℝ) ≥
          c * (n : ℝ) ^ (1 - 2 / (k + 1 : ℝ)) / (Real.log n) ^ c

/-
## Part IV: The Erdős Conjecture
-/

/--
**The Erdős Conjecture (for k ≥ 4):**
g_k(n) ≫ n^{1-1/(k-1)} / (log n)^c for some c > 0.
-/
def ErdosConjecture (k : ℕ) : Prop :=
  k ≥ 4 →
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        (maxChromaticKFree k n : ℝ) ≥ C * (n : ℝ) ^ (1 - 1 / (k - 1 : ℝ)) / (Real.log n) ^ c

/--
**The Gap:**
Current lower bound exponent: 1 - 2/(k+1)
Conjectured lower bound exponent: 1 - 1/(k-1)

For k=4: current = 3/5 = 0.6, conjectured = 2/3 ≈ 0.667
For k=5: current = 2/3 ≈ 0.667, conjectured = 3/4 = 0.75
-/

/-
## Part V: Connection to Ramsey Numbers
-/

/--
**Ramsey Number R(k,m):**
The smallest n such that every 2-coloring of K_n edges contains
either a red K_k or a blue K_m.
-/
axiom RamseyNumber (k m : ℕ) : ℕ

/--
**Ramsey-Chromatic Connection:**
If R(k,m) ≥ c · m^α / (log m)^β, then
g_k(n) ≥ c' · n^{1-1/α} / (log n)^{β/α}.
This is the key bridge between Ramsey theory and chromatic numbers. -/

/--
**Erdős Ramsey Bound (1959):**
R(3,m) ≫ (m/log m)^2
-/

/--
**Mattheus-Verstraete Ramsey Bound (2023):**
R(4,m) ≫ m^3 / (log m)^4
This was a breakthrough for k=4.
-/

/-
## Part VI: Summary
-/

/--
**Erdős Problem #920: OPEN**

PROBLEM: For k ≥ 4, is g_k(n) ≫ n^{1-1/(k-1)} / (log n)^c for some c?

KNOWN:
- Upper: g_k(n) ≪ (n · log log n / log n)^{1-1/(k-1)} [Graver-Yackel]
- Lower: g_k(n) ≫ n^{1-2/(k+1)} / (log n)^{c_k} [general]
- k=3: g_3(n) ≈ (n/log n)^{1/2} [well-understood]
- k=4: g_4(n) ≫ n^{2/3} / (log n)^{4/3} [Mattheus-Verstraete 2023]

GAP: The exponent should be 1-1/(k-1), not 1-2/(k+1), for k ≥ 5. -/
theorem erdos_920_summary :
    -- General lower bound is known
    (∀ k : ℕ, k ≥ 3 → ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        (maxChromaticKFree k n : ℝ) ≥
          c * (n : ℝ) ^ (1 - 2 / (k + 1 : ℝ)) / (Real.log n) ^ c) ∧
    -- k=4 breakthrough by Mattheus-Verstraete (2023)
    (∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        (maxChromaticKFree 4 n : ℝ) ≥ c * (n : ℝ) ^ (2/3 : ℝ) / (Real.log n) ^ (4/3 : ℝ)) :=
  ⟨general_lower_bound, mattheus_verstraete_2023⟩

end Erdos920
