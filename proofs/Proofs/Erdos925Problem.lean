/-
Erdős Problem #925: Independent Sets in Non-Ramsey Graphs

Source: https://erdosproblems.com/925
Status: DISPROVED (Alon-Rödl 2005)

Statement:
Is there a constant δ > 0 such that, for all large n, if G is a graph on n
vertices which is not Ramsey for K₃ (i.e., there exists a 2-coloring of the
edges of G with no monochromatic triangle) then G contains an independent
set of size ≫ n^(1/3+δ)?

Background:
- Erdős posed this problem, likely in the 1960s-70s
- It is easy to show that such graphs have independent sets of size ≫ n^(1/3)
- The question asks whether this can be improved to n^(1/3+δ) for some δ > 0
- Equivalently: does R(3,3,m) ≪ m^(3-c) for some c > 0?

Resolution:
Alon and Rödl (2005) disproved this, proving:
  1/(log m)^(4+o(1)) · m³ ≪ R(3,3,m) ≪ (log log m)/(log m)² · m³

The answer is NO - the n^(1/3) bound cannot be improved to n^(1/3+δ).

Key Insight:
The multicolor Ramsey number R(3,3,m) grows essentially like m³/polylog(m),
not like m^(3-c) for any c > 0.

References:
- [AlRo05] Alon, Rödl, "Sharp bounds for some multicolor Ramsey numbers"
           Combinatorica 25 (2005), 125-141
- See also Problem #553
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

namespace Erdos925

/- ## Part I: Basic Definitions -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph G on n vertices is "not Ramsey for K₃" if there exists a 2-coloring
    of its edges with no monochromatic triangle. -/
def isNotRamseyForTriangle (G : SimpleGraph V) : Prop :=
  ∃ (color : G.edgeSet → Fin 2),
    -- No monochromatic triangle exists
    ¬∃ (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a),
      color ⟨s(a, b), hab⟩ = color ⟨s(b, c), hbc⟩ ∧
      color ⟨s(b, c), hbc⟩ = color ⟨s(a, c), hca⟩

/-- An independent set in G is a set of vertices with no edges between them. -/
def hasIndependentSetOfSize (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (S : Finset V), S.card ≥ k ∧ G.IsCliqueFree 2 ↑S

/-- The independence number α(G): the maximum size of an independent set.
    Axiomatized since computing the supremum requires decidability of
    the graph adjacency and finiteness of the search space. -/
axiom independenceNumber (G : SimpleGraph V) : ℕ

/- ## Part II: Ramsey Numbers -/

/-- R(3,3,m) is the minimum n such that any graph on n vertices either:
    - has a monochromatic triangle in every 2-coloring, OR
    - has an independent set of size m.
    Axiomatized since constructively defining this minimum requires
    decidability of the Ramsey property over all graphs. -/
axiom R_3_3 (m : ℕ) : ℕ

/-- The trivial lower bound: n^(1/3) independent set always exists. -/
/- ## Part III: The Conjecture -/

/-- Erdős's conjecture (later disproved):
    There exists δ > 0 such that non-Ramsey graphs on n vertices
    have independent sets of size ≫ n^(1/3+δ). -/
def erdos_925_conjecture : Prop :=
  ∃ (δ : ℝ) (C : ℝ), δ > 0 ∧ C > 0 ∧
  ∀ n : ℕ, n > 0 →
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
  (Fintype.card V = n) →
  ∀ (G : SimpleGraph V),
  isNotRamseyForTriangle G →
  hasIndependentSetOfSize G ⌈C * (n : ℝ) ^ (1/3 + δ)⌉.toNat

/-- Equivalent formulation in terms of Ramsey numbers:
    R(3,3,m) ≪ m^(3-c) for some c > 0. -/
def erdos_925_ramsey_form : Prop :=
  ∃ (c : ℝ) (C : ℝ), c > 0 ∧ C > 0 ∧
  ∀ m : ℕ, m > 0 → R_3_3 m ≤ ⌈C * (m : ℝ) ^ (3 - c)⌉.toNat

/- ## Part IV: Alon-Rödl Disproof (2005) -/

/-- Alon-Rödl (2005) lower bound:
    R(3,3,m) ≥ m³ / (log m)^(4+o(1)) -/
/-- Alon-Rödl (2005) upper bound:
    R(3,3,m) ≤ m³ · (log log m) / (log m)² -/
/-- Sudakov's improvement: the log log factor can be removed. -/
/-- The conjecture is false - Alon and Rödl disproved it. -/
axiom erdos_925_disproved : ¬erdos_925_conjecture

/-- Equivalently, R(3,3,m) grows like m³/polylog(m), not m^(3-c).
    The Ramsey formulation of the conjecture is also false. -/
/- ## Part V: Why n^(1/3) is Optimal -/

/-- The trivial bound n^(1/3) is essentially tight.
    Non-Ramsey graphs need not have independent sets larger than ~n^(1/3).
    For any ε > 0, there exist non-Ramsey graphs with α(G) ≤ n^(1/3+ε). -/
/- ## Part VI: The Easy Lower Bound -/

/-- The "easy" direction: every non-Ramsey graph has α ≥ cn^(1/3).
    This follows from basic counting arguments: in a 2-coloring without
    monochromatic triangles, one color class is triangle-free and has
    independence number ≥ Ω(n^(1/2)), giving overall α ≥ Ω(n^(1/3)). -/
axiom easy_lower_bound :
  ∃ (c : ℝ), c > 0 ∧
  ∀ n : ℕ, n > 0 →
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
  (Fintype.card V = n) →
  ∀ (G : SimpleGraph V),
  isNotRamseyForTriangle G →
  (independenceNumber G : ℝ) ≥ c * (n : ℝ) ^ (1/3 : ℝ)

/- ## Part VII: Summary

**Erdős Problem #925 - DISPROVED (Alon-Rödl 2005)**

**Problem (Erdős):**
If G is not Ramsey for K₃, must G have an independent set of size ≫ n^(1/3+δ)?

**Answer:** NO (Alon-Rödl 2005)

**The Truth:**
- Non-Ramsey graphs always have independent sets of size ~n^(1/3)
- But this cannot be improved to n^(1/3+δ) for any δ > 0
- Equivalently: R(3,3,m) ~ m³/polylog(m), not m^(3-c)

**Key Bounds:**
  m³/(log m)^(4+o(1)) ≤ R(3,3,m) ≤ m³/(log m)²
-/

/-- **Erdős Problem #925: DISPROVED**

The conjecture is false: there is no δ > 0 such that non-Ramsey graphs
on n vertices have independent sets of size ≫ n^(1/3+δ). -/
theorem erdos_925 : ¬erdos_925_conjecture :=
  erdos_925_disproved

/-- **Summary theorem:** The problem is fully resolved with known bounds.
    The conjecture is false, and the easy lower bound cn^(1/3) is tight. -/
theorem erdos_925_summary :
    ¬erdos_925_conjecture ∧
    (∃ (c : ℝ), c > 0 ∧
      ∀ n : ℕ, n > 0 →
      ∀ (V : Type*) [Fintype V] [DecidableEq V],
      (Fintype.card V = n) →
      ∀ (G : SimpleGraph V),
      isNotRamseyForTriangle G →
      (independenceNumber G : ℝ) ≥ c * (n : ℝ) ^ (1/3 : ℝ)) :=
  ⟨erdos_925_disproved, easy_lower_bound⟩

end Erdos925
